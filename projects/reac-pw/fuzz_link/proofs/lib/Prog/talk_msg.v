(* talk, PLAIN build: the message loop fragment F_msg (lib/Prog/talk_defs.v), 0x1580c .. 0x15840,
   with its arms 0x15888 / 0x15a70 .. 0x15aa4 (NLMSG_ERROR) and 0x15898 / 0x15a68 (RTM_NEWLINK).
   Induction on the fuel of msg_scan; each turn reads ml (lwu), the type (lhu) and, for an
   NLMSG_ERROR of ml >= 36, the int32 code at off+16 (lbu, lbu, lbu, lb joined by slli / or). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem talk_defs talk_kit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge.
(* the faster stepping, as lib/Prog/memcpy.v lines 19-40 *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.Step.zstep ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.StepFast.sf_zstep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.Destzna.dk_ands PO.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require WeqGuard.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.WeqGuard.word_eq_guarded.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.Stor0fe.sb_mem_after_store.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Dieta54.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require AndN.
Local Ltac lia ::= OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.Dieta54.dlia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* --------------------------------------------------------------------------
   1. reads of the chunk
   -------------------------------------------------------------------------- *)

Lemma fm_rd32_read : forall m B ck off, bytes_at rsegs m B ck -> 0 <= off -> off + 4 <= Z.of_nat (length ck) ->
  ov_read_bytes rsegs m (Z_to_bv 64 (B + off)) 4 = Some (le4 (Z_to_bv 64 (rd32 ck off))).
Proof.
  intros m B ck off HB H1 H2. rewrite (tk_read m B ck off 4 HB H1) by (cbn; lia). f_equal.
  change (Z.of_nat 4) with 4. unfold rd32, link_spec.rdn. apply tk_le4.
  rewrite tk_slice_length by lia. reflexivity.
Qed.

Lemma fm_rd16_read : forall m B ck off, bytes_at rsegs m B ck -> 0 <= off -> off + 2 <= Z.of_nat (length ck) ->
  ov_read_bytes rsegs m (Z_to_bv 64 (B + off)) 2 = Some (le2 (Z_to_bv 64 (rd16 ck off))).
Proof.
  intros m B ck off HB H1 H2. rewrite (tk_read m B ck off 2 HB H1) by (cbn; lia). f_equal.
  change (Z.of_nat 2) with 2. unfold rd16, link_spec.rdn. apply tk_le2.
  rewrite tk_slice_length by lia. reflexivity.
Qed.

Lemma fm_rd_range : forall ck off n, 0 <= off -> 0 <= n -> off + n <= Z.of_nat (length ck) ->
  0 <= link_spec.rdn ck off n < 2 ^ (8 * n).
Proof. intros ck off n H1 H2 H3. split; [apply tk_rdn_range | apply tk_rdn_bound; lia]. Qed.

Lemma fm_rd32s_range : forall ck off, 0 <= off -> off + 4 <= Z.of_nat (length ck) ->
  - 2 ^ 31 <= rd32s ck off < 2 ^ 31.
Proof.
  intros ck off H1 H2. pose proof (fm_rd_range ck off 4 H1 ltac:(lia) H2) as R.
  change (link_spec.rdn ck off 4) with (rd32 ck off) in R. change (2 ^ (8 * 4)) with (2 ^ 32) in R.
  unfold rd32s. cbv zeta. destruct (Z.ltb_spec (rd32 ck off) (2 ^ 31)); cbv iota; lia.
Qed.

(* the four bytes of a slice of length 4 *)
Lemma fm_slice4 : forall (c : list byte) off b0 b1 b2 b3, 0 <= off -> off + 4 <= Z.of_nat (length c) ->
  nth_error c (Z.to_nat off) = Some b0 -> nth_error c (Z.to_nat (off + 1)) = Some b1 ->
  nth_error c (Z.to_nat (off + 2)) = Some b2 -> nth_error c (Z.to_nat (off + 3)) = Some b3 ->
  slice c off 4 = [b0; b1; b2; b3].
Proof.
  intros c off b0 b1 b2 b3 H1 H2 E0 E1 E2 E3.
  assert (L : length (slice c off 4) = 4%nat) by (rewrite tk_slice_length by lia; reflexivity).
  assert (N : forall k, 0 <= k < 4 -> nth_error (slice c off 4) (Z.to_nat k) = nth_error c (Z.to_nat (off + k)))
    by (intros k Hk; apply tk_nth_slice; lia).
  pose proof (N 0 ltac:(lia)) as N0. pose proof (N 1 ltac:(lia)) as N1.
  pose proof (N 2 ltac:(lia)) as N2. pose proof (N 3 ltac:(lia)) as N3. clear N.
  rewrite Z.add_0_r, E0 in N0. rewrite E1 in N1. rewrite E2 in N2. rewrite E3 in N3.
  revert L N0 N1 N2 N3.
  destruct (slice c off 4) as [|x0 [|x1 [|x2 [|x3 [|x4 r]]]]]; intros L N0 N1 N2 N3; cbn in L; try discriminate.
  change (Z.to_nat 0) with 0%nat in N0. change (Z.to_nat 1) with 1%nat in N1.
  change (Z.to_nat 2) with 2%nat in N2. change (Z.to_nat 3) with 3%nat in N3.
  cbn [nth_error] in N0, N1, N2, N3. congruence.
Qed.

(* --------------------------------------------------------------------------
   2. words: the int32 joined from four bytes, the alignment of ml
   -------------------------------------------------------------------------- *)

Lemma fm_signed8 : forall b : byte,
  bv_signed b = if bv_unsigned b <? 128 then bv_unsigned b else bv_unsigned b - 256.
Proof.
  intros b. pose proof (tk_byte_range b) as R.
  unfold bv_signed, bv_swrap, bv_wrap.
  replace (bv_half_modulus 8) with 128 by reflexivity. replace (bv_modulus 8) with 256 by reflexivity.
  destruct (Z.ltb_spec (bv_unsigned b) 128) as [H|H]; cbv iota.
  - rewrite Z.mod_small by lia. lia.
  - rewrite <- (Z.mod_add (bv_unsigned b + 128) (-1) 256) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma fm_lor_add : forall a b k, 0 <= k -> 0 <= a -> 0 <= b < 2 ^ k -> a mod 2 ^ k = 0 -> Z.lor a b = a + b.
Proof.
  intros a b k Hk Ha Hb Hm.
  assert (L : Z.land a b = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i k) as [Lt|Ge].
    - rewrite <- (Z.mod_pow2_bits_low a k i Lt). rewrite Hm, Z.bits_0. reflexivity.
    - rewrite (testbit_high_false b k i Hb ltac:(lia)). apply andb_false_r. }
  rewrite <- Z.lxor_lor by exact L. symmetry. apply Z.add_nocarry_lxor. exact L.
Qed.

Lemma fm_slli_lit : forall x k, 0 <= k -> v_slli (Z_to_bv 64 x) k = Z_to_bv 64 ((x * 2 ^ k) mod 2 ^ 64).
Proof.
  intros x k Hk. unfold v_slli. rewrite Z_to_bv_mod64. apply Z_to_bv_eqm.
  rewrite Z.shiftl_mul_pow2 by exact Hk. rewrite unsigned_lit_wrap. rewrite Zmult_mod_idemp_l. reflexivity.
Qed.

Lemma fm_or_lit : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  v_or (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (Z.lor x y).
Proof. intros x y Hx Hy. unfold v_or. rewrite (unsigned_lit x Hx), (unsigned_lit y Hy). reflexivity. Qed.

Ltac fm_side := first [ lia | (apply Z.mod_mul; lia) | (Z.div_mod_to_equations; lia) ].

Lemma fm_join : forall b16 b17 b18 b19 : byte,
  v_or (v_or (v_slli (sxb b19) 24) (v_slli (zxb b18) 16)) (v_or (v_slli (zxb b17) 8) (zxb b16)) =
  Z_to_bv 64 (let v := bytes_le_to_Z [b16; b17; b18; b19] in if v <? 2 ^ 31 then v else v - 2 ^ 32).
Proof.
  intros b16 b17 b18 b19.
  pose proof (tk_byte_range b16) as R16. pose proof (tk_byte_range b17) as R17.
  pose proof (tk_byte_range b18) as R18. pose proof (tk_byte_range b19) as R19.
  pose proof (fm_signed8 b19) as S19.
  rewrite bytes_le_to_Z_le_val. cbn [map le_val]. cbv zeta.
  unfold zxb, sxb.
  rewrite !fm_slli_lit by lia.
  rewrite (Z.mod_small (bv_unsigned b18 * 2 ^ 16)) by lia.
  rewrite (Z.mod_small (bv_unsigned b17 * 2 ^ 8)) by lia.
  rewrite (fm_or_lit (bv_unsigned b17 * 2 ^ 8) (bv_unsigned b16)) by lia.
  rewrite (fm_lor_add (bv_unsigned b17 * 2 ^ 8) (bv_unsigned b16) 8) by fm_side.
  destruct (Z.ltb_spec (bv_unsigned b19) 128) as [Lo|Hi].
  - assert (Es : bv_signed b19 = bv_unsigned b19) by (rewrite S19; destruct (Z.ltb_spec (bv_unsigned b19) 128); [reflexivity | lia]).
    rewrite Es. rewrite (Z.mod_small (bv_unsigned b19 * 2 ^ 24)) by lia.
    rewrite (fm_or_lit (bv_unsigned b19 * 2 ^ 24) (bv_unsigned b18 * 2 ^ 16)) by lia.
    rewrite (fm_lor_add (bv_unsigned b19 * 2 ^ 24) (bv_unsigned b18 * 2 ^ 16) 24) by fm_side.
    rewrite (fm_or_lit (bv_unsigned b19 * 2 ^ 24 + bv_unsigned b18 * 2 ^ 16) (bv_unsigned b17 * 2 ^ 8 + bv_unsigned b16)) by lia.
    rewrite (fm_lor_add (bv_unsigned b19 * 2 ^ 24 + bv_unsigned b18 * 2 ^ 16) (bv_unsigned b17 * 2 ^ 8 + bv_unsigned b16) 16) by fm_side.
    rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbv iota. f_equal. lia.
  - assert (Es : bv_signed b19 = bv_unsigned b19 - 256) by (rewrite S19; destruct (Z.ltb_spec (bv_unsigned b19) 128); [lia | reflexivity]).
    assert (EP : (bv_signed b19 * 2 ^ 24) mod 2 ^ 64 = bv_unsigned b19 * 2 ^ 24 + (2 ^ 64 - 2 ^ 32)).
    { rewrite Es. rewrite <- (Z.mod_add ((bv_unsigned b19 - 256) * 2 ^ 24) 1 (2 ^ 64)) by lia.
      rewrite Z.mod_small by lia. lia. }
    rewrite EP.
    rewrite (fm_or_lit (bv_unsigned b19 * 2 ^ 24 + (2 ^ 64 - 2 ^ 32)) (bv_unsigned b18 * 2 ^ 16)) by lia.
    rewrite (fm_lor_add (bv_unsigned b19 * 2 ^ 24 + (2 ^ 64 - 2 ^ 32)) (bv_unsigned b18 * 2 ^ 16) 24) by fm_side.
    rewrite (fm_or_lit (bv_unsigned b19 * 2 ^ 24 + (2 ^ 64 - 2 ^ 32) + bv_unsigned b18 * 2 ^ 16)
                       (bv_unsigned b17 * 2 ^ 8 + bv_unsigned b16)) by lia.
    rewrite (fm_lor_add (bv_unsigned b19 * 2 ^ 24 + (2 ^ 64 - 2 ^ 32) + bv_unsigned b18 * 2 ^ 16)
                        (bv_unsigned b17 * 2 ^ 8 + bv_unsigned b16) 16) by fm_side.
    rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbv iota. apply Z_to_bv_eqm. Z.div_mod_to_equations. lia.
Qed.

Lemma fm_join_ck : forall ck off b16 b17 b18 b19, 0 <= off -> off + 20 <= Z.of_nat (length ck) ->
  nth_error ck (Z.to_nat (off + 16)) = Some b16 -> nth_error ck (Z.to_nat (off + 17)) = Some b17 ->
  nth_error ck (Z.to_nat (off + 18)) = Some b18 -> nth_error ck (Z.to_nat (off + 19)) = Some b19 ->
  v_or (v_or (v_slli (sxb b19) 24) (v_slli (zxb b18) 16)) (v_or (v_slli (zxb b17) 8) (zxb b16)) =
  Z_to_bv 64 (rd32s ck (off + 16)).
Proof.
  intros ck off b16 b17 b18 b19 H1 H2 E16 E17 E18 E19.
  assert (S4 : slice ck (off + 16) 4 = [b16; b17; b18; b19]).
  { apply fm_slice4; try lia.
    - exact E16.
    - replace (off + 16 + 1) with (off + 17) by lia. exact E17.
    - replace (off + 16 + 2) with (off + 18) by lia. exact E18.
    - replace (off + 16 + 3) with (off + 19) by lia. exact E19. }
  rewrite fm_join. unfold rd32s, rd32, link_spec.rdn. rewrite S4. reflexivity.
Qed.

(* srliw t1, s7, 2 on s7 = ml + 3 *)
Lemma fm_srliw : forall e, 0 <= e < 2 ^ 31 -> bv_swrap 32 (Z.shiftr (bv_wrap 32 e) 2) = e / 4.
Proof.
  intros e He. unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity. replace (bv_modulus 32) with (2 ^ 32) by reflexivity.
  rewrite (Z.mod_small e (2 ^ 32)) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 2) with 4.
  rewrite Z.mod_small by (Z.div_mod_to_equations; lia). lia.
Qed.

(* slli t1, t1, 2 *)
Lemma fm_align_eq : forall ml, Z.shiftl ((ml + 3) / 4) 2 = nl_align ml.
Proof. intros ml. unfold nl_align. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. lia. Qed.

Lemma fm_align_range : forall ml, 16 <= ml <= 4096 -> 16 <= nl_align ml <= ml + 3.
Proof. intros ml H. unfold nl_align. Z.div_mod_to_equations. lia. Qed.

(* --------------------------------------------------------------------------
   3. the spec functions, one turn at a time
   -------------------------------------------------------------------------- *)

Lemma fm_scan_step : forall f c off left, msg_scan (S f) c off left =
  if left <? 16 then NlNone else
  if (rd32 c off <? 16) || (left <? rd32 c off) then NlNone else
  if rd16 c (off + 4) =? 2
  then (if rd32 c off <? 36 then NlShort else NlErr (rd32s c (off + 16)))
  else if rd16 c (off + 4) =? 16
       then NlLink (attr_scan f c (off + NL_HDR + IFI_LEN) (rd32 c off - NL_HDR - IFI_LEN) no_attrs)
       else msg_scan f c (off + nl_align (rd32 c off)) (left - nl_align (rd32 c off)).
Proof. intros. reflexivity. Qed.

Lemma fm_scan_short : forall f c off left, left < 16 -> msg_scan f c off left = NlNone.
Proof.
  intros [|f] c off left H; [reflexivity|]. rewrite fm_scan_step.
  rewrite (proj2 (Z.ltb_lt left 16) H). reflexivity.
Qed.

Lemma fm_attr_short : forall f c off left a, left < 4 -> attr_scan f c off left a = a.
Proof.
  intros [|f] c off left a H; [reflexivity|]. cbn [attr_scan]. unfold RTA_HDR.
  rewrite (proj2 (Z.ltb_lt left 4) H). reflexivity.
Qed.

(* --------------------------------------------------------------------------
   4. the walk
   -------------------------------------------------------------------------- *)

(* the state the walk reached equals the one a continuation names: registers word by word *)
Ltac fm_leaf := first [ reflexivity | (f_equal; lia) | (apply Z_to_bv_eqm; Z.div_mod_to_equations; lia) ].
Ltac fm_eq :=
  lazymatch goal with |- MS _ _ _ _ _ _ _ = MS _ _ _ _ _ _ _ => idtac end;
  unfold mkR;
  repeat (first [ reflexivity
                | lazymatch goal with
                  | |- Z_to_bv 64 _ = Z_to_bv 64 _ => fail
                  | |- _ => progress f_equal
                  end ]);
  fm_leaf.

Lemma F_msg_ok : F_msg_spec.
Proof.
  unfold F_msg_spec.
  intros Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m B ck fu.
  revert t0 t1 t2 a7 s7.
  induction fu as [|f IH]; intros t0 t1 t2 a7 s7 off left -> -> -> -> -> HB LC B0 B1 O0 OL L16 LF KN KR KL.
  { cbn in LF. lia. }
  pose proof (fm_rd32_read m B ck off HB O0 ltac:(lia)) as RD1.
  pose proof (fm_rd_range ck off 4 O0 ltac:(lia) ltac:(lia)) as R1.
  change (link_spec.rdn ck off 4) with (rd32 ck off) in R1. change (2 ^ (8 * 4)) with (2 ^ 32) in R1.
  remember (rd32 ck off) as ml eqn:Eml.
  step. step.                                   (* add t1, s6, a7; lwu s7, 0(t1) *)
  rewrite (tk_zx32_small ml) by lia. clear RD1.
  step.                                         (* bltu s7, a4 *)
  rewrite (tk_ltu ml 16) by lia.
  if_cases K1; zify_bool K1.
  { eapply evt_eq; [ | eapply KN ]; [ fm_eq | ].
    rewrite fm_scan_step, <- Eml. decide_tests. reflexivity. }
  step.                                         (* bltu t0, s7 *)
  rewrite (tk_ltu left ml) by lia.
  if_cases K2; zify_bool K2.
  { eapply evt_eq; [ | eapply KN ]; [ fm_eq | ].
    rewrite fm_scan_step, <- Eml. decide_tests. reflexivity. }
  pose proof (fm_rd16_read m B ck (off + 4) HB ltac:(lia) ltac:(lia)) as RD2.
  pose proof (fm_rd_range ck (off + 4) 2 ltac:(lia) ltac:(lia) ltac:(lia)) as R2.
  change (link_spec.rdn ck (off + 4) 2) with (rd16 ck (off + 4)) in R2. change (2 ^ (8 * 2)) with (2 ^ 16) in R2.
  remember (rd16 ck (off + 4)) as ty eqn:Ety.
  step.                                         (* lhu t2, 4(t1) *)
  rewrite (tk_zx16_small ty) by lia. clear RD2.
  step.                                         (* beq t2, a4: RTM_NEWLINK *)
  rewrite (tk_eqb ty 16) by lia.
  if_cases K3; zify_bool K3.
  { step. step.                                 (* addi a0, zero, 0x24; bltu s7, a0 *)
    rewrite (tk_ltu ml 36) by lia.
    if_cases K4; zify_bool K4.
    - step. step.                               (* 0x15a68: mv a0, zero; j 0x1584c *)
      eapply evt_eq; [ | eapply (KR 0) ]; [ fm_eq | ].
      unfold msg_ret. right; right. split; [|reflexivity].
      rewrite fm_scan_step, <- Eml, <- Ety. decide_tests.
      rewrite fm_attr_short by (unfold NL_HDR, IFI_LEN; lia). reflexivity.
    - eapply evt_eq; [ | eapply (KL f off ml) ]; [ fm_eq | | | | | ].
      + rewrite fm_scan_step, <- Eml, <- Ety. decide_tests. reflexivity.
      + lia.
      + lia.
      + lia.
      + lia. }
  step.                                         (* beq t2, a6: NLMSG_ERROR *)
  rewrite (tk_eqb ty 2) by lia.
  if_cases K5; zify_bool K5.
  { step. step.                                 (* addi a0, zero, 0x24; bgeu s7, a0 *)
    rewrite (tk_ltu ml 36) by lia.
    if_cases K6; zify_bool K6.
    - (* 0x15a70: the code, the int32 at off+16 *)
      destruct (tk_nth_some ck (Z.to_nat (off + 16)) ltac:(lia)) as [b16 E16].
      destruct (tk_nth_some ck (Z.to_nat (off + 17)) ltac:(lia)) as [b17 E17].
      destruct (tk_nth_some ck (Z.to_nat (off + 18)) ltac:(lia)) as [b18 E18].
      destruct (tk_nth_some ck (Z.to_nat (off + 19)) ltac:(lia)) as [b19 E19].
      pose proof (tk_read1 m B ck (off + 17) b17 HB ltac:(lia) E17) as RB. step. clear RB.
      pose proof (tk_read1 m B ck (off + 16) b16 HB ltac:(lia) E16) as RB. step. clear RB.
      pose proof (tk_read1 m B ck (off + 18) b18 HB ltac:(lia) E18) as RB. step. clear RB.
      pose proof (tk_read1 m B ck (off + 19) b19 HB ltac:(lia) E19) as RB. step. clear RB.
      do 6 step.                                (* slli; or; slli; slli; or; or *)
      pose proof (fm_join_ck ck off b16 b17 b18 b19 O0 ltac:(lia) E16 E17 E18 E19) as EJ.
      match goal with
      | |- context [Z_to_bv 64 (Z.lor ?X ?Y)] =>
          replace (Z_to_bv 64 (Z.lor X Y)) with (Z_to_bv 64 (rd32s ck (off + 16))) by (first [exact EJ | exact (eq_sym EJ)])
      end.
      clear EJ.
      pose proof (fm_rd32s_range ck (off + 16) ltac:(lia) ltac:(lia)) as R3.
      remember (rd32s ck (off + 16)) as r eqn:Er.
      step.                                     (* blez a0 *)
      rewrite (tk_lts 0 r) by lia.
      if_cases K7; zify_bool K7.
      + eapply evt_eq; [ | eapply (KR r) ]; [ fm_eq | ].
        unfold msg_ret. right; left. exists r. split.
        * rewrite fm_scan_step, <- Eml, <- Ety, <- Er. decide_tests. reflexivity.
        * unfold norm_rc. rewrite (proj2 (Z.ltb_ge 0 r)) by lia. reflexivity.
      + step. step. step.                       (* lui a0, 0xf4; addiw a0, a0, 0x240; j *)
        eapply evt_eq; [ | eapply (KR RC_FAILS) ]; [ fm_eq | ].
        unfold msg_ret. right; left. exists r. split.
        * rewrite fm_scan_step, <- Eml, <- Ety, <- Er. decide_tests. reflexivity.
        * unfold norm_rc. rewrite (proj2 (Z.ltb_lt 0 r)) by lia. reflexivity.
    - step. step.                               (* 0x15890: addi a0, zero, -5; j 0x1584c *)
      eapply evt_eq; [ | eapply (KR (- E_IO)) ]; [ fm_eq | ].
      unfold msg_ret. left. split; [|reflexivity].
      rewrite fm_scan_step, <- Eml, <- Ety. decide_tests. reflexivity. }
  (* any other type: step over the message *)
  pose proof (fm_align_range ml ltac:(lia)) as NA.
  step.                                         (* addi s7, s7, 3 *)
  step.                                         (* srliw t1, s7, 2 *)
  rewrite (unsigned_lit (ml + 3)) by lia. rewrite (fm_srliw (ml + 3)) by lia.
  step.                                         (* slli t1, t1, 2 *)
  rewrite (unsigned_lit ((ml + 3) / 4)) by (Z.div_mod_to_equations; lia). rewrite fm_align_eq.
  step.                                         (* sub t0, t0, t1 *)
  rewrite (unsigned_lit left), (unsigned_lit (nl_align ml)) by lia.
  step.                                         (* add a7, a7, t1 *)
  step.                                         (* bge t0, a4 *)
  rewrite (tk_lts (left - nl_align ml) 16) by lia.
  assert (E : msg_scan (S f) ck off left = msg_scan f ck (off + nl_align ml) (left - nl_align ml)).
  { rewrite fm_scan_step, <- Eml, <- Ety. decide_tests. reflexivity. }
  rewrite E in KN, KR, KL.
  if_cases K7; zify_bool K7.
  - eapply evt_eq;
      [ | eapply (IH _ _ _ _ _ (off + nl_align ml) (left - nl_align ml) eq_refl eq_refl eq_refl eq_refl eq_refl
                   HB LC B0 B1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) KN KR KL) ].
    fm_eq.
  - step.                                       (* j 0x157f0 *)
    eapply evt_eq; [ | eapply KN ]; [ fm_eq | ].
    apply fm_scan_short. lia.
Qed.

Print Assumptions F_msg_ok.
