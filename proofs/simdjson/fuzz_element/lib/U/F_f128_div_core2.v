(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sf_lib.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import F_sf_helpers F_sf_helpers2 F_f128_mul_core1 F_f128_mul F_sf_helpers3 F_f128_div_wide F_f128_div_core1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast.
Local Ltac unfold_sf_in H ::= unfold_sf_in_recast H.
Local Ltac blia ::= blia_fast.

Local Ltac step ::= step_fast.
Local Ltac zsimp ::= zsimp_fast.

Definition DC6 (signHi wE q1Hi q1Lo resHi resLo aDHi aDLo bSigHiI bLo : Z) : Z :=
  if negb (Z.leb wE 0) then

    let absLo := q1Lo in
    let fracHi := Z.land q1Hi MASK48 in
    let absHi := Z.lor (shl64 (wrap64 wE) 48) fracHi in
    let r2Hi := Z.lor (shl64 resHi 1) (shr64 resLo 63) in
    let r2Lo := shl64 resLo 1 in
    div_round signHi absHi absLo r2Hi r2Lo bSigHiI bLo
  else if Z.leb wE (-113) then mk128 signHi 0
  else

    let shiftw := sext32 (sub64 1 (wrap64 wE)) in
    let shift32 := zext32 shiftw in
    let lsh := add64 (wrap64 wE) 112 in
    let absLo := if is_neg64 (sub64 shift32 64)
                 then Z.lor (shr64 q1Lo (Z.land shiftw 63)) (shl64 (shl64 q1Hi 1) (Z.land (not64 shift32) 63))
                 else shr64 q1Hi (Z.land shift32 63) in
    let absHi0 := shr64 q1Hi (Z.land shiftw 63) in
    let maskS := sra63 (sub64 shift32 64) in
    let lsh32 := zext32 lsh in
    let absHi := Z.land maskS absHi0 in
    let aSHi := if is_neg64 (sub64 lsh32 64)
                then Z.lor (shl64 aDHi (Z.land lsh 63)) (shr64 (shr64 aDLo 1) (Z.land (not64 lsh32) 63))
                else shl64 aDLo (Z.land lsh32 63) in
    let aSLo0 := shl64 aDLo (Z.land lsh 63) in
    let maskL := sra63 (sub64 lsh32 64) in
    let pb1 := mul64 bLo absHi in
    let pb2 := mulhu bLo absLo in
    let pb3 := mul64 bSigHiI absLo in
    let aSLo := Z.land maskL aSLo0 in
    let qbLo := mul64 bLo absLo in
    let qh1 := add64 pb2 pb3 in
    let qb2Lo := shl64 qbLo 1 in
    let qbHi := add64 qh1 pb1 in
    let bor := b2z (Z.ltb aSLo qb2Lo) in
    let d1 := sub64 aSHi bor in
    let qb2Hi := Z.lor (shl64 qbHi 1) (shr64 qbLo 63) in
    let r2Hi := sub64 d1 qb2Hi in
    let r2Lo := sub64 aSLo qb2Lo in
    div_round signHi absHi absLo r2Hi r2Lo bSigHiI bLo.

Definition DC6d (signHi wE q1Hi q1Lo aDHi aDLo bSigHiI bLo : Z) : Z :=
    let shiftw := sext32 (sub64 1 (wrap64 wE)) in
    let shift32 := zext32 shiftw in
    let lsh := add64 (wrap64 wE) 112 in
    let absLo := if is_neg64 (sub64 shift32 64)
                 then Z.lor (shr64 q1Lo (Z.land shiftw 63)) (shl64 (shl64 q1Hi 1) (Z.land (not64 shift32) 63))
                 else shr64 q1Hi (Z.land shift32 63) in
    let absHi0 := shr64 q1Hi (Z.land shiftw 63) in
    let maskS := sra63 (sub64 shift32 64) in
    let lsh32 := zext32 lsh in
    let absHi := Z.land maskS absHi0 in
    let aSHi := if is_neg64 (sub64 lsh32 64)
                then Z.lor (shl64 aDHi (Z.land lsh 63)) (shr64 (shr64 aDLo 1) (Z.land (not64 lsh32) 63))
                else shl64 aDLo (Z.land lsh32 63) in
    let aSLo0 := shl64 aDLo (Z.land lsh 63) in
    let maskL := sra63 (sub64 lsh32 64) in
    let pb1 := mul64 bLo absHi in
    let pb2 := mulhu bLo absLo in
    let pb3 := mul64 bSigHiI absLo in
    let aSLo := Z.land maskL aSLo0 in
    let qbLo := mul64 bLo absLo in
    let qh1 := add64 pb2 pb3 in
    let qb2Lo := shl64 qbLo 1 in
    let qbHi := add64 qh1 pb1 in
    let bor := b2z (Z.ltb aSLo qb2Lo) in
    let d1 := sub64 aSHi bor in
    let qb2Hi := Z.lor (shl64 qbHi 1) (shr64 qbLo 63) in
    let r2Hi := sub64 d1 qb2Hi in
    let r2Lo := sub64 aSLo qb2Lo in
    div_round signHi absHi absLo r2Hi r2Lo bSigHiI bLo.

Lemma DC6_normal : forall s wE q1Hi q1Lo resHi resLo aDHi aDLo bH bL, 0 < wE ->
  DC6 s wE q1Hi q1Lo resHi resLo aDHi aDLo bH bL =
  div_round s (Z.lor (Z.land (Z.shiftl (Z.land wE 18446744073709551615) 48) 18446744073709551615) (Z.land q1Hi 281474976710655))
            q1Lo (Z.lor (Z.land (Z.shiftl resHi 1) 18446744073709551615) (Z.shiftr resLo 63)) (Z.land (Z.shiftl resLo 1) 18446744073709551615) bH bL.
Proof. intros. cbv beta delta [DC6]. rewrite (proj2 (Z.leb_gt wE 0)) by lia. reflexivity. Qed.

Lemma DC6_tiny : forall s wE q1Hi q1Lo resHi resLo aDHi aDLo bH bL, wE <= -113 ->
  DC6 s wE q1Hi q1Lo resHi resLo aDHi aDLo bH bL = mk128 s 0.
Proof. intros. cbv beta delta [DC6]. rewrite (proj2 (Z.leb_le wE 0)) by lia. cbv beta iota delta [negb]. rewrite (proj2 (Z.leb_le wE (-113))) by lia. reflexivity. Qed.

Lemma DC6_denorm : forall s wE q1Hi q1Lo resHi resLo aDHi aDLo bH bL, -113 < wE <= 0 ->
  DC6 s wE q1Hi q1Lo resHi resLo aDHi aDLo bH bL = DC6d s wE q1Hi q1Lo aDHi aDLo bH bL.

Proof. intros. cbv beta delta [DC6 DC6d]. rewrite (proj2 (Z.leb_le wE 0)) by lia. cbv beta iota delta [negb]. rewrite (proj2 (Z.leb_gt wE (-113))) by lia. reflexivity. Qed.

Lemma land64_id : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551615 = x.
Proof. intros. rewrite land_W64. apply Z.mod_small. lia. Qed.
Lemma landM32_id : forall x, 0 <= x < 2^32 -> Z.land x 4294967295 = x.
Proof. intros. change 4294967295 with (2^32 - 1). rewrite zb_land_mask by lia. apply Z.mod_small. lia. Qed.
Lemma land63_id : forall x, 0 <= x < 64 -> Z.land x 63 = x.
Proof. intros. rewrite <- mod64_land63. apply Z.mod_small. lia. Qed.

Lemma sext32_id : forall x, 0 <= x < 2^31 ->
  Z.land (Z.lxor (Z.land x 4294967295) 2147483648 - 2147483648) 18446744073709551615 = x.
Proof.
  intros. rewrite landM32_id by lia. change 2147483648 with (2^31). rewrite zb_lxor_pow2_small by lia.
  rewrite land_W64. rewrite Z.add_simpl_r. apply Z.mod_small. lia.
Qed.
Lemma lxor_2p31_small : forall x, 0 <= x < 2^31 -> Z.lxor x 2147483648 = x + 2147483648.
Proof. intros. change 2147483648 with (2^31). apply zb_lxor_pow2_small; lia. Qed.

Lemma land_add_neg : forall pe c, pe <= 0 -> 0 <= pe + c -> c < 2^64 ->
  Z.land (Z.land pe 18446744073709551615 + c) 18446744073709551615 = pe + c.
Proof. intros. rewrite !land_W64. Z.div_mod_to_equations. lia. Qed.

Lemma isneg_land : forall y, -2^63 <= y < 2^63 ->
  negb (Z.shiftr (Z.land y 18446744073709551615) 63 =? 0) = (y <? 0).
Proof.
  intros. rewrite land_W64, Z.shiftr_div_pow2 by lia.
  destruct (Z.ltb_spec0 y 0); destruct (Z.eqb_spec ((y mod 2^64) / 2^63) 0); cbn; try reflexivity; exfalso;
    Z.div_mod_to_equations; lia.
Qed.

Lemma isneg_land2 : forall y, -2^63 <= y < 2^63 ->
  (Z.shiftr (Z.land y 18446744073709551615) 63 =? 0) = (0 <=? y).
Proof.
  intros. rewrite land_W64, Z.shiftr_div_pow2 by lia.
  destruct (Z.leb_spec0 0 y); destruct (Z.eqb_spec ((y mod 2^64) / 2^63) 0); cbn; try reflexivity; exfalso;
    Z.div_mod_to_equations; lia.
Qed.
Lemma shr63_neg : forall z, -2^63 <= z < 0 -> Z.shiftr z 63 = -1.
Proof. intros. rewrite Z.shiftr_div_pow2 by lia. Z.div_mod_to_equations. lia. Qed.
Lemma shr63_nonneg : forall z, 0 <= z < 2^63 -> Z.shiftr z 63 = 0.
Proof. intros. rewrite Z.shiftr_div_pow2 by lia. Z.div_mod_to_equations. lia. Qed.

Lemma srai63_mask : forall z, -2^63 <= z < 2^63 ->
  Z.land (Z.shiftr z 63) 18446744073709551615 = (if z <? 0 then 18446744073709551615 else 0).
Proof.
  intros. destruct (Z.ltb_spec0 z 0).
  - rewrite shr63_neg by lia. reflexivity.
  - rewrite shr63_nonneg by lia. reflexivity.
Qed.

Lemma amt_xor63 : forall x, 0 <= x -> Z.land (Z.lxor x 63) 63 = Z.land (Z.lxor x 18446744073709551615) 63.
Proof.
  intros. apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec, !Z.lxor_spec.
  destruct (Z.lt_ge_cases i 6).
  - change 18446744073709551615 with (Z.ones 64). rewrite (Z.ones_spec_low 64) by lia.
    change 63 with (Z.ones 6). rewrite (Z.ones_spec_low 6) by lia. reflexivity.
  - change 63 with (Z.ones 6). rewrite (Z.ones_spec_high 6) by lia. now rewrite !Bool.andb_false_r.
Qed.

Ltac unland :=
  repeat match goal with
  | |- context [Z.land ?x 18446744073709551615] => rewrite (land64_id x) by (first [zrange2 | lia])
  end.

Ltac zeta_head_let :=
  lazymatch goal with
  | |- (let x := ?v in ?c) = ?r =>
      let c' := eval cbv beta in ((fun x : Z => c) v) in
      change (c' = r)
  end.
Ltac fold_model_lets3 := repeat first [ fold_head_let | zeta_head_let ].

Ltac decide_ifs :=
  repeat (match goal with
  | |- context [if (?x <? ?y) then _ else _] => first [rewrite (proj2 (Z.ltb_lt x y)) by lia | rewrite (proj2 (Z.ltb_ge x y)) by lia]
  | |- context [if negb (?x <? ?y) then _ else _] => first [rewrite (proj2 (Z.ltb_lt x y)) by lia | rewrite (proj2 (Z.ltb_ge x y)) by lia]
  | |- context [if (?x <=? ?y) then _ else _] => first [rewrite (proj2 (Z.leb_le x y)) by lia | rewrite (proj2 (Z.leb_gt x y)) by lia]
  | |- context [if negb (?x <=? ?y) then _ else _] => first [rewrite (proj2 (Z.leb_le x y)) by lia | rewrite (proj2 (Z.leb_gt x y)) by lia]
  | |- context [if (?x =? ?y) then _ else _] => first [rewrite (proj2 (Z.eqb_eq x y)) by lia | rewrite (proj2 (Z.eqb_neq x y)) by lia]
  | |- context [if negb (?x =? ?y) then _ else _] => first [rewrite (proj2 (Z.eqb_eq x y)) by lia | rewrite (proj2 (Z.eqb_neq x y)) by lia]
  end; change (negb true) with false; change (negb false) with true; cbv beta iota).
Ltac rng X := let RX := fresh "R" X in
  first [ assert (RX : (0 <= X < 18446744073709551616)%Z) by (cbv delta [X]; zrange2) | idtac "note: rng failed for" X ].

Ltac simp_amounts :=
  try rewrite !land_sub_neg by lia; try rewrite !sext32_id by lia; try rewrite !land_add_neg by lia; try rewrite !landM32_id by lia;
  try rewrite !isneg_land by lia; try rewrite !isneg_land2 by lia; decide_ifs; try rewrite !land_ones_l by zrange2; rewrite ?Z.land_0_l.
Ltac fold_dc6 := repeat (simp_amounts; first [ fold_head_let | zeta_head_let ]); simp_amounts.

Lemma divc_tail_arms : forall signHi expM1 q_hi q_lo aLo aSigHiI bSigHiI bLo aHi2 aLoTop a2Lo,
  divc_tail signHi expM1 q_hi q_lo aLo aSigHiI bSigHiI bLo aHi2 aLoTop a2Lo =
  if negb (Z.eqb (shr64 q_hi 49) 0) then
      let q1Lo := Z.lor (shr64 q_lo 1) (shl64 q_hi 63) in
      let q1Hi := shr64 q_hi 1 in
      let aTop := shl64 aLo 48 in
      let pq1 := mul64 q1Hi bLo in
      let pq2 := mul64 q1Lo bSigHiI in
      let pq3 := mulhu q1Lo bLo in
      let d1 := sub64 aTop pq1 in
      let qbLo := mul64 q1Lo bLo in
      let sh := add64 pq3 pq2 in
      let bor := b2z (negb (Z.eqb qbLo 0)) in
      let d2 := sub64 d1 sh in
      let resHi := sub64 d2 bor in
      let resLo := sub64 0 qbLo in
      let wE := expM1 + 1 in
      if negb (Z.ltb wE 0x7fff) then mk128 (Z.lor signHi INF_HI) 0
      else DC6 signHi wE q1Hi q1Lo resHi resLo aSigHiI aLo bSigHiI bLo
  else
      let bit112 := shr64 q_hi 48 in
      let sh := b2z (Z.eqb bit112 0) in
      let q1Hi := Z.lor (shl64 q_hi sh) (shr64 (shr64 q_lo 1) (Z.lxor sh 63)) in
      let q1Lo := shl64 q_lo sh in
      let expSel := if negb (Z.eqb bit112 0) then expM1 + 1 else expM1 in
      let aDHi := Z.lor aHi2 aLoTop in
      let aTop := shl64 aLo 49 in
      let pq2 := mul64 q1Lo bSigHiI in
      let pq3 := mulhu q1Lo bLo in
      let pq1 := mul64 q1Hi bLo in
      let sh2 := add64 pq3 pq2 in
      let qbLo := mul64 q1Lo bLo in
      let d1 := sub64 aTop sh2 in
      let bor := b2z (negb (Z.eqb qbLo 0)) in
      let resLo := sub64 0 qbLo in
      let d2 := sub64 d1 pq1 in
      let resHi := sub64 d2 bor in
      let wE := expSel - 1 in
      if Z.leb 0x7fff wE then mk128 (Z.lor signHi INF_HI) 0
      else DC6 signHi wE q1Hi q1Lo resHi resLo aDHi a2Lo bSigHiI bLo.
Proof.
  intros. cbv beta delta [divc_tail].
  do 2 (lazymatch goal with
        | |- (let x := ?v in ?c) = ?r => let c' := eval cbv beta in ((fun x : Z => c) v) in change (c' = r)
        end).
  destruct (negb (Z.eqb (shr64 q_hi 49) 0)); reflexivity.
Qed.

Lemma bit_sh1 : forall b, 0 <= b <= 1 -> Z.lxor b 1 = Z.b2z (b =? 0).
Proof. intros. assert (b = 0 \/ b = 1) as [->| ->] by lia; reflexivity. Qed.
Lemma bit_sh62 : forall b, 0 <= b <= 1 -> Z.land (Z.lxor b 62) 63 = Z.lxor (Z.b2z (b =? 0)) 63.
Proof. intros. assert (b = 0 \/ b = 1) as [->| ->] by lia; reflexivity. Qed.
Lemma land63_b2z : forall c, Z.land (Z.b2z c) 63 = Z.b2z c.
Proof. intros [|]; reflexivity. Qed.
Lemma bit_wE : forall b e, 0 <= b <= 1 -> b + e + -1 = (if negb (b =? 0) then e + 1 else e) - 1.
Proof. intros. assert (b = 0 \/ b = 1) as [->| ->] by lia; cbn; lia. Qed.

Lemma blez_cond : forall w, (-2^63 <= w < 2^63)%Z ->
  ((0 <? Z.land w 18446744073709551615) && (Z.land w 18446744073709551615 <? 9223372036854775808) = false)%Z <-> (w <= 0)%Z.
Proof.
  intros w Hw. rewrite land_W64.
  destruct (Z.le_gt_cases w 0).
  - split; [lia|intros _]. destruct (Z.eq_dec w 0) as [->|NZ]; [reflexivity|].
    rewrite <- (Z.mod_add _ 1), Z.mod_small by lia.
    apply Bool.andb_false_intro2. apply Z.ltb_ge. lia.
  - rewrite Z.mod_small by lia. split; [|lia]. intros K. exfalso.
    rewrite (proj2 (Z.ltb_lt 0 w)), (proj2 (Z.ltb_lt w _)) in K by lia. discriminate.
Qed.
Lemma bgtz_cond : forall w, (-2^63 <= w < 2^63)%Z ->
  ((0 <? Z.land w 18446744073709551615) && (Z.land w 18446744073709551615 <? 9223372036854775808) = true)%Z <-> (0 < w)%Z.
Proof.
  intros w Hw. pose proof (blez_cond w Hw) as B.
  destruct (_ && _); split; intros; try reflexivity; try lia.
  all: try (destruct (Z.le_gt_cases w 0); [|lia]; exfalso; assert (true = false) by (apply B; lia); discriminate).
  all: try (exfalso; assert (w <= 0)%Z by (apply B; reflexivity); lia).
Qed.
Lemma bgez_cond : forall w, (-2^63 <= w < 2^63)%Z ->
  (Z.land w 18446744073709551615 < 9223372036854775808)%Z <-> (0 <= w)%Z.
Proof. intros. rewrite land_W64. Z.div_mod_to_equations. lia. Qed.
Lemma bltz_cond : forall w, (-2^63 <= w < 2^63)%Z ->
  (9223372036854775808 <= Z.land w 18446744073709551615)%Z <-> (w < 0)%Z.
Proof. intros. rewrite land_W64. Z.div_mod_to_equations. lia. Qed.
Ltac sgn_cond K := first [ apply blez_cond in K; [|lia] | apply bgtz_cond in K; [|lia]
                         | apply bgez_cond in K; [|lia] | apply bltz_cond in K; [|lia] | idtac ].

Section Walk.
  Variables (sp a0w w4 w6 : word).
  Notation spw := (Z_to_bv 64 (bv_unsigned sp + -128)).
  Notation sgn := (bv_unsigned a0w).
  Notation bLo := (bv_unsigned w6).

  Ltac hyp :=
    match goal with
    | H : mem_inv _ ?m |- mem_inv _ ?m => exact H
    | H : munch ?W ?m ?m' |- munch ?W ?m ?m' => exact H
    | H : wmono _ ?m ?m' |- wmono _ ?m ?m' => exact H
    | H : stk _ ?m ?lo ?hi |- stk _ ?m ?lo ?hi => exact H
    | H : rw_cells _ ?m ?A _ |- rw_cells _ ?m ?A _ => exact H
    | H : (?a <= ?b)%Z |- (?a <= ?b)%Z => exact H
    | H : bv_unsigned ?w = _ |- bv_unsigned ?w = _ => exact H
    | H : ?x = ?y |- ?x = ?y => exact H
    | H : ?x <> ?y |- ?x <> ?y => exact H
    | H : (?a <= ?x < ?b)%Z |- (?a <= ?x < ?b)%Z => exact H
    | |- (_ <= _ <= _)%Z => lia
    | |- (0 <= _ < _)%Z => first [zrange2 | lia]
    end.
  Ltac join L := eapply L; try hyp.

  Ltac dc_vocab_term T :=
    eval cbv beta delta [add64 sub64 mul64 shl64 not64 ltu64 eqz64 nez64 zext32 sext32 srliw mulhu
                    is_neg64 sra63 lt_s64 lo64 hi64 wrap64
                    ONES64 M32 SIGN64 MASK48 MASKLO ABS_HI INF_HI QUIET_HI QNAN_HI IMPLICIT_HI C_HW X_ADJ EXPK EXPK2] in T.
  Ltac model_in H :=
    let T := type of H in let T' := dc_vocab_term T in recast_hyp H T';
    rewrite ?b2z_Zb2z in H; zb_fold_lits_in H.
  Ltac eblia := rewrite ?Z.shiftl_mul_pow2 in * by lia; blia.
  Ltac decide_in_cond H c :=
    match c with
    | context [Z.eqb ?x ?y] =>
        first [ rewrite (proj2 (Z.eqb_eq x y)) in H by (clear H; eblia) | rewrite (proj2 (Z.eqb_neq x y)) in H by (clear H; eblia) ]
    | context [Z.ltb ?x ?y] =>
        first [ rewrite (proj2 (Z.ltb_lt x y)) in H by (clear H; eblia) | rewrite (proj2 (Z.ltb_ge x y)) in H by (clear H; eblia) ]
    | context [Z.leb ?x ?y] =>
        first [ rewrite (proj2 (Z.leb_le x y)) in H by (clear H; eblia) | rewrite (proj2 (Z.leb_gt x y)) in H by (clear H; eblia) ]
    end.
  Ltac decide_head H :=
    cbn_bool_in H;
    lazymatch type of H with
    | _ = ?t => match t with context [if ?c then _ else _] => decide_in_cond H c end
    end;
    cbn_bool_in H.
  Ltac res_words := rewrite ?lo64_mk128, ?hi64_mk128 by zrange; first [ apply Z_to_bv_lit_self | weq ].

End Walk.

