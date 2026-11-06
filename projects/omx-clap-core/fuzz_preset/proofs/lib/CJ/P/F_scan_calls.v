(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib Require SFModel.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P Require F_sf_helpers2.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P Require F_f128_mul.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P Require F_sf_helpers3.
Module F_f128_div_wide.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.SFModel.
Import OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P.F_sf_helpers2 OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P.F_f128_mul.F_f128_mul_core1 OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P.F_sf_helpers3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac flia ::= flia_fast.
Local Ltac unfold_sf_in H ::= unfold_sf_in_recast H.
Local Ltac blia ::= blia_fast.
(* [comment removed for export] *)
Local Ltac step ::= step_fast. Local Ltac stepz ::= stepz_fast.
Local Ltac zsimp ::= zsimp_fast.
(* [comment removed for export] *)
Ltac sf_vocab ::=
  cbv beta delta [add64 sub64 mul64 shl64 not64 ltu64 eqz64 nez64 zext32 sext32 srliw mulhu
         is_neg64 sra63 lt_s64 lo64 hi64 wrap64
         ONES64 M32 SIGN64 MASK48 MASKLO ABS_HI INF_HI QUIET_HI QNAN_HI IMPLICIT_HI IMPL3_HI SPEC_K HALF60 DQUIET
         C_HW X_ADJ EXPK EXPK2];
  rewrite ?b2z_Zb2z.

(* [comment removed for export] *)
Ltac folded_check :=
  lazymatch goal with
  | |- (let x := ?b in _) = _ => fail 0 "fold_model_lets stuck at a let with body" b
  | |- _ => idtac
  end.
End F_f128_div_wide.

(* [comment removed for export] *)
Module F_f128_div_core1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.SFModel.
Import OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P.F_sf_helpers2 OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P.F_f128_mul.F_f128_mul_core1 OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P.F_sf_helpers3 F_f128_div_wide.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac flia ::= flia_fast.
Local Ltac unfold_sf_in H ::= unfold_sf_in_recast H.
Local Ltac blia ::= blia_fast.
(* [comment removed for export] *)
Local Ltac step ::= step_fast. Local Ltac stepz ::= stepz_fast.
Local Ltac zsimp ::= zsimp_fast.

Lemma half_iter_range : forall x b, 0 <= half_iter x b < 18446744073709551616.
Proof.
  intros. unfold half_iter, shl64, mul64, mulhu, sub64.
  apply Z_lor_range.
  - apply (zr_shiftr _ 63). apply SoftFloat.wrap64_range. lia.
  - apply SoftFloat.wrap64_range.
Qed.
Ltac hi_rng X := let RX := fresh "R" X in
  assert (RX : 0 <= X < 18446744073709551616) by (cbv delta [X]; apply half_iter_range).
Ltac mulhu_rng X := let RX := fresh "R" X in
  assert (RX : 0 <= X < 18446744073709551616) by (cbv delta [X]; apply mulhu_range; (change (inr64 _) || idtac); zrange).
End F_f128_div_core1.

(* [comment removed for export] *)
Module F_f128_div_core2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.SFModel.
Import OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P.F_sf_helpers2 OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P.F_f128_mul.F_f128_mul_core1 OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P.F_f128_mul OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P.F_sf_helpers3 F_f128_div_wide F_f128_div_core1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac flia ::= flia_fast.
Local Ltac unfold_sf_in H ::= unfold_sf_in_recast H.
Local Ltac blia ::= blia_fast.
(* [comment removed for export] *)
Local Ltac step ::= step_fast. Local Ltac stepz ::= stepz_fast.
Local Ltac zsimp ::= zsimp_fast.

(* [comment removed for export] *)
Definition DC6 (signHi wE q1Hi q1Lo resHi resLo aDHi aDLo bSigHiI bLo : Z) : Z :=
  if negb (Z.leb wE 0) then
    (* [comment removed for export] *)
    let absLo := q1Lo in
    let fracHi := Z.land q1Hi MASK48 in
    let absHi := Z.lor (shl64 (wrap64 wE) 48) fracHi in
    let r2Hi := Z.lor (shl64 resHi 1) (shr64 resLo 63) in
    let r2Lo := shl64 resLo 1 in
    div_round signHi absHi absLo r2Hi r2Lo bSigHiI bLo
  else if Z.leb wE (-113) then mk128 signHi 0
  else
    (* [comment removed for export] *)
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

(* [comment removed for export] *)
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
(* [comment removed for export] *)
Proof. intros. cbv beta delta [DC6 DC6d]. rewrite (proj2 (Z.leb_le wE 0)) by lia. cbv beta iota delta [negb]. rewrite (proj2 (Z.leb_gt wE (-113))) by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma land64_id : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551615 = x.
Proof. intros. rewrite land_W64. apply Z.mod_small. lia. Qed.
Lemma landM32_id : forall x, 0 <= x < 2^32 -> Z.land x 4294967295 = x.
Proof. intros. change 4294967295 with (2^32 - 1). rewrite zb_land_mask by lia. apply Z.mod_small. lia. Qed.
Lemma land63_id : forall x, 0 <= x < 64 -> Z.land x 63 = x.
Proof. intros. rewrite <- mod64_land63. apply Z.mod_small. lia. Qed.
(* [comment removed for export] *)
Lemma sext32_id : forall x, 0 <= x < 2^31 ->
  Z.land (Z.lxor (Z.land x 4294967295) 2147483648 - 2147483648) 18446744073709551615 = x.
Proof.
  intros. rewrite landM32_id by lia. change 2147483648 with (2^31). rewrite zb_lxor_pow2_small by lia.
  rewrite land_W64. rewrite Z.add_simpl_r. apply Z.mod_small. lia.
Qed.
(* [comment removed for export] *)
Lemma land_add_neg : forall pe c, pe <= 0 -> 0 <= pe + c -> c < 2^64 ->
  Z.land (Z.land pe 18446744073709551615 + c) 18446744073709551615 = pe + c.
Proof. intros. rewrite !land_W64. Z.div_mod_to_equations. lia. Qed.
(* [comment removed for export] *)
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
(* [comment removed for export] *)
Lemma srai63_mask : forall z, -2^63 <= z < 2^63 ->
  Z.land (Z.shiftr z 63) 18446744073709551615 = (if z <? 0 then 18446744073709551615 else 0).
Proof.
  intros. destruct (Z.ltb_spec0 z 0).
  - rewrite shr63_neg by lia. reflexivity.
  - rewrite shr63_nonneg by lia. reflexivity.
Qed.

Ltac unland :=
  repeat match goal with
  | |- context [Z.land ?x 18446744073709551615] => rewrite (land64_id x) by (first [zrange2 | lia])
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac zeta_head_let :=
  lazymatch goal with
  | |- (let x := ?v in ?c) = ?r =>
      let c' := eval cbv beta in ((fun x : Z => c) v) in
      change (c' = r)
  end.

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
(* [comment removed for export] *)
Ltac simp_amounts :=
  try rewrite !land_sub_neg by lia; try rewrite !sext32_id by lia; try rewrite !land_add_neg by lia; try rewrite !landM32_id by lia;
  try rewrite !isneg_land by lia; try rewrite !isneg_land2 by lia; decide_ifs; try rewrite !land_ones_l by zrange2; rewrite ?Z.land_0_l.
Ltac fold_dc6 := repeat (simp_amounts; first [ fold_head_let | zeta_head_let ]); simp_amounts.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
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
End F_f128_div_core2.

(* [comment removed for export] *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P Require F_f128_mul_top.
Module F_f128_div_top.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.SFModel.
Import OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P.F_sf_helpers2 OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P.F_f128_mul.F_f128_mul_core1 OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P.F_f128_mul OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P.F_f128_mul_top OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P.F_sf_helpers3 F_f128_div_wide F_f128_div_core1 F_f128_div_core2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


Import ListNotations.
Local Open Scope Z_scope.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac flia ::= flia_fast.
Local Ltac unfold_sf_in H ::= unfold_sf_in_recast H.
Local Ltac blia ::= blia_fast.
(* [comment removed for export] *)
Local Ltac step ::= step_fast. Local Ltac stepz ::= stepz_fast.
Local Ltac zsimp ::= zsimp_fast.

(* [comment removed for export] *)
Section Model.
  Variables a_lo a_hi b_lo b_hi : Z.
  Let aExp := shr64 (shl64 a_hi 1) 49.
  Let bExp := shr64 (shl64 b_hi 1) 49.
  Let signHi := shl64 (shr64 (Z.lxor b_hi a_hi) 63) 63.
  Let aSigHi := Z.land a_hi MASK48.
  Let bSigHi := Z.land b_hi MASK48.
  Let aAbsHi := Z.land a_hi ABS_HI.
  Let bAbsHi := Z.land b_hi ABS_HI.

  (* [comment removed for export] *)
  Definition FD_p2b (aSigHi1 aLo1 scale1 : Z) : Z :=
    let '(bSigHi1, bLo1, scale2) :=
      if shr64 bAbsHi 48 =? 0 then
        let '(nhi, nlo, nclz) := norm_denormal bSigHi b_lo in (nhi, nlo, (scale1 + nclz) - 16)
      else (bSigHi, b_lo, scale1) in
    div_core signHi aExp bExp aSigHi1 aLo1 bSigHi1 bLo1 scale2.
  (* [comment removed for export] *)
  Definition FD_p2 : Z :=
    let '(aSigHi1, aLo1, scale1) :=
      if shr64 aAbsHi 48 =? 0 then
        let '(nhi, nlo, nclz) := norm_denormal aSigHi a_lo in (nhi, nlo, 16 - nclz)
      else (aSigHi, a_lo, 0) in
    FD_p2b aSigHi1 aLo1 scale1.
  (* [comment removed for export] *)
  Definition FD_inf : Z :=
    if Z.lor (Z.lxor aAbsHi INF_HI) a_lo =? 0 then
      (if negb (Z.lor b_lo (Z.lxor bAbsHi INF_HI) =? 0) then mk128 (Z.lor signHi INF_HI) 0 else mk128 QNAN_HI 0)
    else if Z.lor b_lo (Z.lxor bAbsHi INF_HI) =? 0 then mk128 signHi 0
    else if Z.lor a_lo aAbsHi =? 0 then
      (if negb (Z.lor b_lo bAbsHi =? 0) then mk128 signHi 0 else mk128 QNAN_HI 0)
    else if Z.lor b_lo bAbsHi =? 0 then mk128 (Z.lor signHi INF_HI) 0
    else FD_p2.
  (* [comment removed for export] *)
  Definition FD_b : Z :=
    let bIsNaN := if bAbsHi =? INF_HI then negb (b_lo =? 0) else negb (bAbsHi <? INF_HI) in
    if bIsNaN then mk128 (Z.lor b_hi QUIET_HI) b_lo else FD_inf.
  (* [comment removed for export] *)
  Definition FD_a : Z :=
    let aIsNaN := if aAbsHi =? INF_HI then negb (a_lo =? 0) else negb (aAbsHi <? INF_HI) in
    if aIsNaN then mk128 (Z.lor a_hi QUIET_HI) a_lo else FD_b.
  (* [comment removed for export] *)
  Definition FD_0b : Z :=
    let bExpM := add64 bExp 0xffffffffffff8001 in
    if bExpM <=? 0xffffffffffff8001 then FD_a
    else div_core signHi aExp bExp aSigHi a_lo bSigHi b_lo 0.
  Definition f128_div_w : Z :=
    let aExpM := add64 aExp 0xffffffffffff8001 in
    if aExpM <? 0xffffffffffff8002 then FD_a else FD_0b.
End Model.

Lemma f128_div_words : forall a_lo a_hi b_lo b_hi,
  0 <= a_lo < 2^64 -> 0 <= a_hi < 2^64 -> 0 <= b_lo < 2^64 -> 0 <= b_hi < 2^64 ->
  f128_div (mk128 a_hi a_lo) (mk128 b_hi b_lo) = f128_div_w a_lo a_hi b_lo b_hi.
Proof.
  intros. unfold f128_div, f128_div_w, FD_0b. rewrite !lo64_mk128, !hi64_mk128 by lia. cbv zeta.
  destruct (_ <? _); destruct (_ <=? _); reflexivity.
Qed.
End F_f128_div_top.

(* [comment removed for export] *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib Require Arr.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib Require SysStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Spec Require Prelim.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Spec Require SoftFloat.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Spec Require FmtFp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Spec Require StrFun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P Require Exit_tac.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P Require SFW1_lemmas.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P Require F_f128_le.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P Require F_fmt_out.
Module F_fmt_calls.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.SFModel OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Arr OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.SysStep.
Import OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Spec.Prelim OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Spec.SoftFloat OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Spec.FmtFp OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Spec.StrFun.

Import OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P.Exit_tac.STRW_tac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P.SFW1_lemmas OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P.F_f128_le OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P.F_sf_helpers2.F_f128_to_u32 OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P.F_f128_mul_top F_f128_div_top OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P.F_fmt_out.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


Import ListNotations.
Open Scope bv_scope.

Lemma le8_lit : forall z, (0 <= z < 2^64)%Z -> Z_to_le_bytes 8 z = le8 (Z_to_bv 64 z).
Proof. intros z Hz. rewrite <- store_bytes_8'. rewrite unsigned_lit by lia. reflexivity. Qed.
Lemma le4_lit : forall z, (0 <= z < 2^64)%Z -> Z_to_le_bytes 4 z = le4 (Z_to_bv 64 z).
Proof. intros z Hz. unfold le4. rewrite unsigned_lit by lia. reflexivity. Qed.
Lemma le1_lit : forall z, (0 <= z < 2^64)%Z -> Z_to_le_bytes 1 z = le1 (Z_to_bv 64 z).
Proof. intros z Hz. unfold le1. rewrite unsigned_lit by lia. reflexivity. Qed.
Ltac fix_litstore :=
  match goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) => rewrite (le1_lit z) by lia
  | _ => idtac
  end.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lo64_range : forall x, 0 <= lo64 x < 2^64.
Proof. intros. unfold lo64, wrap64, ONES64. rewrite land_W64. apply Z.mod_pos_bound. lia. Qed.
Lemma hi64_range : forall x, 0 <= hi64 x < 2^64.
Proof. intros. unfold hi64, wrap64, ONES64. rewrite land_W64. apply Z.mod_pos_bound. lia. Qed.
Definition canon (x : Z) : Z := lo64 x + 2^64 * hi64 x.
Lemma lo64_canon : forall x, lo64 (canon x) = lo64 x.
Proof. intros. unfold canon. apply lo64_words. apply lo64_range. Qed.
Lemma hi64_canon : forall x, hi64 (canon x) = hi64 x.
Proof. intros. unfold canon. apply hi64_words; [apply lo64_range | apply hi64_range]. Qed.

Local Open Scope bv_scope.
End F_fmt_calls.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib Require Import SFModel Arr SysStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Spec Require Import Prelim SoftFloat StrFun FloatScan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P Require Exit_tac.
Import OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P.Exit_tac.STRW_tac.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P Require Import SFW1_lemmas F_f128_le F_f128_mul_top.
Import F_f128_div_top.
Export F_fmt_calls.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P Require Export Shgetc_lemmas.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


Import ListNotations.
Local Open Scope Z_scope.

Lemma f128_ge_canon : forall a b, f128_ge (canon a) (canon b) = f128_ge a b.
Proof. intros. unfold f128_ge. rewrite !lo64_canon, !hi64_canon. reflexivity. Qed.
Lemma f128_to_d_canon : forall a, f128_to_d (canon a) = f128_to_d a.
Proof. intros. unfold f128_to_d. rewrite !lo64_canon, !hi64_canon. reflexivity. Qed.

(* [comment removed for export] *)
Tactic Notation "callw" tactic3(tac) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ tac | post_call segs m ]
  end.
(* [comment removed for export] *)
Ltac br K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia); try (exfalso; lia).

Local Open Scope bv_scope.