(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.

From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree HufWalkKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require HufHarness.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_w4m AF_huf_w4s3b.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

Definition AW4_DBC : Z := 151050438420815295.     

Definition AW4_F3 : Z := 0x89328.
Definition AW4_FL : Z := 0x89480.
Definition AW4_FE : Z := 0x897bc.
Definition AW4_FT : Z := 0x89940.
Definition AW4_FEND : Z := 0x899e0.
Definition AW4_FERR : Z := 0x89a70.
Definition AW4_FX2 : Z := 0x89a78.
Definition AW4_CTZ : Z := 134547.

Section CANSEC1. Context {rc : runConstT}.
Lemma w4l_br_tix : forall E D X Y,
  8192 <= bv_unsigned (edenot E D) -> 52 <= bv_unsigned (edenot E Y) mod 64 <= 63 ->
  branch_taken BC_GEU (edenot E D) (edenot E (EMd M_MUL (ELit 2) (EAlu ALU_SRL X Y))) = true.
Proof.
  intros E D X Y HD HY.
  assert (RX : bv_unsigned (edenot E X) < 2^64)
    by (pose proof (bv_unsigned_in_range _ (edenot E X)); unfold bv_modulus in *; lia).
  pose proof (bv_unsigned_in_range _ (edenot E X)) as [RX0 _].
  cbn [edenot branch_taken].
  rewrite bv_ltu_Z, u_mul64, u_srl64.
  set (s := bv_unsigned (edenot E Y) mod 64) in *.
  change (bv_unsigned (Z_to_bv 64 2)) with 2.
  assert (HI : bv_unsigned (edenot E X) / 2 ^ s < 2 ^ (64 - s)).
  { apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|].
    rewrite <- Z.pow_add_r by lia. replace (s + (64 - s)) with 64 by lia. exact RX. }
  assert (H12 : 2 ^ (64 - s) <= 2 ^ 12) by (apply Z.pow_le_mono_r; lia).
  assert (HP : 0 <= bv_unsigned (edenot E X) / 2 ^ s) by (apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]).
  change (2 ^ 12) with 4096 in H12.
  rewrite Z.mod_small by lia.
  destruct (Z.ltb_spec (bv_unsigned (edenot E D)) (2 * (bv_unsigned (edenot E X) / 2 ^ s))); [lia | reflexivity].
Qed.

Ltac w4l_uzm :=
  first [ w4uz | w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; Z.div_mod_to_equations; lia ].

Lemma w4l_srl_lt : forall E x s, 53 <= bv_unsigned (edenot E s) mod 64 <= 63 ->
  0 <= bv_unsigned (edenot E (EAlu ALU_SRL x s)) < 2048.
Proof.
  intros E x s HS.
  assert (RX : bv_unsigned (edenot E x) < 2^64)
    by (pose proof (bv_unsigned_in_range _ (edenot E x)); unfold bv_modulus in *; lia).
  pose proof (bv_unsigned_in_range _ (edenot E x)) as [RX0 _].
  cbn [edenot]. rewrite u_srl64.
  set (t := bv_unsigned (edenot E s) mod 64) in *.
  assert (HI : bv_unsigned (edenot E x) / 2 ^ t < 2 ^ (64 - t)).
  { apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|].
    rewrite <- Z.pow_add_r by lia. replace (t + (64 - t)) with 64 by lia. exact RX. }
  assert (H12 : 2 ^ (64 - t) <= 2 ^ 11) by (apply Z.pow_le_mono_r; lia).
  assert (HP : 0 <= bv_unsigned (edenot E x) / 2 ^ t) by (apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]).
  change (2 ^ 11) with 2048 in H12. lia.
Qed.

Lemma w4l_shd_ap : forall E X B O k,
  bv_unsigned (edenot E X) < 2^47 -> 0 <= O -> O + 2^44 <= 2^64 ->
  0 <= bv_unsigned (edenot E B) + k -> bv_unsigned (edenot E B) + k + 1 <= 2^64 ->
  bv_unsigned (edenot E B) + k + 1 <= O \/ O + 2^44 <= bv_unsigned (edenot E B) + k ->
  flat E (SA (EAlu ALU_SRL X (ELit 3)) O) (elenZ E (ELit 1)) /\ flat E (SA B k) (elenZ E (ELit 1)) /\
  (estart E (SA (EAlu ALU_SRL X (ELit 3)) O) + elenZ E (ELit 1) <= estart E (SA B k) \/
   estart E (SA B k) + elenZ E (ELit 1) <= estart E (SA (EAlu ALU_SRL X (ELit 3)) O)).
Proof.
  intros E X B O k HX HO1 HO2 HB1 HB2 HAP.
  pose proof (bv_unsigned_in_range _ (edenot E X)) as [RX0 _].
  unfold flat, estart, elenZ. cbn [a_base a_off edenot].
  rewrite u_srl64.
  change (bv_unsigned (Z_to_bv 64 3)) with 3. change (bv_unsigned (Z_to_bv 64 1)) with 1.
  change (2 ^ (3 mod 64)) with 8.
  assert (HD : bv_unsigned (edenot E X) / 8 < 2^44)
    by (apply Z.div_lt_upper_bound; [lia | change (8 * 2^44) with (2^47); lia]).
  assert (HD0 : 0 <= bv_unsigned (edenot E X) / 8) by (apply Z.div_pos; lia).
  repeat split; lia.
Qed.

Ltac w4l_xb :=
  lazymatch goal with
  | |- bv_unsigned (edenot ?E ?X) < _ =>
      let b := eval unfold E in E in
      lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
        rewrite (ez_ok zv E (kE_atoms zv xs) X);
        let na := eval vm_compute in (length zv) in
        cbv [ez]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb];
        repeat match goal with
        | |- context [bv_unsigned (edenot E (EAlu ALU_SRL ?x ?s))] =>
            let HV := fresh "HV" in
            assert (HV : 0 <= bv_unsigned (edenot E (EAlu ALU_SRL x s)) < 2048) by (apply w4l_srl_lt; w4l_uzm);
            let v := fresh "v" in set (v := bv_unsigned (edenot E (EAlu ALU_SRL x s))) in *; clearbody v
        end;
        rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite ?Z.mod_small by lia;
        first [lia | Z.div_mod_to_equations; lia]
      end
  end.

Ltac w4l_apz :=
  w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite ?Z.mod_small by lia;
  match goal with H : KXGoM.apart _ _ _ _ |- _ =>
    let H' := fresh "AP" in pose proof H as H'; unfold KXGoM.apart in H'; lia end.

Lemma w4l_tadr : forall E A x c,
  0 <= c -> bv_unsigned (edenot E A) + 4094 + c < 2^47 ->
  bv_unsigned (edenot E (EAlu ALU_ADD (EAlu ALU_ADD A (EMd M_MUL (ELit 2) (EAlu ALU_SRL x (ELit 53)))) (ELit c))) < 2^47.
Proof.
  intros E A x c Hc HA.
  pose proof (bv_unsigned_in_range _ (edenot E x)) as [RX0 RX]. unfold bv_modulus in RX.
  pose proof (bv_unsigned_in_range _ (edenot E A)) as [RA0 _].
  cbn [edenot]. rewrite !u_add64, u_mul64, u_srl64, !u_lit64a.
  rewrite (Z.mod_small 53 (2 ^ 64)) by lia. rewrite (Z.mod_small 53 64) by lia. rewrite (Z.mod_small 2 (2 ^ 64)) by lia.
  assert (HI : bv_unsigned (edenot E x) / 2 ^ 53 < 2048)
    by (apply Z.div_lt_upper_bound; [lia | change (2 ^ 53 * 2048) with (2 ^ 64); lia]).
  assert (HP : 0 <= bv_unsigned (edenot E x) / 2 ^ 53) by (apply Z.div_pos; lia).
  set (q := bv_unsigned (edenot E x) / 2 ^ 53) in *. set (a := bv_unsigned (edenot E A)) in *.
  rewrite (Z.mod_small (2 * q) (2 ^ 64)) by lia.
  rewrite (Z.mod_small c (2 ^ 64)) by lia.
  rewrite (Z.mod_small (a + 2 * q) (2 ^ 64)) by lia.
  rewrite Z.mod_small by lia. lia.
Qed.

Ltac w4lshd :=
  lazymatch goal with
  | |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) _ /\ _ =>
      apply (w4l_shd_ap E X B O k);
      [ first [ apply w4l_tadr; [lia | w4uz] | w4l_xb ] | lia | lia | w4uz | w4uz | w4l_apz ]
  end.

Lemma w4l_srlw3 : forall E B, bv_unsigned (edenot E B) <= 64 ->
  bv_unsigned (edenot E (EAluw ALU_SRL B (ELit 3))) = bv_unsigned (edenot E B) / 8.
Proof.
  intros E B HB.
  pose proof (bv_unsigned_in_range _ (edenot E B)) as [RB _].
  cbn [edenot].
  rewrite (u_srlw_small (edenot E B) (Z_to_bv 64 3) 3) by
    (first [reflexivity | lia | change (2 ^ (3 mod 32)) with 8; Z.div_mod_to_equations; lia]).
  change (2 ^ (3 mod 32)) with 8. reflexivity.
Qed.

Lemma w4l_and7 : forall E B, 0 <= bv_unsigned (edenot E (EAlu ALU_AND B (ELit 7))) <= 7.
Proof.
  intros E B.
  pose proof (bv_unsigned_in_range _ (edenot E B)) as [RB _].
  cbn [edenot]. rewrite u_and64. change (bv_unsigned (Z_to_bv 64 7)) with (Z.ones 3).
  rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
  pose proof (Z.mod_pos_bound (bv_unsigned (edenot E B)) 8 ltac:(lia)). lia.
Qed.

Lemma w4l_bcv : forall E A O B,
  bv_unsigned (edenot E B) <= 64 ->
  bv_unsigned (edenot E (EAlu ALU_ADD A (EAlu ALU_ADD O (EMd M_MUL (ELit (-1)) (EAluw ALU_SRL B (ELit 3))))))
  = (bv_unsigned (edenot E A) + bv_unsigned (edenot E O) - bv_unsigned (edenot E B) / 8) mod 2^64.
Proof.
  intros E A O B H1.
  pose proof (w4l_srlw3 E B H1) as HS.
  cbn [edenot] in HS |- *.
  rewrite !u_add64, u_mul64, HS.
  change (bv_unsigned (Z_to_bv 64 (-1))) with (2^64 - 1).
  set (a := bv_unsigned (edenot E A)). set (o := bv_unsigned (edenot E O)). set (q := bv_unsigned (edenot E B) / 8).
  rewrite Z.add_mod_idemp_r by lia. rewrite Z.add_assoc. rewrite Z.add_mod_idemp_r by lia.
  replace (a + o + (2^64 - 1) * q) with (a + o - q + q * 2^64) by ring.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma w4l_bcu : forall E A O B,
  bv_unsigned (edenot E B) <= 64 -> bv_unsigned (edenot E B) <= 8 * bv_unsigned (edenot E O) + 7 ->
  bv_unsigned (edenot E A) + bv_unsigned (edenot E O) < 2^64 ->
  branch_taken BC_GEU (edenot E (EAlu ALU_ADD A (EAlu ALU_ADD O (EMd M_MUL (ELit (-1)) (EAluw ALU_SRL B (ELit 3))))))
    (edenot E A) = true.
Proof.
  intros E A O B H1 H2 H3.
  cbn [branch_taken]. rewrite bv_ltu_Z, (w4l_bcv E A O B H1).
  pose proof (bv_unsigned_in_range _ (edenot E A)) as [RA _].
  pose proof (bv_unsigned_in_range _ (edenot E O)) as [RO _].
  pose proof (bv_unsigned_in_range _ (edenot E B)) as [RB _].
  assert (Q0 : 0 <= bv_unsigned (edenot E B) / 8) by (apply Z.div_pos; lia).
  assert (Q1 : bv_unsigned (edenot E B) / 8 < bv_unsigned (edenot E O) + 1) by (apply Z.div_lt_upper_bound; lia).
  rewrite Z.mod_small by lia.
  destruct (Z.ltb_spec (bv_unsigned (edenot E A) + bv_unsigned (edenot E O) - bv_unsigned (edenot E B) / 8)
                       (bv_unsigned (edenot E A))); [lia | reflexivity].
Qed.

Lemma w4l_bce : forall E A O B,
  bv_unsigned (edenot E B) <= 64 -> 8 * bv_unsigned (edenot E O) + 8 <= bv_unsigned (edenot E B) ->
  8 <= bv_unsigned (edenot E A) ->
  branch_taken BC_GEU (edenot E (EAlu ALU_ADD A (EAlu ALU_ADD O (EMd M_MUL (ELit (-1)) (EAluw ALU_SRL B (ELit 3))))))
    (edenot E A) = false.
Proof.
  intros E A O B H1 H2 H3.
  cbn [branch_taken]. rewrite bv_ltu_Z, (w4l_bcv E A O B H1).
  pose proof (bv_unsigned_in_range _ (edenot E A)) as [_ RA]. unfold bv_modulus in RA.
  pose proof (bv_unsigned_in_range _ (edenot E O)) as [RO _].
  assert (Q1 : bv_unsigned (edenot E O) + 1 <= bv_unsigned (edenot E B) / 8) by (apply Z.div_le_lower_bound; lia).
  assert (Q2 : bv_unsigned (edenot E B) / 8 <= 8) by (apply Z.div_le_upper_bound; lia).
  rewrite Z.mod_small by lia.
  destruct (Z.ltb_spec (bv_unsigned (edenot E A) + bv_unsigned (edenot E O) - bv_unsigned (edenot E B) / 8)
                       (bv_unsigned (edenot E A))); [reflexivity | lia].
Qed.

Ltac w4l_brs :=
  w4ez; rewrite ?w4l_srlw3 by w4uz; w4ez;
  unfold branch_taken; try unfold bv_lts;
  rewrite ?bv_ltu_Z, ?bv_eqb_Z, ?zb_signed, ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
  rewrite ?Z.mod_small by (Z.div_mod_to_equations; lia);
  repeat match goal with |- context [(?x <? ?y)%Z] => destruct (Z.ltb_spec x y) end;
  repeat match goal with |- context [(?x =? ?y)%Z] => destruct (Z.eqb_spec x y) end;
  cbn [negb]; first [reflexivity | exfalso; Z.div_mod_to_equations; lia].

Definition AW4_L1398 : Z := 0x894dc.
Definition AW4_L1534 : Z := 0x896fc.
Definition AW4_L1631 : Z := 0x89880.
Definition AW4_L1674 : Z := 0x8992c.
Definition AW4_L1675 : Z := 0x89930.

Notation w4ls1375 se sP gp tp ps x6 x7 bc SS off x11 x12 x13 x14 k x16 DT p x28 :=
  (mkR (Z_to_bv 64 se) (Z_to_bv 64 (sP + -480)) gp tp (Z_to_bv 64 ps) x6 x7 (Z_to_bv 64 (SS + 8))
       (Z_to_bv 64 bc) (Z_to_bv 64 (SS + off)) x11 x12 x13 x14 (Z_to_bv 64 k) x16 (Z_to_bv 64 (2^64 - DT - 5))
       (Z_to_bv 64 (se - ps)) (Z_to_bv 64 SS) (Z_to_bv 64 se) (Z_to_bv 64 (sP + -344 + 8 * k)) (Z_to_bv 64 p)
       (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 AW4_KSB) (Z_to_bv 64 (p - ps)) (Z_to_bv 64 AW4_KTB) (Z_to_bv 64 (se - 3)) x28
       (Z_to_bv 64 2) (Z_to_bv 64 (-1)) (Z_to_bv 64 64)).

Notation w4ls1398 se sP gp tp ps x6 x7 b SS o nb p st x14 k x16 DT x28 :=
  (mkR (Z_to_bv 64 se) (Z_to_bv 64 (sP + -480)) gp tp (Z_to_bv 64 ps) x6 x7 (Z_to_bv 64 (SS + 8))
       (Z_to_bv 64 b) (Z_to_bv 64 (SS + o + nb)) (Z_to_bv 64 p) (Z_to_bv 64 nb) (Z_to_bv 64 st) x14 (Z_to_bv 64 k) x16
       (Z_to_bv 64 (2^64 - DT - 5)) (Z_to_bv 64 (se - ps)) (Z_to_bv 64 SS) (Z_to_bv 64 se) (Z_to_bv 64 (sP + -344 + 8 * k))
       (Z_to_bv 64 p) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 AW4_KSB) (Z_to_bv 64 (p - ps)) (Z_to_bv 64 AW4_KTB)
       (Z_to_bv 64 (se - 3)) x28 (Z_to_bv 64 2) (Z_to_bv 64 (-1)) (Z_to_bv 64 64)).

Notation w4ls1534 se sP gp tp ps x6 x7 x9 SS off p x12 x13 x14 k x16 DT x28 :=
  (mkR (Z_to_bv 64 se) (Z_to_bv 64 (sP + -480)) gp tp (Z_to_bv 64 ps) x6 x7 (Z_to_bv 64 (SS + 8))
       x9 (Z_to_bv 64 (SS + off)) (Z_to_bv 64 (p + 3)) x12 x13 x14 (Z_to_bv 64 k) x16 (Z_to_bv 64 (2^64 - DT - 5))
       (Z_to_bv 64 (se - ps)) (Z_to_bv 64 SS) (Z_to_bv 64 se) (Z_to_bv 64 (sP + -344 + 8 * k)) (Z_to_bv 64 p)
       (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 AW4_KSB) (Z_to_bv 64 (p - ps)) (Z_to_bv 64 AW4_KTB) (Z_to_bv 64 (se - 3)) x28
       (Z_to_bv 64 2) (Z_to_bv 64 (-1)) (Z_to_bv 64 64)).

Notation w4lx1631 se sP gp tp ps k DT op y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y16 y19 y25 y27 y28 :=
  (mkR (Z_to_bv 64 se) (Z_to_bv 64 (sP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14
       (Z_to_bv 64 k) y16 (Z_to_bv 64 (2^64 - DT - 5)) (Z_to_bv 64 (se - ps))
       y19 (Z_to_bv 64 se) (Z_to_bv 64 (sP + -344 + 8 * k)) (Z_to_bv 64 op) (Z_to_bv 64 (DT + 4))
       (Z_to_bv 64 AW4_KSB) y25 (Z_to_bv 64 AW4_KTB) y27 y28 (Z_to_bv 64 2) (Z_to_bv 64 (-1)) (Z_to_bv 64 64)).

Notation w4lx1675 se sP gp tp ps k DT op y5 y6 y7 y8 y9 y10 y12 y13 y14 y16 y19 y22 y25 y27 y28 :=
  (mkR (Z_to_bv 64 se) (Z_to_bv 64 (sP + -480)) gp tp y5 y6 y7 y8 y9 y10 (Z_to_bv 64 op) y12 y13 y14
       (Z_to_bv 64 k) y16 (Z_to_bv 64 (2^64 - DT - 5)) (Z_to_bv 64 (se - ps))
       y19 (Z_to_bv 64 se) (Z_to_bv 64 (sP + -344 + 8 * k)) y22 (Z_to_bv 64 (DT + 4))
       (Z_to_bv 64 AW4_KSB) y25 (Z_to_bv 64 AW4_KTB) y27 y28 (Z_to_bv 64 2) (Z_to_bv 64 (-1)) (Z_to_bv 64 64)).

Notation w4lx1674 se sP gp tp ps k DT u v y6 y7 y8 y9 y10 y11 y12 y13 y14 y16 y19 y22 y27 y28 :=
  (mkR (Z_to_bv 64 se) (Z_to_bv 64 (sP + -480)) gp tp (Z_to_bv 64 u) y6 y7 y8 y9 y10 y11 y12 y13 y14
       (Z_to_bv 64 k) y16 (Z_to_bv 64 (2^64 - DT - 5)) (Z_to_bv 64 (se - ps))
       y19 (Z_to_bv 64 se) (Z_to_bv 64 (sP + -344 + 8 * k)) y22 (Z_to_bv 64 (DT + 4))
       (Z_to_bv 64 AW4_KSB) (Z_to_bv 64 v) (Z_to_bv 64 AW4_KTB) y27 y28 (Z_to_bv 64 2) (Z_to_bv 64 (-1)) (Z_to_bv 64 64)).

Definition w4lmem (RNG : footprint) (mm : amem) (sP DST dcap SS DT dtl nn SBL SBH : Z) (bs cbs : list byte) (buf : list Z) : Prop :=
  bytes_at bsegs mm SS bs /\ Z.of_nat (length bs) = nn /\
  bytes_at bsegs mm (DT + 4) cbs /\ Z.of_nat (length cbs) = 4096 /\
  u8arr bsegs mm DST (map (Z_to_bv 8) buf) /\ Z.of_nat (length buf) = dcap /\
  unpoisoned mm SBL SBH /\ unpoisoned mm DT (DT + dtl) /\ unpoisoned mm DST (DST + dcap) /\
  rng RNG SBL (SBH - SBL) /\ rng RNG DT dtl /\ rng RNG DST dcap /\
  rng RNG (shad SBL) (shlen (SBH - SBL + 7)) /\ rng RNG (shad DT) (shlen (dtl + 7)) /\ rng RNG (shad DST) (shlen (dcap + 7)) /\
  SBL mod 8 = 0 /\ DT mod 8 = 0 /\ DST mod 8 = 0 /\ 0 <= SBL /\ 0 <= DT /\ 0 <= DST /\
  SBL <= SS /\ SS + nn <= SBH /\ DT + 4 + 4096 <= DT + dtl /\
  KXGoM.apart DST dcap DT dtl /\ KXGoM.apart DST dcap SS nn /\ KXGoM.apart DT dtl SS nn /\
  KXGoM.apart SBL (SBH - SBL) ASHOFF (2^44) /\ KXGoM.apart DT dtl ASHOFF (2^44) /\ KXGoM.apart DST dcap ASHOFF (2^44) /\
  mem_inv bsegs mm /\ rng_aimg RNG /\
  4096 <= DST /\ DST + dcap <= 2^47 /\ 0 <= dcap <= 2^32 - 1 /\ 4096 <= SS /\ SS + nn <= 2^47 /\ 4096 <= DT /\
  DT + dtl <= 2^47 /\ 8 <= nn <= 2^26 /\ 8192 <= sP <= 2^47.

Lemma w4l_st : forall (RNG : footprint) (Q : machine_state -> Prop) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16
    x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16
    y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word) F pc fc m rom,
  evtF bsegs RNG Q (MS (mkR y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25
                            y26 y27 y28 y29 y30 y31) F pc fc None m rom) ->
  x1 = y1 -> x2 = y2 -> x3 = y3 -> x4 = y4 -> x5 = y5 -> x6 = y6 -> x7 = y7 -> x8 = y8 -> x9 = y9 -> x10 = y10 ->
  x11 = y11 -> x12 = y12 -> x13 = y13 -> x14 = y14 -> x15 = y15 -> x16 = y16 -> x17 = y17 -> x18 = y18 -> x19 = y19 ->
  x20 = y20 -> x21 = y21 -> x22 = y22 -> x23 = y23 -> x24 = y24 -> x25 = y25 -> x26 = y26 -> x27 = y27 -> x28 = y28 ->
  x29 = y29 -> x30 = y30 -> x31 = y31 ->
  evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
                            x26 x27 x28 x29 x30 x31) F pc fc None m rom).
Proof. intros; subst; assumption. Qed.

Ltac w4l_eq :=
  first [ reflexivity | f_equal; lia | rewrite Z_to_bv_bv_unsigned; reflexivity ].

Lemma w4l_b64t : forall E a, bv_unsigned (edenot E a) <= 64 -> branch_taken BC_GEU (edenot E (ELit 64)) (edenot E a) = true.
Proof.
  intros E a H. cbn [branch_taken]. rewrite bv_ltu_Z. change (bv_unsigned (edenot E (ELit 64))) with 64.
  destruct (Z.ltb_spec 64 (bv_unsigned (edenot E a))); [lia | reflexivity].
Qed.

Lemma w4l_b64f : forall E a, 64 < bv_unsigned (edenot E a) -> branch_taken BC_GEU (edenot E (ELit 64)) (edenot E a) = false.
Proof.
  intros E a H. cbn [branch_taken]. rewrite bv_ltu_Z. change (bv_unsigned (edenot E (ELit 64))) with 64.
  destruct (Z.ltb_spec 64 (bv_unsigned (edenot E a))); [reflexivity | lia].
Qed.

Ltac w4l_atm :=
  lazymatch goal with |- context [edenot ?E _] =>
    let b := eval unfold E in E in
    lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
      change E with (kE zv xs); cbn [edenot];
      repeat rewrite (kE_atoms zv xs) by (apply Nat.ltb_lt; vm_compute; reflexivity);
      cbv [nth]; rewrite ?Z_to_bv_bv_unsigned
    end
  end.

Lemma w4l_stE : forall E A O B,
  bv_unsigned (edenot E B) <= 64 -> 8 * bv_unsigned (edenot E O) + 8 <= bv_unsigned (edenot E B) ->
  8 <= bv_unsigned (edenot E A) ->
  edenot E (EAlu ALU_XOR (EAlu ALU_SLTU (EAlu ALU_ADD A (EAlu ALU_ADD O (EMd M_MUL (ELit (-1)) (EAluw ALU_SRL B (ELit 3))))) A)
              (ELit 1)) = Z_to_bv 64 0.
Proof.
  intros E A O B H1 H2 H3.
  pose proof (w4l_bce E A O B H1 H2 H3) as HB. cbn [branch_taken] in HB. rewrite bv_ltu_Z in HB.
  apply bv_eq. revert HB. cbn [edenot]. rewrite u_xor64, u_sltu64.
  destruct (_ <? _); cbn [negb]; intros HB; [reflexivity | discriminate].
Qed.

Lemma w4l_stU : forall E A O B,
  bv_unsigned (edenot E B) <= 64 -> bv_unsigned (edenot E B) <= 8 * bv_unsigned (edenot E O) + 7 ->
  bv_unsigned (edenot E A) + bv_unsigned (edenot E O) < 2^64 ->
  edenot E (EAlu ALU_XOR (EAlu ALU_SLTU (EAlu ALU_ADD A (EAlu ALU_ADD O (EMd M_MUL (ELit (-1)) (EAluw ALU_SRL B (ELit 3))))) A)
              (ELit 1)) = Z_to_bv 64 1.
Proof.
  intros E A O B H1 H2 H3.
  pose proof (w4l_bcu E A O B H1 H2 H3) as HB. cbn [branch_taken] in HB. rewrite bv_ltu_Z in HB.
  apply bv_eq. revert HB. cbn [edenot]. rewrite u_xor64, u_sltu64.
  destruct (_ <? _); cbn [negb]; intros HB; [discriminate | reflexivity].
Qed.

Ltac w4l_cnd :=
  first [ lia
        | lazymatch goal with |- context [bv_unsigned (edenot ?E (EAlu ALU_AND ?B (ELit 7)))] =>
            pose proof (w4l_and7 E B); lia end
        | rewrite ?w4l_srlw3 by w4uz; w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
          rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia ].

Ltac w4l_post WIN WINL buf :=
  kx_post_regs_keep;
  lazymatch goal with H : u8arr bsegs ?m _ (map _ buf), HL : log_flat _ _ |- _ =>
    let buf' := fresh "buf'" in let OUT' := fresh "OUT'" in let LB' := fresh "LB'" in
    destruct (kx_u8arr_ex bsegs _ m _ _ buf H HL) as (buf' & OUT' & LB');
    let MUW := fresh "MUW" in let WMr := fresh "WMr" in
    pose proof (munch_refl WIN m) as MUW; pose proof (wmono_refl bsegs m) as WMr;
    kx_munch_wins MUW WINL
  end;
  kx_post_mem_free.

Ltac w4l_side :=
  try (lazymatch goal with |- branch_taken BC_GEU (edenot ?E ?D) (edenot ?E (EMd M_MUL (ELit 2) (EAlu ALU_SRL ?X ?Y))) = true =>
         apply (w4l_br_tix E D X Y); w4l_uzm end);
  try (lazymatch goal with |- flat _ _ _ /\ _ => w4lshd end).

Lemma w4l_r0 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (bs cbs : list byte) (buf : list Z) (gp tp x6 x7 x11 x12 x13 x14 x16 x28 : word)
    (sP DST dcap SS DT dtl nn off bc k se ps p SBL SBH : Z),
  w4lmem RNG mm sP DST dcap SS DT dtl nn SBL SBH bs cbs buf ->
  off = 0 -> off + 8 <= nn -> DST <= ps -> ps <= p -> p <= se -> se <= DST + dcap -> 0 <= bc <= 64 -> 0 <= k <= 3 ->
  (forall (y5 y6 y7 y8 y9 y10 y12 y13 y14 y16 y19 y22 y25 y27 y28 : word),
     evtF bsegs RNG Q (MS (w4lx1675 se sP gp tp ps k DT p y5 y6 y7 y8 y9 y10 y12 y13 y14 y16 y19 y22 y25 y27 y28)
                          F (Z_to_bv 64 AW4_L1675) fc None mm (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (w4ls1375 se sP gp tp ps x6 x7 bc SS off x11 x12 x13 x14 k x16 DT p x28)
                       F (Z_to_bv 64 AW4_FL) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc bs cbs buf gp tp x6 x7 x11 x12 x13 x14 x16 x28 sP DST dcap SS DT dtl nn off bc k se ps p SBL SBH
    HM HO HON HP1 HP2 HP3 HP4 HB HK K.
  unfold w4lmem in HM. decompose [and] HM. clear HM. unfold AW4_KTB, AW4_KSB.
  kx_runFLd [0x89930; 0x89480; 0x89880; 0x8992c; 0x896fc; 0x894dc] 120%nat (repeat false 64)
      [KZRange DST 4096 (2^47); KZRange dcap 0 (2^32 - 1); KZRange (DST + dcap) 4096 (2^47); KZRange SS 4096 (2^47);
       KZRange (SS + nn) 4096 (2^47); KZRange DT 4096 (2^47); KZRange nn 8 (2^26); KZRange off 0 0; KZRange (nn - off) 8 (2^26);
       KZRange ps 4096 (2^47); KZRange (ps - DST) 0 (2^32); KZRange (p - ps) 0 (2^32); KZRange p 4096 (2^47);
       KZRange (se - p) 0 (2^32); KZRange se 4096 (2^47); KZRange (DST + dcap - se) 0 (2^32); KZRange bc 0 64;
       KZRange k 0 3; KZRange sP 8192 (2^47); KZIdx 11 2048]
      [(SS, nn); (DT + 4, 4096)] [(SS, nn); (DT + 4, 4096)] [(SS, nn); (DT + 4, 4096)].
  kx_post_regs. cbn [mem_denot].
  eapply w4l_st; [apply K | ..]; w4l_eq.
Time Qed.

Lemma w4l_andv : forall E B, bv_unsigned (edenot E (EAlu ALU_AND B (ELit 7))) = bv_unsigned (edenot E B) mod 8.
Proof.
  intros E B. cbn [edenot]. rewrite u_and64. change (bv_unsigned (Z_to_bv 64 7)) with (Z.ones 3).
  rewrite Z.land_ones by lia. change (2 ^ 3) with 8. reflexivity.
Qed.

Ltac w4l_weq :=
  first [ reflexivity | f_equal; lia | rewrite Z_to_bv_bv_unsigned; reflexivity
        | apply bv_eq; rewrite ?w4l_andv; rewrite ?w4l_srlw3 by w4uz; w4ez; rewrite ?Z_to_bv_unsigned;
          unfold bv_wrap, bv_modulus; rewrite ?Z.mod_small by (Z.div_mod_to_equations; lia);
          Z.div_mod_to_equations; lia ].

Lemma w4l_rf : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (bs cbs : list byte) (buf : list Z) (gp tp x6 x7 x11 x12 x13 x14 x16 x28 : word)
    (sP DST dcap SS DT dtl nn off bc k se ps p SBL SBH : Z),
  w4lmem RNG mm sP DST dcap SS DT dtl nn SBL SBH bs cbs buf ->
  8 <= off -> off + 8 <= nn -> DST <= ps -> ps <= p -> p <= se -> se <= DST + dcap -> 0 <= bc <= 64 -> 0 <= k <= 3 ->
  evtF bsegs RNG Q (MS (w4ls1398 se sP gp tp ps x6 x7 (bc mod 8) SS (off - bc / 8) (bc / 8) p 1 x14 k x16 DT x28)
                       F (Z_to_bv 64 AW4_L1398) fc None mm (seg_rom bsegs)) ->
  evtF bsegs RNG Q (MS (w4ls1375 se sP gp tp ps x6 x7 bc SS off x11 x12 x13 x14 k x16 DT p x28)
                       F (Z_to_bv 64 AW4_FL) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc bs cbs buf gp tp x6 x7 x11 x12 x13 x14 x16 x28 sP DST dcap SS DT dtl nn off bc k se ps p SBL SBH
    HM HO HON HP1 HP2 HP3 HP4 HB HK K.
  unfold w4lmem in HM. decompose [and] HM. clear HM. unfold AW4_KTB, AW4_KSB.
  kx_runFLd [0x894dc; 0x89480; 0x89930; 0x89880; 0x8992c; 0x896fc] 120%nat (repeat false 64)
      [KZRange DST 4096 (2^47); KZRange dcap 0 (2^32 - 1); KZRange (DST + dcap) 4096 (2^47); KZRange SS 4096 (2^47);
       KZRange (SS + nn) 4096 (2^47); KZRange DT 4096 (2^47); KZRange nn 8 (2^26); KZRange off 8 (2^26); KZRange (nn - off) 8 (2^26);
       KZRange ps 4096 (2^47); KZRange (ps - DST) 0 (2^32); KZRange (p - ps) 0 (2^32); KZRange p 4096 (2^47);
       KZRange (se - p) 0 (2^32); KZRange se 4096 (2^47); KZRange (DST + dcap - se) 0 (2^32); KZRange bc 0 64;
       KZRange k 0 3; KZRange sP 8192 (2^47); KZIdx 11 2048]
      [(SS, nn); (DT + 4, 4096)] [(SS, nn); (DT + 4, 4096)] [(SS, nn); (DT + 4, 4096)].
  kx_post_regs. cbn [mem_denot].
  eapply w4l_st; [apply K | ..]; w4l_weq.
Time Qed.

Ltac w4l_xeq :=
  first [ rewrite w4l_stU by w4uz; reflexivity | rewrite w4l_stE by w4uz; reflexivity | w4l_weq ].

Lemma w4l_rcu : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (bs cbs : list byte) (buf : list Z) (gp tp x6 x7 x11 x12 x13 x14 x16 x28 : word)
    (sP DST dcap SS DT dtl nn off bc k se ps p SBL SBH : Z),
  w4lmem RNG mm sP DST dcap SS DT dtl nn SBL SBH bs cbs buf ->
  1 <= off <= 7 -> off + 8 <= nn -> DST <= ps -> ps <= p -> p <= se -> se <= DST + dcap -> 0 <= bc <= 64 ->
  bc <= 8 * off + 7 -> 0 <= k <= 3 ->
  (forall y14 y16 : word,
     evtF bsegs RNG Q (MS (w4ls1398 se sP gp tp ps x6 x7 (bc mod 8) SS (off - bc / 8) (bc / 8) p 1 y14 k y16 DT x28)
                          F (Z_to_bv 64 AW4_L1398) fc None mm (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (w4ls1375 se sP gp tp ps x6 x7 bc SS off x11 x12 x13 x14 k x16 DT p x28)
                       F (Z_to_bv 64 AW4_FL) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc bs cbs buf gp tp x6 x7 x11 x12 x13 x14 x16 x28 sP DST dcap SS DT dtl nn off bc k se ps p SBL SBH
    HM HO HON HP1 HP2 HP3 HP4 HB HBO HK K.
  unfold w4lmem in HM. decompose [and] HM. clear HM. unfold AW4_KTB, AW4_KSB.
  kx_runFLd [0x894dc; 0x89480; 0x89930; 0x89880; 0x8992c; 0x896fc] 120%nat (true :: repeat false 63)
      [KZRange DST 4096 (2^47); KZRange dcap 0 (2^32 - 1); KZRange (DST + dcap) 4096 (2^47); KZRange SS 4096 (2^47);
       KZRange (SS + nn) 4096 (2^47); KZRange DT 4096 (2^47); KZRange nn 8 (2^26); KZRange off 1 7; KZRange (nn - off) 8 (2^26);
       KZRange ps 4096 (2^47); KZRange (ps - DST) 0 (2^32); KZRange (p - ps) 0 (2^32); KZRange p 4096 (2^47);
       KZRange (se - p) 0 (2^32); KZRange se 4096 (2^47); KZRange (DST + dcap - se) 0 (2^32); KZRange bc 0 64;
       KZRange k 0 3; KZRange sP 8192 (2^47); KZIdx 11 2048]
      [(SS, nn); (DT + 4, 4096)] [(SS, nn); (DT + 4, 4096)] [(SS, nn); (DT + 4, 4096)].
  all: try (lazymatch goal with |- branch_taken _ _ _ = _ => apply w4l_bcu; w4uz end).
  kx_post_regs. cbn [mem_denot].
  eapply w4l_st; [apply K | ..]; w4l_xeq.
Time Qed.

Lemma w4l_rce : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (bs cbs : list byte) (buf : list Z) (gp tp x6 x7 x11 x12 x13 x14 x16 x28 : word)
    (sP DST dcap SS DT dtl nn off bc k se ps p SBL SBH : Z),
  w4lmem RNG mm sP DST dcap SS DT dtl nn SBL SBH bs cbs buf ->
  1 <= off <= 7 -> off + 8 <= nn -> DST <= ps -> ps <= p -> p <= se -> se <= DST + dcap -> 0 <= bc <= 64 ->
  8 * off + 8 <= bc -> 0 <= k <= 3 ->
  (forall y14 y16 : word,
     evtF bsegs RNG Q (MS (w4ls1398 se sP gp tp ps x6 x7 (bc - 8 * off) SS 0 off p 0 y14 k y16 DT x28)
                          F (Z_to_bv 64 AW4_L1398) fc None mm (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (w4ls1375 se sP gp tp ps x6 x7 bc SS off x11 x12 x13 x14 k x16 DT p x28)
                       F (Z_to_bv 64 AW4_FL) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc bs cbs buf gp tp x6 x7 x11 x12 x13 x14 x16 x28 sP DST dcap SS DT dtl nn off bc k se ps p SBL SBH
    HM HO HON HP1 HP2 HP3 HP4 HB HBO HK K.
  unfold w4lmem in HM. decompose [and] HM. clear HM. unfold AW4_KTB, AW4_KSB.
  kx_runFLd [0x894dc; 0x89480; 0x89930; 0x89880; 0x8992c; 0x896fc] 120%nat (repeat false 64)
      [KZRange DST 4096 (2^47); KZRange dcap 0 (2^32 - 1); KZRange (DST + dcap) 4096 (2^47); KZRange SS 4096 (2^47);
       KZRange (SS + nn) 4096 (2^47); KZRange DT 4096 (2^47); KZRange nn 8 (2^26); KZRange off 1 7; KZRange (nn - off) 8 (2^26);
       KZRange ps 4096 (2^47); KZRange (ps - DST) 0 (2^32); KZRange (p - ps) 0 (2^32); KZRange p 4096 (2^47);
       KZRange (se - p) 0 (2^32); KZRange se 4096 (2^47); KZRange (DST + dcap - se) 0 (2^32); KZRange bc 0 64;
       KZRange k 0 3; KZRange sP 8192 (2^47); KZIdx 11 2048]
      [(SS, nn); (DT + 4, 4096)] [(SS, nn); (DT + 4, 4096)] [(SS, nn); (DT + 4, 4096)].
  all: try (lazymatch goal with |- branch_taken _ _ _ = _ => apply w4l_bce; w4uz end).
  kx_post_regs. cbn [mem_denot].
  eapply w4l_st; [apply K | ..]; w4l_xeq.
Time Qed.

Lemma w4l_j0 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (bs cbs : list byte) (buf : list Z) (gp tp x6 x7 x14 x16 x28 : word)
    (sP DST dcap SS DT dtl nn o nb b st k se ps p SBL SBH : Z),
  w4lmem RNG mm sP DST dcap SS DT dtl nn SBL SBH bs cbs buf ->
  0 <= o -> 0 <= nb <= 8 -> o + nb + 8 <= nn -> DST <= ps -> ps <= p -> p <= se -> se <= DST + dcap -> 0 <= b <= 64 ->
  0 <= k <= 3 -> (st = 0 \/ (st = 1 /\ se < p + 4)) ->
  (forall (y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y16 y19 y25 y27 y28 : word),
     evtF bsegs RNG Q (MS (w4lx1631 se sP gp tp ps k DT p y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y16 y19 y25 y27 y28)
                          F (Z_to_bv 64 AW4_L1631) fc None mm (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (w4ls1398 se sP gp tp ps x6 x7 b SS o nb p st x14 k x16 DT x28)
                       F (Z_to_bv 64 AW4_L1398) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc bs cbs buf gp tp x6 x7 x14 x16 x28 sP DST dcap SS DT dtl nn o nb b st k se ps p SBL SBH
    HM HO HNB HON HP1 HP2 HP3 HP4 HB HK HST K.
  unfold w4lmem in HM. decompose [and] HM. clear HM. unfold AW4_KTB, AW4_KSB.
  destruct HST as [HST | [HST HSE]]; subst st.
  - kx_runFLd [0x896fc; 0x89480; 0x89930; 0x89880; 0x8992c; 0x894dc] 120%nat (repeat false 64)
      [KZRange DST 4096 (2^47); KZRange dcap 0 (2^32 - 1); KZRange (DST + dcap) 4096 (2^47); KZRange SS 4096 (2^47);
       KZRange (SS + nn) 4096 (2^47); KZRange DT 4096 (2^47); KZRange nn 8 (2^26); KZRange o 0 (2^26); KZRange nb 0 8;
       KZRange (nn - o) 8 (2^26); KZRange ps 4096 (2^47); KZRange (ps - DST) 0 (2^32); KZRange (p - ps) 0 (2^32);
       KZRange p 4096 (2^47); KZRange (se - p) 0 (2^32); KZRange se 4096 (2^47); KZRange (DST + dcap - se) 0 (2^32);
       KZRange b 0 64; KZRange k 0 3; KZRange sP 8192 (2^47); KZIdx 11 2048]
      [(SS, nn); (DT + 4, 4096)] [(SS, nn); (DT + 4, 4096)] [(SS, nn); (DT + 4, 4096)].
    kx_post_regs. cbn [mem_denot].
    eapply w4l_st; [apply K | ..]; w4l_eq.
  - kx_runFLd [0x896fc; 0x89480; 0x89930; 0x89880; 0x8992c; 0x894dc] 120%nat (repeat false 64)
      [KZRange DST 4096 (2^47); KZRange dcap 0 (2^32 - 1); KZRange (DST + dcap) 4096 (2^47); KZRange SS 4096 (2^47);
       KZRange (SS + nn) 4096 (2^47); KZRange DT 4096 (2^47); KZRange nn 8 (2^26); KZRange o 0 (2^26); KZRange nb 0 8;
       KZRange (nn - o) 8 (2^26); KZRange ps 4096 (2^47); KZRange (ps - DST) 0 (2^32); KZRange (p - ps) 0 (2^32);
       KZRange p 4096 (2^47); KZRange (se - p) 0 3; KZRange se 4096 (2^47); KZRange (DST + dcap - se) 0 (2^32);
       KZRange b 0 64; KZRange k 0 3; KZRange sP 8192 (2^47); KZIdx 11 2048]
      [(SS, nn); (DT + 4, 4096)] [(SS, nn); (DT + 4, 4096)] [(SS, nn); (DT + 4, 4096)].
    kx_post_regs. cbn [mem_denot].
    eapply w4l_st; [apply K | ..]; w4l_eq.
Time Qed.

Lemma w4l_j1 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (bs cbs : list byte) (buf : list Z) (gp tp x6 x7 x14 x16 x28 : word)
    (sP DST dcap SS DT dtl nn o nb b k se ps p SBL SBH : Z),
  w4lmem RNG mm sP DST dcap SS DT dtl nn SBL SBH bs cbs buf ->
  0 <= o -> 0 <= nb <= 8 -> o + nb + 8 <= nn -> DST <= ps -> ps <= p -> p + 4 <= se -> se <= DST + dcap -> 0 <= b <= 64 ->
  0 <= k <= 3 ->
  (forall m1 (buf' : list Z) (y6 y7 y9 y12 y13 y14 y16 y28 : word),
     munch [(p, p + 4)] mm m1 -> wmono bsegs mm m1 -> mem_inv bsegs m1 ->
     u8arr bsegs m1 DST (map (Z_to_bv 8) buf') -> length buf' = length buf ->
     evtF bsegs RNG Q (MS (w4ls1534 se sP gp tp ps y6 y7 y9 SS o p y12 y13 y14 k y16 DT y28)
                          F (Z_to_bv 64 AW4_L1534) fc None m1 (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (w4ls1398 se sP gp tp ps x6 x7 b SS o nb p 1 x14 k x16 DT x28)
                       F (Z_to_bv 64 AW4_L1398) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc bs cbs buf gp tp x6 x7 x14 x16 x28 sP DST dcap SS DT dtl nn o nb b k se ps p SBL SBH
    HM HO HNB HON HP1 HP2 HP3 HP4 HB HK K.
  unfold w4lmem in HM. decompose [and] HM. clear HM. unfold AW4_KTB, AW4_KSB.
  kx_runFLd [0x896fc; 0x89480; 0x89930; 0x89880; 0x8992c; 0x894dc] 400%nat (true :: true :: true :: true :: repeat false 60)
      [KZRange DST 4096 (2^47); KZRange dcap 0 (2^32 - 1); KZRange (DST + dcap) 4096 (2^47); KZRange SS 4096 (2^47);
       KZRange (SS + nn) 4096 (2^47); KZRange DT 4096 (2^47); KZRange nn 8 (2^26); KZRange o 0 (2^26); KZRange nb 0 8;
       KZRange (nn - o) 8 (2^26); KZRange ps 4096 (2^47); KZRange (ps - DST) 0 (2^32); KZRange (p - ps) 0 (2^32);
       KZRange p 4096 (2^47); KZRange (se - p) 4 (2^32); KZRange se 4096 (2^47); KZRange (DST + dcap - se) 0 (2^32);
       KZRange b 0 64; KZRange k 0 3; KZRange sP 8192 (2^47); KZIdx 11 2048;
       KZWr p 4; KZDisj p 4 (DT + 4) 4096; KZDisj SS nn p 4]
      [(SS, nn); (DT + 4, 4096)] [(SS, nn); (DT + 4, 4096); (p, 4)] [(SS, nn); (DT + 4, 4096); (p, 4)].
  all: try (lazymatch goal with |- branch_taken BC_GEU (edenot ?E ?D) (edenot ?E (EMd M_MUL (ELit 2) (EAlu ALU_SRL ?X ?Y))) = true =>
         apply (w4l_br_tix E D X Y); w4l_uzm end).
  all: try unfold ASHOFF in *.
  all: try (lazymatch goal with |- flat _ _ _ /\ _ => w4lshd end).
  w4l_post [(p, p + 4)] [(p, 4)] buf.
  lazymatch goal with |- context [mem_denot ?E mm ?l] => set (m1 := mem_denot E mm l) in * end.
  eapply w4l_st; [eapply (K m1 buf') | ..]; first [eassumption | w4l_eq].
Time Qed.

Definition w4lw (a b : word) : word := sext 64 (alu32 ALU_ADD (low32 a) (low32 b)).

Lemma w4l_bt : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (bs cbs : list byte) (buf : list Z) (gp tp x6 x7 x9 x12 x13 x14 x16 x28 : word)
    (sP DST dcap SS DT dtl nn off k se ps p SBL SBH : Z),
  w4lmem RNG mm sP DST dcap SS DT dtl nn SBL SBH bs cbs buf ->
  0 <= off -> off + 8 <= nn -> DST <= ps -> ps <= p -> p + 4 <= se -> se <= DST + dcap -> 0 <= k <= 3 ->
  (bv_unsigned (w4lw x14 x9) <= 64 -> forall m1 (buf' : list Z) (y6 y7 y11 y12 y13 y14 y16 y28 : word),
     munch [(p + 3, p + 4)] mm m1 -> wmono bsegs mm m1 -> mem_inv bsegs m1 ->
     u8arr bsegs m1 DST (map (Z_to_bv 8) buf') -> length buf' = length buf ->
     evtF bsegs RNG Q (MS (w4ls1375 se sP gp tp ps y6 y7 (bv_unsigned (w4lw x14 x9)) SS off y11 y12 y13 y14 k y16 DT (p + 4) y28)
                          F (Z_to_bv 64 AW4_FL) fc None m1 (seg_rom bsegs))) ->
  (64 < bv_unsigned (w4lw x14 x9) -> forall m1 (buf' : list Z) (y6 y7 y8 y9 y10 y11 y12 y13 y14 y16 y19 y22 y27 y28 : word),
     munch [(p + 3, p + 4)] mm m1 -> wmono bsegs mm m1 -> mem_inv bsegs m1 ->
     u8arr bsegs m1 DST (map (Z_to_bv 8) buf') -> length buf' = length buf ->
     evtF bsegs RNG Q (MS (w4lx1674 se sP gp tp ps k DT ps (p + 4 - ps) y6 y7 y8 y9 y10 y11 y12 y13 y14 y16 y19 y22 y27 y28)
                          F (Z_to_bv 64 AW4_L1674) fc None m1 (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (w4ls1534 se sP gp tp ps x6 x7 x9 SS off p x12 x13 x14 k x16 DT x28)
                       F (Z_to_bv 64 AW4_L1534) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc bs cbs buf gp tp x6 x7 x9 x12 x13 x14 x16 x28 sP DST dcap SS DT dtl nn off k se ps p SBL SBH
    HM HO HON HP1 HP2 HP3 HP4 HK KT KF.
  unfold w4lmem in HM. decompose [and] HM. clear HM. unfold AW4_KTB, AW4_KSB.
  destruct (Z_le_gt_dec (bv_unsigned (w4lw x14 x9)) 64) as [HW | HW].
  - kx_runFLd [0x89480; 0x8992c; 0x89930; 0x89880; 0x894dc] 100%nat (true :: repeat false 63)
      [KZRange DST 4096 (2^47); KZRange dcap 0 (2^32 - 1); KZRange (DST + dcap) 4096 (2^47); KZRange SS 4096 (2^47);
       KZRange (SS + nn) 4096 (2^47); KZRange DT 4096 (2^47); KZRange nn 8 (2^26); KZRange off 0 (2^26); KZRange (nn - off) 8 (2^26);
       KZRange ps 4096 (2^47); KZRange (ps - DST) 0 (2^32); KZRange (p - ps) 0 (2^32); KZRange p 4096 (2^47);
       KZRange (se - p) 4 (2^32); KZRange se 4096 (2^47); KZRange (DST + dcap - se) 0 (2^32);
       KZRange k 0 3; KZRange sP 8192 (2^47); KZWr (p + 3) 1]
      (@nil (Z * Z)) [(p + 3, 1)] [(p + 3, 1)].
    all: try (lazymatch goal with |- branch_taken _ _ _ = _ =>
           apply w4l_b64t; w4l_atm; unfold w4lw in HW; exact HW end).
    w4l_post [(p + 3, p + 4)] [(p + 3, 1)] buf.
    lazymatch goal with |- context [mem_denot ?E mm ?l] => set (m1 := mem_denot E mm l) in * end.
    eapply w4l_st; [eapply (KT HW m1 buf') | ..];
      first [eassumption | rewrite Z_to_bv_bv_unsigned; w4l_atm; reflexivity | w4l_eq].
  - apply Z.gt_lt in HW.
    kx_runFLd [0x89480; 0x8992c; 0x89930; 0x89880; 0x894dc] 100%nat (repeat false 64)
      [KZRange DST 4096 (2^47); KZRange dcap 0 (2^32 - 1); KZRange (DST + dcap) 4096 (2^47); KZRange SS 4096 (2^47);
       KZRange (SS + nn) 4096 (2^47); KZRange DT 4096 (2^47); KZRange nn 8 (2^26); KZRange off 0 (2^26); KZRange (nn - off) 8 (2^26);
       KZRange ps 4096 (2^47); KZRange (ps - DST) 0 (2^32); KZRange (p - ps) 0 (2^32); KZRange p 4096 (2^47);
       KZRange (se - p) 4 (2^32); KZRange se 4096 (2^47); KZRange (DST + dcap - se) 0 (2^32);
       KZRange k 0 3; KZRange sP 8192 (2^47); KZWr (p + 3) 1]
      (@nil (Z * Z)) [(p + 3, 1)] [(p + 3, 1)].
    all: try (lazymatch goal with |- branch_taken _ _ _ = _ =>
           apply w4l_b64f; w4l_atm; unfold w4lw in HW; exact HW end).
    w4l_post [(p + 3, p + 4)] [(p + 3, 1)] buf.
    lazymatch goal with |- context [mem_denot ?E mm ?l] => set (m1 := mem_denot E mm l) in * end.
    eapply w4l_st; [eapply (KF HW m1 buf') | ..]; first [eassumption | w4l_eq].
Time Qed.
Section W4FIN.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte) (pdt pb : aptr) (SBL SBH : Z) (rstk : region).
  Notation SP := (bv_unsigned sp).
  Notation SPF := (SP + -480).
  Notation n := (zlen src).
  Notation seg := ((dcap + 3) / 4).
  Notation DTL := (DTABLE_BYTES mtl).
  Hypothesis AH : AHEAP AI L RNG st LB m0.
  Hypothesis MTL : 1 <= mtl <= 12.
  Hypothesis TL11 : tl = 11.
  Hypothesis TLM : tl <= mtl + 1.
  Hypothesis HDT : In (HB pdt DT DTL) LB.
  Hypothesis LCB : zlen cbs = 2 * 2^tl.
  Hypothesis HDB : In (HB pb DST dcap) LB.
  Hypothesis DC : 0 <= dcap < 2^32.
  Hypothesis NSM : n < 2^26.
  Hypothesis S16 : 16 <= SS.
  Hypothesis SRCB : 0 < n -> exists p, In (HB p SBL (SBH - SBL)) LB /\ SBL <= SS /\ SS + n <= SBH.
  Hypothesis DJ1 : KXGoM.apart DT DTL SS n.
  Hypothesis DJ2 : KXGoM.apart DST dcap SS n.
  Hypothesis DJ3 : KXGoM.apart DST dcap DT DTL.
  Hypothesis LOA : ATOP + 4096 <= lo.
  Hypothesis LOS : lo <= SP - HUF_DEC_STACK_A.
  Hypothesis SPT : SP + 16 < al_top L.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis RCL : rclean m0 rstk.
  Hypothesis RLO : r_lo rstk <= lo.
  Hypothesis RHI : SP <= r_hi rstk.
  Hypothesis RRL : ATOP <= r_rlo rstk.
  Hypothesis RRS : rrng RNG rstk.
  Hypothesis WSK : rng RNG lo (al_top L - lo).
  Hypothesis WIM : rng_aimg RNG.

  Notation DW := [(lo, SP); (DST, DST + dcap)].
  Notation POST := (huf_dec_postA AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB DST dcap lo m0).
  Notation W4FX := (W4F ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs).
  Notation FRS := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Definition W4KFL (k : nat) (se ps : Z) (fr mid l256 l296 l336 : list cell) : Prop :=
    forall (mm : amem) (p off bc : Z) (x6 x7 x11 x12 x13 x14 x16 x28 : word),
    W4FX mm fr mid l256 l296 l336 -> (k <= 3)%nat -> DST <= ps <= p -> p <= se <= DST + dcap ->
    0 <= off -> off + 8 <= n -> 0 <= bc <= 64 ->
    evtF bsegs RNG POST
      (MS (mkR (Z_to_bv 64 se) (Z_to_bv 64 SPF) gp tp (Z_to_bv 64 ps) x6 x7
               (Z_to_bv 64 (SS + 8)) (Z_to_bv 64 bc) (Z_to_bv 64 (SS + off)) x11 x12 x13 x14
               (Z_to_bv 64 (Z.of_nat k)) x16 (Z_to_bv 64 (2^64 - DT - 5)) (Z_to_bv 64 (se - ps))
               (Z_to_bv 64 SS) (Z_to_bv 64 se) (Z_to_bv 64 (SP + -344 + 8 * Z.of_nat k)) (Z_to_bv 64 p) (Z_to_bv 64 (DT + 4))
               (Z_to_bv 64 AW4_KSB) (Z_to_bv 64 (p - ps)) (Z_to_bv 64 AW4_KTB) (Z_to_bv 64 (se - 3))
               x28 (Z_to_bv 64 2) (Z_to_bv 64 (-1)) (Z_to_bv 64 64))
          FR (Z_to_bv 64 AW4_FL) fc None mm (seg_rom bsegs)).
  Lemma w4f_dtl : 4 + 4096 <= DTL.
  Proof.
    unfold DTABLE_BYTES, HufHarness.DT_BYTES.
    assert (2^10 <= 2^mtl) by (apply Z.pow_le_mono_r; lia). lia.
  Qed.
  Ltac w4dj := cbn [disjoint_from]; split; [| exact I]; rewrite ?length_map; simpl length; lia.
  Lemma w4f_wr : forall mm m1 fr mid l256 l296 l336 a len (buf' : list Z),
    W4FX mm fr mid l256 l296 l336 -> DST <= a -> a + len <= DST + dcap ->
    munch [(a, a + len)] mm m1 -> wmono bsegs mm m1 -> mem_inv bsegs m1 ->
    u8arr bsegs m1 DST (map (Z_to_bv 8) buf') -> zlen buf' = dcap ->
    W4FX m1 fr mid l256 l296 l336.
  Proof.
    intros mm m1 fr mid l256 l296 l336 a len buf' HW HA1 HA2 MUa WMa MI1 OUT1 LB1.
    destruct HW as ((buf & OUT & LB0) & SRC & TAB & HDR & STK & RW1 & CS1 & RW2 & CS2 & RW3 & CS3 & RW4 & CS4
                    & RW5 & CS5 & RWF & MI & MU & WM).
    pose proof (w4_sp_bounds AI L RNG st LB sp m0 lo AH LOA LOS SPT) as (_ & SB1 & SB2 & SB3).
    pose proof (hb_unpoisoned AI _ _ _ _ _ _ _ _ AH HDT) as (_ & _ & _ & TBK & TT & _).
    pose proof (hb_unpoisoned AI _ _ _ _ _ _ _ _ AH HDB) as (_ & _ & _ & DBK & DTT & _).
    pose proof w4f_dtl as DTb.
    assert (LCB' : Z.of_nat (length cbs) = 4096) by (rewrite LCB, TL11; reflexivity).
    unfold KXGoM.apart in DJ1, DJ2, DJ3.
    split; [exists buf'; split; assumption |].
    split; [apply (bytes_at_transport bsegs _ mm m1 _ _ SRC MUa); w4dj |].
    split; [apply (bytes_at_transport bsegs _ mm m1 _ _ TAB MUa); w4dj |].
    split; [apply (bytes_at_transport bsegs _ mm m1 _ _ HDR MUa); w4dj |].
    split; [apply (stk_transport_disjoint bsegs _ mm m1 _ _ STK MUa WMa); w4dj |].
    split; [apply (rw_cells_transport bsegs _ mm m1 _ _ RW1 MUa WMa); rewrite CS1; w4dj | split; [exact CS1 |]].
    split; [apply (rw_cells_transport bsegs _ mm m1 _ _ RW2 MUa WMa); rewrite CS2; w4dj | split; [exact CS2 |]].
    split; [apply (rw_cells_transport bsegs _ mm m1 _ _ RW3 MUa WMa); rewrite CS3; w4dj | split; [exact CS3 |]].
    split; [apply (rw_cells_transport bsegs _ mm m1 _ _ RW4 MUa WMa); rewrite CS4; w4dj | split; [exact CS4 |]].
    split; [apply (rw_cells_transport bsegs _ mm m1 _ _ RW5 MUa WMa); rewrite CS5; w4dj | split; [exact CS5 |]].
    split; [apply (rw_cells_transport bsegs _ mm m1 _ _ RWF MUa WMa); cbn [cells_size csize]; w4dj |].
    split; [exact MI1 |].
    split.
    - apply (munch_trans _ m0 mm m1 MU). apply (munch_weaken [(a, a + len)] _ mm m1); [| exact MUa].
      intros x Hx; cbn [outside] in *. destruct Hx as (H1 & H2 & _). split; [lia | exact I].
    - exact (wmono_trans bsegs m0 mm m1 WM WMa).
  Qed.
  Lemma w4f_unp : forall mm fr mid l256 l296 l336, W4FX mm fr mid l256 l296 l336 -> 0 < n ->
    (unpoisoned mm SBL SBH /\ rng RNG (shad SBL) (shlen (SBH - SBL + 7)) /\ SBL mod 8 = 0 /\ 0 <= SBL
       /\ rng RNG SBL (SBH - SBL) /\ SBL <= SS /\ SS + n <= SBH /\ ablk SBL SBH)
    /\ (unpoisoned mm DT (DT + DTL) /\ rng RNG (shad DT) (shlen (DTL + 7)) /\ DT mod 8 = 0 /\ 0 <= DT
       /\ rng RNG DT DTL /\ ablk DT (DT + DTL) /\ DT + 4 + 4096 <= DT + DTL)
    /\ (unpoisoned mm DST (DST + dcap) /\ rng RNG (shad DST) (shlen (dcap + 7)) /\ DST mod 8 = 0 /\ 0 <= DST
       /\ rng RNG DST dcap /\ ablk DST (DST + dcap))
    /\ rng RNG SPF 480 /\ KXGoM.apart SS n SPF 480 /\ KXGoM.apart DT DTL SPF 480 /\ KXGoM.apart DST dcap SPF 480
    /\ AIMG_HI <= SBL /\ SBH <= ATOP /\ AIMG_HI <= DT /\ DT + DTL <= ATOP /\ AIMG_HI <= DST /\ DST + dcap <= ATOP
    /\ ATOP + 4096 <= lo /\ lo + 8192 <= SP /\ SP <= 2^47 /\ ATOP <= ATOP_MAX.
  Proof.
    intros mm fr mid l256 l296 l336 HW HN.
    destruct HW as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MU & WM).
    assert (AHm : AHEAP AI L RNG st LB mm) by (eapply w4_aheap; eassumption).
    pose proof (w4_sp_bounds AI L RNG st LB sp m0 lo AH LOA LOS SPT) as (_ & SB1 & SB2 & SB3).
    destruct (SRCB HN) as (psb & HSB & SB4 & SB5).
    pose proof (hb_unpoisoned AI _ _ _ _ _ _ _ _ AHm HSB) as (US & S16' & S1 & SBK & ST & SR & SS1 & _).
    pose proof (hb_unpoisoned AI _ _ _ _ _ _ _ _ AHm HDT) as (UT & T16 & T1 & TBK & TT & TR & TS & _).
    pose proof (hb_unpoisoned AI _ _ _ _ _ _ _ _ AHm HDB) as (UD & D16 & D1 & DBK & DTT & DR & DS & _).
    pose proof (ablk_lin _ _ SBK) as (A1 & A2 & A3 & A4).
    pose proof (ablk_lin _ _ TBK) as (B1 & B2 & B3 & B4).
    pose proof (ablk_lin _ _ DBK) as (C1 & C2 & C3 & C4).
    replace (SBL + (SBH - SBL)) with SBH in US, SBK, A3, A4 by lia.
    pose proof (@ATOP_range rc) as AR.
    pose proof w4f_dtl as DTb.
    assert (RS : rng RNG SPF 480) by (apply (rng_sub RNG lo (al_top L - lo)); [exact WSK | lia | lia]).
    unfold KXGoM.apart.
    repeat match goal with |- _ /\ _ => split end; first [assumption | lia | Z.div_mod_to_equations; lia].
  Qed.

  Definition AW4_ST64 : Z := 151050438420815295.
  Definition w4fr (w0 w8 w16 w24 w32 : word) : list cell :=
    [C8 w0; C8 w8; C8 w16; C8 w24; C8 w32; C8 (Z_to_bv 64 SS); C8 (Z_to_bv 64 DT); C8 (Z_to_bv 64 n);
     C8 (Z_to_bv 64 AW4_ST64); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + dcap)); C8 (Z_to_bv 64 seg)].
  Definition w4sel (k : nat) (fw vw : list word) : list word := firstn k fw ++ skipn k vw.
  Definition w4mid (k : nat) (a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew : word)
      (i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 : Z) (c0 c1 c2 c3 : word) : list cell :=
    map C8 (w4sel k [a0; a1; a2; a3] [Z_to_bv 64 (SS + i0); Z_to_bv 64 (SS + i1); Z_to_bv 64 (SS + i2); Z_to_bv 64 (SS + i3)]
            ++ w4sel k [p0; p1; p2; p3] [Z_to_bv 64 (DST + o0); Z_to_bv 64 (DST + o1); Z_to_bv 64 (DST + o2); Z_to_bv 64 (DST + o3)]
            ++ w4sel k [b0; b1; b2; b3] [c0; c1; c2; c3]
            ++ [adt; Z_to_bv 64 SS; oew]
            ++ w4sel k [q0; q1; q2; q3] [Z_to_bv 64 (SS + e0); Z_to_bv 64 (SS + e1); Z_to_bv 64 (SS + e2); Z_to_bv 64 (SS + e3)]).
  Definition w4sr1 (i o e : Z) (c : word) : Prop := 0 <= i /\ i + 8 <= n /\ 0 <= o <= dcap /\ 1 <= bv_unsigned c /\ 6 <= e <= n.
  Definition W4SR (i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 : Z) (c0 c1 c2 c3 : word) : Prop :=
    DST + 3 * seg < DST + dcap /\ 9 <= n /\
    w4sr1 i0 o0 e0 c0 /\ w4sr1 i1 o1 e1 c1 /\ w4sr1 i2 o2 e2 c2 /\ w4sr1 i3 o3 e3 c3.
  Definition W4KF3 (k : nat) (i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 : Z) (c0 c1 c2 c3 : word) : Prop :=
    forall (mm : amem) (w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew : word)
           (l256 l296 l336 : list cell)
           (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x18 x19 x21 x22 x25 x27 x28 : word),
    W4FX mm (w4fr w0 w8 w16 w24 w32)
         (w4mid k a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3)
         l256 l296 l336 ->
    W4SR i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> (k <= 3)%nat ->
    evtF bsegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 (Z_to_bv 64 (Z.of_nat k)) (Z_to_bv 64 9)
               (Z_to_bv 64 (2^64 - DT - 5)) x18 x19 (Z_to_bv 64 (DST + Z.of_nat k * seg)) x21 x22 (Z_to_bv 64 (DT + 4))
               (Z_to_bv 64 AW4_KSB) x25 (Z_to_bv 64 AW4_KTB) x27 x28 (Z_to_bv 64 2) (Z_to_bv 64 (-1)) (Z_to_bv 64 64))
          FR (Z_to_bv 64 AW4_F3) fc None mm (seg_rom bsegs)).
  Definition W4KERR : Prop :=
    forall (mm : amem) (fr mid l256 l296 l336 : list cell)
           (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    W4FX mm fr mid l256 l296 l336 ->
    evtF bsegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31)
          FR (Z_to_bv 64 AW4_FERR) fc None mm (seg_rom bsegs)).
  Definition W4KFX2 : Prop :=
    forall (mm : amem) (w0 w8 w16 w24 w32 : word) (mid l256 l296 l336 : list cell)
           (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    W4FX mm (w4fr w0 w8 w16 w24 w32) mid l256 l296 l336 -> 0 < dcap ->
    evtF bsegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31)
          FR (Z_to_bv 64 AW4_FX2) fc None mm (seg_rom bsegs)).
  Definition AW4_X1631 : Z := 563328.
  Definition AW4_X1674 : Z := 563500.
  Definition AW4_X1675 : Z := 563504.
  Definition w4se (k : nat) : Z := if (k <? 3)%nat then DST + (Z.of_nat k + 1) * seg else DST + dcap.
  Definition w4nth (k : nat) (z0 z1 z2 z3 : Z) : Z := nth k [z0; z1; z2; z3] 0.
  Definition W4TM (k : nat) (i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 : Z) (c0 c1 c2 c3 : word) (mm : amem) : Prop :=
    exists (w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew : word) (l256 l296 l336 : list cell),
      W4FX mm (w4fr w0 w8 w16 w24 w32)
        (w4mid k a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3)
        l256 l296 l336.
  Definition W4KFE (k : nat) (i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 : Z) (c0 c1 c2 c3 : word) : Prop :=
    forall (mm : amem) (bc : Z) (x6 x7 x11 x12 x13 x14 x16 x22 x25 x27 x28 : word),
    W4TM k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 mm ->
    W4SR i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> (k <= 3)%nat -> 0 <= bc <= 64 ->
    DST + w4nth k o0 o1 o2 o3 <= w4se k ->
    evtF bsegs RNG POST
      (MS (mkR (Z_to_bv 64 (w4se k)) (Z_to_bv 64 SPF) gp tp (Z_to_bv 64 (DST + w4nth k o0 o1 o2 o3)) x6 x7
               (Z_to_bv 64 (SS + 8)) (Z_to_bv 64 bc) (Z_to_bv 64 (SS + w4nth k i0 i1 i2 i3)) x11 x12 x13 x14
               (Z_to_bv 64 (Z.of_nat k)) x16 (Z_to_bv 64 (2^64 - DT - 5)) (Z_to_bv 64 (w4se k - (DST + w4nth k o0 o1 o2 o3)))
               (Z_to_bv 64 SS) (Z_to_bv 64 (w4se k)) (Z_to_bv 64 (SP + -344 + 8 * Z.of_nat k)) x22 (Z_to_bv 64 (DT + 4))
               (Z_to_bv 64 AW4_KSB) x25 (Z_to_bv 64 AW4_KTB) x27 x28 (Z_to_bv 64 2) (Z_to_bv 64 (-1)) (Z_to_bv 64 64))
          FR (Z_to_bv 64 AW4_FE) fc None mm (seg_rom bsegs)).
  Definition W4K1631 (k : nat) (i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 : Z) (c0 c1 c2 c3 : word) : Prop :=
    forall (mm : amem) (op : Z) (x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x16 x19 x25 x27 x28 : word),
    W4TM k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 mm ->
    W4SR i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> (k <= 3)%nat -> DST <= op <= w4se k ->
    DST + w4nth k o0 o1 o2 o3 <= w4se k ->
    evtF bsegs RNG POST
      (MS (mkR (Z_to_bv 64 (w4se k)) (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14
               (Z_to_bv 64 (Z.of_nat k)) x16 (Z_to_bv 64 (2^64 - DT - 5)) (Z_to_bv 64 (w4se k - (DST + w4nth k o0 o1 o2 o3)))
               x19 (Z_to_bv 64 (w4se k)) (Z_to_bv 64 (SP + -344 + 8 * Z.of_nat k)) (Z_to_bv 64 op) (Z_to_bv 64 (DT + 4))
               (Z_to_bv 64 AW4_KSB) x25 (Z_to_bv 64 AW4_KTB) x27 x28 (Z_to_bv 64 2) (Z_to_bv 64 (-1)) (Z_to_bv 64 64))
          FR (Z_to_bv 64 AW4_X1631) fc None mm (seg_rom bsegs)).
  Definition W4K1675 (k : nat) (i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 : Z) (c0 c1 c2 c3 : word) : Prop :=
    forall (mm : amem) (op : Z) (x5 x6 x7 x8 x9 x10 x12 x13 x14 x16 x19 x22 x25 x27 x28 : word),
    W4TM k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 mm ->
    W4SR i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> (k <= 3)%nat -> DST <= op <= w4se k ->
    DST + w4nth k o0 o1 o2 o3 <= w4se k ->
    evtF bsegs RNG POST
      (MS (mkR (Z_to_bv 64 (w4se k)) (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 op) x12 x13 x14
               (Z_to_bv 64 (Z.of_nat k)) x16 (Z_to_bv 64 (2^64 - DT - 5)) (Z_to_bv 64 (w4se k - (DST + w4nth k o0 o1 o2 o3)))
               x19 (Z_to_bv 64 (w4se k)) (Z_to_bv 64 (SP + -344 + 8 * Z.of_nat k)) x22 (Z_to_bv 64 (DT + 4))
               (Z_to_bv 64 AW4_KSB) x25 (Z_to_bv 64 AW4_KTB) x27 x28 (Z_to_bv 64 2) (Z_to_bv 64 (-1)) (Z_to_bv 64 64))
          FR (Z_to_bv 64 AW4_X1675) fc None mm (seg_rom bsegs)).
  Definition W4K1674 (k : nat) (i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 : Z) (c0 c1 c2 c3 : word) : Prop :=
    forall (mm : amem) (u v : Z) (x6 x7 x8 x9 x10 x11 x12 x13 x14 x16 x19 x22 x27 x28 : word),
    W4TM k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 mm ->
    W4SR i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> (k <= 3)%nat -> DST <= u + v <= w4se k ->
    DST + w4nth k o0 o1 o2 o3 <= w4se k ->
    evtF bsegs RNG POST
      (MS (mkR (Z_to_bv 64 (w4se k)) (Z_to_bv 64 SPF) gp tp (Z_to_bv 64 u) x6 x7 x8 x9 x10 x11 x12 x13 x14
               (Z_to_bv 64 (Z.of_nat k)) x16 (Z_to_bv 64 (2^64 - DT - 5)) (Z_to_bv 64 (w4se k - (DST + w4nth k o0 o1 o2 o3)))
               x19 (Z_to_bv 64 (w4se k)) (Z_to_bv 64 (SP + -344 + 8 * Z.of_nat k)) x22 (Z_to_bv 64 (DT + 4))
               (Z_to_bv 64 AW4_KSB) (Z_to_bv 64 v) (Z_to_bv 64 AW4_KTB) x27 x28 (Z_to_bv 64 2) (Z_to_bv 64 (-1)) (Z_to_bv 64 64))
          FR (Z_to_bv 64 AW4_X1674) fc None mm (seg_rom bsegs)).
  Definition W4KFT (k : nat) (i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 : Z) (c0 c1 c2 c3 : word) : Prop :=
    forall (mm : amem) (op : Z) (x1 x6 x7 x8 x9 x11 x12 x14 x16 x19 x22 x25 x27 x28 : word),
    W4TM k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 mm ->
    W4SR i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> (k <= 3)%nat -> DST <= op < w4se k ->
    DST + w4nth k o0 o1 o2 o3 <= w4se k ->
    evtF bsegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp (Z_to_bv 64 op) x6 x7 x8 x9 (Z_to_bv 64 op) x11 x12 (Z_to_bv 64 (w4se k - op)) x14
               (Z_to_bv 64 (Z.of_nat k)) x16 (Z_to_bv 64 (2^64 - DT - 5)) (Z_to_bv 64 (w4se k - (DST + w4nth k o0 o1 o2 o3)))
               x19 (Z_to_bv 64 (w4se k)) (Z_to_bv 64 (SP + -344 + 8 * Z.of_nat k)) x22 (Z_to_bv 64 (DT + 4))
               (Z_to_bv 64 AW4_KSB) x25 (Z_to_bv 64 AW4_KTB) x27 x28 (Z_to_bv 64 2) (Z_to_bv 64 (-1)) (Z_to_bv 64 64))
          FR (Z_to_bv 64 AW4_FT) fc None mm (seg_rom bsegs)).
  Definition W4KFEND (k : nat) (i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 : Z) (c0 c1 c2 c3 : word) : Prop :=
    forall (mm : amem) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x16 x19 x22 x25 x27 x28 : word),
    W4TM k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 mm ->
    W4SR i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> (k <= 3)%nat ->
    DST + w4nth k o0 o1 o2 o3 <= w4se k ->
    evtF bsegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14
               (Z_to_bv 64 (Z.of_nat k)) x16 (Z_to_bv 64 (2^64 - DT - 5)) (Z_to_bv 64 (w4se k - (DST + w4nth k o0 o1 o2 o3)))
               x19 (Z_to_bv 64 (w4se k)) (Z_to_bv 64 (SP + -344 + 8 * Z.of_nat k)) x22 (Z_to_bv 64 (DT + 4))
               (Z_to_bv 64 AW4_KSB) x25 (Z_to_bv 64 AW4_KTB) x27 x28 (Z_to_bv 64 2) (Z_to_bv 64 (-1)) (Z_to_bv 64 64))
          FR (Z_to_bv 64 AW4_FEND) fc None mm (seg_rom bsegs)).

  
  Lemma w4l_mem : forall mm fr mid l256 l296 l336, W4FX mm fr mid l256 l296 l336 -> 9 <= n ->
    exists buf, zlen buf = dcap /\ w4lmem RNG mm SP DST dcap SS DT DTL n SBL SBH (map (Z_to_bv 8) src) cbs buf.
  Proof.
    intros mm fr mid l256 l296 l336 HW HN.
    pose proof (w4f_unp mm fr mid l256 l296 l336 HW ltac:(lia)) as U.
    destruct HW as ((buf & OUT & LBF) & SRC & TAB & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI & _ & _).
    exists buf. split; [exact LBF |]. unfold w4lmem.
    pose proof (@ATOP_range rc) as AR.
    assert (LCB' : Z.of_nat (length cbs) = 4096) by (rewrite LCB, TL11; reflexivity).
    rewrite length_map.
    decompose [and] U. clear U.
    clear AH HDT HDB SRCB.
    repeat match goal with H : ablk _ _ |- _ => unfold ablk in H; destruct H as [[? ?] | [? ?]] end.
    all: unfold KXGoM.apart in *; unfold AIMG_HI, ATOP_MIN, ATOP_MAX, ASHOFF, KLS in *.
    all: repeat match goal with |- _ /\ _ => split end; first [assumption | lia].
  Qed.

  Section W4LOOP.
  Variables (k : nat) (i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 : Z) (c0 c1 c2 c3 : word)
    (w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew : word) (l256 l296 l336 : list cell).
  Hypothesis HSR : W4SR i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3.
  Hypothesis HK3 : (k <= 3)%nat.
  Hypothesis X1631 : W4K1631 k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3.
  Hypothesis X1674 : W4K1674 k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3.
  Hypothesis X1675 : W4K1675 k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3.
  Notation W4LSE := (w4se k).
  Notation W4LPS := (DST + w4nth k o0 o1 o2 o3).
  Notation W4LW mm := (W4FX mm (w4fr w0 w8 w16 w24 w32)
      (w4mid k a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3)
      l256 l296 l336).
  Notation W4LS1375 mm p off bc x6 x7 x11 x12 x13 x14 x16 x28 :=
    (evtF bsegs RNG POST (MS (w4ls1375 W4LSE SP gp tp W4LPS x6 x7 bc SS off x11 x12 x13 x14 (Z.of_nat k) x16 DT p x28)
                            FR (Z_to_bv 64 AW4_FL) fc None mm (seg_rom bsegs))).

  Definition W4LR (p : Z) : Prop :=
    forall mm off bc (y6 y7 y11 y12 y13 y14 y16 y28 : word),
    W4LW mm -> p + 4 <= W4LSE -> 0 <= off -> off + 8 <= n -> 0 <= bc <= 64 ->
    W4LS1375 mm (p + 4) off bc y6 y7 y11 y12 y13 y14 y16 y28.

  
  Lemma w4l_tm : forall mm, W4LW mm -> W4TM k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 mm.
  Proof.
    intros mm HW. exists w0, w8, w16, w24, w32, a0, a1, a2, a3, p0, p1, p2, p3, b0, b1, b2, b3, q0, q1, q2, q3, adt, oew,
      l256, l296, l336. exact HW.
  Qed.

  
  Lemma w4l_n9 : 9 <= n.
  Proof. exact (proj1 (proj2 HSR)). Qed.

  
  Lemma w4l_B : forall mm p off (x6 x7 x9 x12 x13 x14 x16 x28 : word),
    W4LR p -> W4LW mm -> DST <= W4LPS <= p -> p + 4 <= W4LSE -> W4LSE <= DST + dcap -> 0 <= off -> off + 8 <= n ->
    evtF bsegs RNG POST (MS (w4ls1534 W4LSE SP gp tp W4LPS x6 x7 x9 SS off p x12 x13 x14 (Z.of_nat k) x16 DT x28)
                            FR (Z_to_bv 64 AW4_L1534) fc None mm (seg_rom bsegs)).
  Proof.
    intros mm p off x6 x7 x9 x12 x13 x14 x16 x28 R HW HB1 HB2 HB3 HO HON.
    destruct (w4l_mem mm _ _ _ _ _ HW w4l_n9) as (buf & LB0 & HM).
    eapply w4l_bt; [exact HM | lia .. | |].
    - intros HW1 m1 buf' y6 y7 y11 y12 y13 y14 y16 y28 MU WM MI OUT LB1.
      replace (p + 4) with (p + 3 + 1) in MU by lia.
      pose proof (w4f_wr mm m1 _ _ _ _ _ (p + 3) 1 buf' HW ltac:(lia) ltac:(lia) MU WM MI OUT ltac:(lia)) as HW'.
      unfold W4LR in R.
      pose proof (bv_unsigned_in_range _ (w4lw x14 x9)) as [RW _].
      apply (R m1 off (bv_unsigned (w4lw x14 x9)) y6 y7 y11 y12 y13 y14 y16 y28 HW' HB2 HO HON); lia.
    - intros HW1 m1 buf' y6 y7 y8 y9 y10 y11 y12 y13 y14 y16 y19 y22 y27 y28 MU WM MI OUT LB1.
      replace (p + 4) with (p + 3 + 1) in MU by lia.
      pose proof (w4f_wr mm m1 _ _ _ _ _ (p + 3) 1 buf' HW ltac:(lia) ltac:(lia) MU WM MI OUT ltac:(lia)) as HW'.
      exact (X1674 m1 W4LPS (p + 4 - W4LPS) y6 y7 y8 y9 y10 y11 y12 y13 y14 y16 y19 y22 y27 y28 (w4l_tm m1 HW') HSR HK3
               ltac:(lia) ltac:(lia)).
  Qed.

  
  Lemma w4l_J : forall mm p o nb b st0 (x6 x7 x14 x16 x28 : word),
    W4LR p -> W4LW mm -> DST <= W4LPS <= p -> p <= W4LSE <= DST + dcap ->
    0 <= o -> 0 <= nb <= 8 -> o + nb + 8 <= n -> 0 <= b <= 64 -> (st0 = 0 \/ st0 = 1) ->
    evtF bsegs RNG POST (MS (w4ls1398 W4LSE SP gp tp W4LPS x6 x7 b SS o nb p st0 x14 (Z.of_nat k) x16 DT x28)
                            FR (Z_to_bv 64 AW4_L1398) fc None mm (seg_rom bsegs)).
  Proof.
    intros mm p o nb b st0 x6 x7 x14 x16 x28 R HW HB1 HB2 HO HNB HON HB HST.
    destruct (w4l_mem mm _ _ _ _ _ HW w4l_n9) as (buf & LB0 & HM).
    destruct (Z_lt_le_dec W4LSE (p + 4)) as [HE | HE].
    - eapply w4l_j0; [exact HM | lia .. | ].
      intros y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y16 y19 y25 y27 y28.
      exact (X1631 mm p y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y16 y19 y25 y27 y28 (w4l_tm mm HW) HSR HK3
               ltac:(lia) ltac:(lia)).
    - destruct HST as [HST | HST]; subst st0.
      + eapply w4l_j0; [exact HM | lia .. | ].
        intros y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y16 y19 y25 y27 y28.
        exact (X1631 mm p y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y16 y19 y25 y27 y28 (w4l_tm mm HW) HSR HK3
                 ltac:(lia) ltac:(lia)).
      + eapply w4l_j1; [exact HM | lia .. | ].
        intros m1 buf' y6 y7 y9 y12 y13 y14 y16 y28 MU WM MI OUT LB1.
        pose proof (w4f_wr mm m1 _ _ _ _ _ p 4 buf' HW ltac:(lia) ltac:(lia) MU WM MI OUT ltac:(lia)) as HW'.
        apply (w4l_B m1 p o y6 y7 y9 y12 y13 y14 y16 y28 R HW'); lia.
  Qed.

  
  Lemma w4l_step : forall mm p off bc (x6 x7 x11 x12 x13 x14 x16 x28 : word),
    W4LR p -> W4LW mm -> DST <= W4LPS <= p -> p <= W4LSE <= DST + dcap -> 0 <= off -> off + 8 <= n -> 0 <= bc <= 64 ->
    W4LS1375 mm p off bc x6 x7 x11 x12 x13 x14 x16 x28.
  Proof.
    intros mm p off bc x6 x7 x11 x12 x13 x14 x16 x28 R HW HB1 HB2 HO HON HB.
    destruct (w4l_mem mm _ _ _ _ _ HW w4l_n9) as (buf & LB0 & HM).
    destruct (Z.eq_dec off 0) as [E0 | E0].
    - eapply w4l_r0; [exact HM | lia .. | ].
      intros y5 y6 y7 y8 y9 y10 y12 y13 y14 y16 y19 y22 y25 y27 y28.
      exact (X1675 mm p y5 y6 y7 y8 y9 y10 y12 y13 y14 y16 y19 y22 y25 y27 y28 (w4l_tm mm HW) HSR HK3
               ltac:(lia) ltac:(lia)).
    - destruct (Z_le_gt_dec 8 off) as [E8 | E8].
      + eapply w4l_rf; [exact HM | lia .. | ].
        eapply w4l_J; [exact R | exact HW | lia .. ].
      + destruct (Z_le_gt_dec bc (8 * off + 7)) as [EB | EB].
        * eapply w4l_rcu; [exact HM | lia .. | ].
          intros y14 y16. eapply w4l_J; [exact R | exact HW | lia .. ].
        * eapply w4l_rce; [exact HM | lia .. | ].
          intros y14 y16. eapply w4l_J; [exact R | exact HW | lia .. ].
  Qed.

  
  Lemma w4l_ind : forall (d : nat) mm p off bc (x6 x7 x11 x12 x13 x14 x16 x28 : word),
    (Z.to_nat (W4LSE - p) <= d)%nat -> W4LW mm -> DST <= W4LPS <= p -> p <= W4LSE <= DST + dcap ->
    0 <= off -> off + 8 <= n -> 0 <= bc <= 64 ->
    W4LS1375 mm p off bc x6 x7 x11 x12 x13 x14 x16 x28.
  Proof.
    induction d as [|d IH]; intros mm p off bc x6 x7 x11 x12 x13 x14 x16 x28 HD HW HB1 HB2 HO HON HB;
      apply (w4l_step mm p off bc x6 x7 x11 x12 x13 x14 x16 x28); try assumption;
      intros mm' off' bc' y6 y7 y11 y12 y13 y14 y16 y28 HW' HP4 HO' HON' HB'.
    - exfalso. lia.
    - apply IH; try assumption; lia.
  Qed.
  End W4LOOP.

  
  Lemma w4f_loop : forall (k : nat) (i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 : Z) (c0 c1 c2 c3 : word)
      (w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew : word) (l256 l296 l336 : list cell),
    W4SR i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> (k <= 3)%nat -> W4K1631 k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> W4K1674 k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> W4K1675 k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 ->
    W4KFL k (w4se k) (DST + w4nth k o0 o1 o2 o3) (w4fr w0 w8 w16 w24 w32)
      (w4mid k a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3 q0 q1 q2 q3 adt oew i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3) l256 l296 l336.
  Proof.
    intros k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 w0 w8 w16 w24 w32 a0 a1 a2 a3 p0 p1 p2 p3 b0 b1 b2 b3
      q0 q1 q2 q3 adt oew l256 l296 l336 HSR HK K1 K2 K3.
    unfold W4KFL. intros mm p off bc x6 x7 x11 x12 x13 x14 x16 x28 HW _ HB1 HB2 HO HON HB.
    eapply w4l_ind with (d := Z.to_nat (w4se k - p)); try eassumption; lia.
  Qed.

  
  Lemma w4f_st : forall (Q : machine_state -> Prop) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word) (F : bvmap 5 word) (pc : word) (m : amem) rom,
    evtF bsegs RNG Q (MS (mkR y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31) F pc fc None m rom) -> x1 = y1 -> x2 = y2 -> x3 = y3 -> x4 = y4 -> x5 = y5 -> x6 = y6 -> x7 = y7 -> x8 = y8 -> x9 = y9 -> x10 = y10 -> x11 = y11 -> x12 = y12 -> x13 = y13 -> x14 = y14 -> x15 = y15 -> x16 = y16 -> x17 = y17 -> x18 = y18 -> x19 = y19 -> x20 = y20 -> x21 = y21 -> x22 = y22 -> x23 = y23 -> x24 = y24 -> x25 = y25 -> x26 = y26 -> x27 = y27 -> x28 = y28 -> x29 = y29 -> x30 = y30 -> x31 = y31 ->
    evtF bsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F pc fc None m rom).
  Proof. intros; subst; assumption. Qed.

  
  Lemma w4f_zeq : forall a b q, a = b + q * 2^64 -> Z_to_bv 64 a = Z_to_bv 64 b.
  Proof.
    intros a b q E. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. subst a.
    change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_add; [reflexivity | lia].
  Time Qed.

  Ltac w4f_eq :=
    first [ reflexivity | f_equal; lia
          | apply (w4f_zeq _ _ 0); lia | apply (w4f_zeq _ _ 1); lia | apply (w4f_zeq _ _ (-1)); lia ].

  Ltac w4f_k K :=
    eapply w4f_st; [eapply K | ..];
    try (lazymatch goal with |- @eq _ _ _ => w4f_eq end); try eassumption; try lia.

  
  Lemma w4f_x17 : Z_to_bv 64 (2^64 - DT - 5) = Z_to_bv 64 (- DT - 5).
  Proof. apply (w4f_zeq _ _ 1); lia. Qed.

  
  Lemma w4f_se : forall k, (k <= 3)%nat -> DST + 3 * seg < DST + dcap ->
    DST + seg <= w4se k <= DST + dcap /\ ((k < 3)%nat -> w4se k = DST + (Z.of_nat k + 1) * seg) /\ (k = 3%nat -> w4se k = DST + dcap).
  Proof.
    intros k HK H3. pose proof DC.
    destruct k as [|[|[|[|k]]]]; cbn [w4se Nat.ltb Nat.leb Z.of_nat]; [| | | | lia]; repeat split; intros; try lia.
  Time Qed.

  Lemma w4f_db : 4096 <= DST /\ DST + dcap <= ATOP /\ ATOP + 4096 <= lo /\ lo + 8192 <= SP /\ SP <= 2^47.
  Proof.
    destruct (hb_unpoisoned AI L RNG st LB m0 pb DST dcap AH HDB) as (_ & _ & _ & ABK & TOP & _).
    destruct (w4_sp_bounds AI L RNG st LB sp m0 lo AH LOA LOS SPT) as (S1 & S2 & S3 & S4).
    unfold ablk, AIMG_HI in ABK. lia.
  Time Qed.

  Lemma w4f_x1631 : forall k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3,
    W4KFT k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 ->
    W4KFEND k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 ->
    W4K1631 k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3.
  Proof.
    intros k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 KT KE.
    intros mm op x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x16 x19 x25 x27 x28 HM HSR HK HOP HO.
    pose proof w4f_db as (D1 & D2 & D3 & D4 & D5).
    pose proof HSR as (H3 & _).
    pose proof (w4f_se k HK H3) as (SE1 & _).
    rewrite w4f_x17. unfold AW4_X1631, AW4_FT, AW4_FEND, AW4_KSB, AW4_KTB.
    remember (w4se k) as se eqn:ESE. remember (w4nth k o0 o1 o2 o3) as ok eqn:EOK.
    destruct (Z_lt_le_dec op se) as [HL|HG].
    - kx_runFmd [AW4_FT; AW4_FEND] 40%nat [true]
        [KZRange op 4096 (2^47); KZRange se 4096 (2^47); KZRange (se - op) 1 (2^47)]
        (@nil (Z * Z)) (@nil (Z * Z)) (@nil (Z * Z)).
      all: try w4br.
      kx_post_regs. cbn [mem_denot].
      subst se ok. w4f_k KT.
    - kx_runFmd [AW4_FT; AW4_FEND] 40%nat [false]
        [KZRange op 4096 (2^47); KZRange se 4096 (2^47); KZRange (op - se) 0 0]
        (@nil (Z * Z)) (@nil (Z * Z)) (@nil (Z * Z)).
      all: try w4br.
      kx_post_regs. cbn [mem_denot].
      subst se ok. w4f_k KE.
  Time Qed.

  Lemma w4f_x1675 : forall k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3,
    W4KFT k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 ->
    W4KFEND k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 ->
    W4K1675 k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3.
  Proof.
    intros k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 KT KE.
    intros mm op x5 x6 x7 x8 x9 x10 x12 x13 x14 x16 x19 x22 x25 x27 x28 HM HSR HK HOP HO.
    pose proof w4f_db as (D1 & D2 & D3 & D4 & D5).
    pose proof HSR as (H3 & _).
    pose proof (w4f_se k HK H3) as (SE1 & _).
    rewrite w4f_x17. unfold AW4_X1675, AW4_FT, AW4_FEND, AW4_KSB, AW4_KTB.
    remember (w4se k) as se eqn:ESE. remember (w4nth k o0 o1 o2 o3) as ok eqn:EOK.
    destruct (Z_lt_le_dec op se) as [HL|HG].
    - kx_runFmd [AW4_FT; AW4_FEND] 40%nat [false]
        [KZRange op 4096 (2^47); KZRange se 4096 (2^47); KZRange (se - op) 1 (2^47)]
        (@nil (Z * Z)) (@nil (Z * Z)) (@nil (Z * Z)).
      all: try w4br.
      kx_post_regs. cbn [mem_denot].
      subst se ok. w4f_k KT.
    - kx_runFmd [AW4_FT; AW4_FEND] 40%nat [true]
        [KZRange op 4096 (2^47); KZRange se 4096 (2^47); KZRange (op - se) 0 0]
        (@nil (Z * Z)) (@nil (Z * Z)) (@nil (Z * Z)).
      all: try w4br.
      kx_post_regs. cbn [mem_denot].
      subst se ok. w4f_k KE.
  Time Qed.

  Lemma w4f_x1674 : forall k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3,
    W4KFT k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 ->
    W4KFEND k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 ->
    W4K1674 k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3.
  Proof.
    intros k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 KT KE.
    intros mm u v x6 x7 x8 x9 x10 x11 x12 x13 x14 x16 x19 x22 x27 x28 HM HSR HK HOP HO.
    pose proof w4f_db as (D1 & D2 & D3 & D4 & D5).
    pose proof HSR as (H3 & _).
    pose proof (w4f_se k HK H3) as (SE1 & _).
    rewrite w4f_x17. unfold AW4_X1674, AW4_FT, AW4_FEND, AW4_KSB, AW4_KTB.
    remember (w4se k) as se eqn:ESE. remember (w4nth k o0 o1 o2 o3) as ok eqn:EOK.
    destruct (Z_lt_le_dec (u + v) se) as [HL|HG].
    - kx_runFmd [AW4_FT; AW4_FEND] 40%nat [false]
        [KZRange (u + v) 4096 (2^47); KZRange se 4096 (2^47); KZRange (se - (u + v)) 1 (2^47)]
        (@nil (Z * Z)) (@nil (Z * Z)) (@nil (Z * Z)).
      all: try w4br.
      kx_post_regs. cbn [mem_denot].
      subst se ok. w4f_k KT.
    - kx_runFmd [AW4_FT; AW4_FEND] 40%nat [true]
        [KZRange (u + v) 4096 (2^47); KZRange se 4096 (2^47); KZRange (u + v - se) 0 0]
        (@nil (Z * Z)) (@nil (Z * Z)) (@nil (Z * Z)).
      all: try w4br.
      kx_post_regs. cbn [mem_denot].
      subst se ok. w4f_k KE.
  Time Qed.

  Lemma w4f_srk : forall k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3,
    W4SR i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> (k <= 3)%nat ->
    0 <= w4nth k i0 i1 i2 i3 /\ w4nth k i0 i1 i2 i3 + 8 <= n /\ 0 <= w4nth k o0 o1 o2 o3 <= dcap.
  Proof.
    intros k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 HSR HK.
    destruct HSR as (_ & _ & (A0 & B0 & C0 & _) & (A1 & B1 & C1 & _) & (A2 & B2 & C2 & _) & (A3 & B3 & C3 & _)).
    destruct k as [|[|[|[|k]]]]; cbn [w4nth nth]; lia.
  Time Qed.

  Ltac w4f_epre :=
    lazymatch goal with
    | HM : W4TM ?k _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm, HSR : W4SR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, HK : (?k <= 3)%nat |- _ =>
        pose proof (w4f_srk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HSR HK) as (IK1 & IK2 & OK1);
        pose proof HSR as (H3 & H9 & _);
        pose proof (w4f_se k HK H3) as (SE1 & _);
        pose proof HM as (w0 & w8 & w16 & w24 & w32 & a0 & a1 & a2 & a3 & p0 & p1 & p2 & p3 & b0 & b1 & b2 & b3 & q0 & q1 & q2 & q3 & adt & oew & l256 & l296 & l336 & HF);
        pose proof (w4f_unp _ _ _ _ _ _ HF ltac:(lia)) as
          ((U1 & U2 & U3 & U4 & U5 & U6 & U7 & U8) & _ & _ & R480 & AP1 & _ & _ & B1 & B2 & _ & _ & B5 & B6 & B7 & B8 & B9 & B10);
        pose proof HF as (_ & HSS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI & _ & _);
        assert (LSM : Z.of_nat (length (map (Z_to_bv 8) src)) = n) by (rewrite length_map; reflexivity);
        assert (RSS : rng RNG SS n) by (apply (rng_sub RNG SBL (SBH - SBL)); [exact U5 | lia | lia]);
        unfold AIMG_HI in *
    end.

  Definition W4KFEc (P : Z -> Z -> Prop) (k : nat) (i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 : Z) (c0 c1 c2 c3 : word) : Prop :=
    forall (mm : amem) (bc : Z) (x6 x7 x11 x12 x13 x14 x16 x22 x25 x27 x28 : word),
    P (w4nth k i0 i1 i2 i3) bc -> W4TM k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 mm ->
    W4SR i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> (k <= 3)%nat -> 0 <= bc <= 64 ->
    DST + w4nth k o0 o1 o2 o3 <= w4se k ->
    evtF bsegs RNG POST
      (MS (mkR (Z_to_bv 64 (w4se k)) (Z_to_bv 64 SPF) gp tp (Z_to_bv 64 (DST + w4nth k o0 o1 o2 o3)) x6 x7
               (Z_to_bv 64 (SS + 8)) (Z_to_bv 64 bc) (Z_to_bv 64 (SS + w4nth k i0 i1 i2 i3)) x11 x12 x13 x14
               (Z_to_bv 64 (Z.of_nat k)) x16 (Z_to_bv 64 (2^64 - DT - 5)) (Z_to_bv 64 (w4se k - (DST + w4nth k o0 o1 o2 o3)))
               (Z_to_bv 64 SS) (Z_to_bv 64 (w4se k)) (Z_to_bv 64 (SP + -344 + 8 * Z.of_nat k)) x22 (Z_to_bv 64 (DT + 4))
               (Z_to_bv 64 AW4_KSB) x25 (Z_to_bv 64 AW4_KTB) x27 x28 (Z_to_bv 64 2) (Z_to_bv 64 (-1)) (Z_to_bv 64 64))
          FR (Z_to_bv 64 AW4_FE) fc None mm (seg_rom bsegs)).

  Ltac w4f_er KT KE se ok ik bc ilo ihi blo bhi :=
    destruct (Z_lt_le_dec (DST + ok) se) as [HL|HG];
    [ kx_runFmd [AW4_FT; AW4_FEND] 80%nat (@nil bool)
        [KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange SS 4096 (2^47); KZRange (SS + n) 4096 (2^47);
         KZRange n 9 (2^26); KZRange ik ilo ihi; KZRange (n - ik) 8 (2^26); KZRange ok 0 (2^32);
         KZRange (se - (DST + ok)) 1 (2^47); KZRange se 4096 (2^47); KZRange bc blo bhi; KZDisj SS n (SP + -480) 480]
        [(SS, n)] (@nil (Z * Z)) [(SS, n)];
      try w4br; try (kx_asan I); try (kx_post_regs; cbn [mem_denot]); subst se ok ik; w4f_k KT
    | kx_runFmd [AW4_FT; AW4_FEND] 80%nat (@nil bool)
        [KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange SS 4096 (2^47); KZRange (SS + n) 4096 (2^47);
         KZRange n 9 (2^26); KZRange ik ilo ihi; KZRange (n - ik) 8 (2^26); KZRange ok 0 (2^32);
         KZRange (se - (DST + ok)) 0 0; KZRange se 4096 (2^47); KZRange bc blo bhi; KZDisj SS n (SP + -480) 480]
        [(SS, n)] (@nil (Z * Z)) [(SS, n)];
      try w4br; try (kx_asan I); try (kx_post_regs; cbn [mem_denot]); subst se ok ik; w4f_k KE ].

  Ltac w4f_eintro :=
    intros k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 KT KE;
    intros mm bc x6 x7 x11 x12 x13 x14 x16 x22 x25 x27 x28 HP HM HSR HK HBC HO;
    w4f_epre;
    rewrite w4f_x17; unfold AW4_FE, AW4_FT, AW4_FEND, AW4_KSB, AW4_KTB;
    remember (w4se k) as se eqn:ESE; remember (w4nth k o0 o1 o2 o3) as ok eqn:EOK;
    remember (w4nth k i0 i1 i2 i3) as ik eqn:EIK.

  Lemma w4f_eA : forall k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3,
    W4KFT k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> W4KFEND k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> W4KFEc (fun ik bc => 8 <= ik \/ ik = 0) k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3.
  Proof.
    w4f_eintro.
    destruct HP as [I8|I0].
    - w4f_er KT KE se ok ik bc 8 (2^26) 0 64.
    - w4f_er KT KE se ok ik bc 0 0 0 64.
  Time Qed.

  Lemma w4f_eB : forall k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3,
    W4KFT k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> W4KFEND k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> W4KFEc (fun ik bc => 1 <= ik <= 7 /\ bc <= 39) k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3.
  Proof.
    w4f_eintro.
    destruct HP as (I1 & BJ).
    assert (CJ : (0 <= bc <= 7) \/ (8 <= bc <= 15) \/ (16 <= bc <= 23) \/ (24 <= bc <= 31) \/ (32 <= bc <= 39)) by lia.
    destruct CJ as [C0|[C1|[C2|[C3|C4]]]].
    - w4f_er KT KE se ok ik bc 1 7 0 7.
    - w4f_er KT KE se ok ik bc 1 7 8 15.
    - destruct (Z_le_gt_dec 2 ik) as [J1|J1].
      + w4f_er KT KE se ok ik bc 2 7 16 23.
      + w4f_er KT KE se ok ik bc 1 1 16 23.
    - destruct (Z_le_gt_dec 3 ik) as [J1|J1].
      + w4f_er KT KE se ok ik bc 3 7 24 31.
      + w4f_er KT KE se ok ik bc 1 2 24 31.
    - destruct (Z_le_gt_dec 4 ik) as [J1|J1].
      + w4f_er KT KE se ok ik bc 4 7 32 39.
      + w4f_er KT KE se ok ik bc 1 3 32 39.
  Time Qed.

  Lemma w4f_eC : forall k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3,
    W4KFT k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> W4KFEND k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> W4KFEc (fun ik bc => 1 <= ik <= 7 /\ 40 <= bc) k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3.
  Proof.
    w4f_eintro.
    destruct HP as (I1 & BJ).
    assert (CJ : (40 <= bc <= 47) \/ (48 <= bc <= 55) \/ (56 <= bc <= 63) \/ (64 <= bc <= 64)) by lia.
    destruct CJ as [C5|[C6|[C7|C8]]].
    - destruct (Z_le_gt_dec 5 ik) as [J1|J1].
      + w4f_er KT KE se ok ik bc 5 7 40 47.
      + w4f_er KT KE se ok ik bc 1 4 40 47.
    - destruct (Z_le_gt_dec 6 ik) as [J1|J1].
      + w4f_er KT KE se ok ik bc 6 7 48 55.
      + w4f_er KT KE se ok ik bc 1 5 48 55.
    - destruct (Z_le_gt_dec 7 ik) as [J1|J1].
      + w4f_er KT KE se ok ik bc 7 7 56 63.
      + w4f_er KT KE se ok ik bc 1 6 56 63.
    - w4f_er KT KE se ok ik bc 1 7 64 64.
  Time Qed.

  Lemma w4f_else : forall k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3,
    W4KFT k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> W4KFEND k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> W4KFE k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3.
  Proof.
    intros k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 KT KE.
    intros mm bc x6 x7 x11 x12 x13 x14 x16 x22 x25 x27 x28 HM HSR HK HBC HO.
    destruct (Z_le_gt_dec 8 (w4nth k i0 i1 i2 i3)) as [I|I];
      [| destruct (Z.eq_dec (w4nth k i0 i1 i2 i3) 0) as [I0|I0]; [| destruct (Z_le_gt_dec bc 39) as [B|B]]].
    - eapply (w4f_eA k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 KT KE); [left; lia | eassumption ..].
    - eapply (w4f_eA k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 KT KE); [right; lia | eassumption ..].
    - pose proof (w4f_srk k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 HSR HK).
      eapply (w4f_eB k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 KT KE); [lia | eassumption ..].
    - pose proof (w4f_srk k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 HSR HK).
      eapply (w4f_eC k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 KT KE); [lia | eassumption ..].
  Time Qed.

  Lemma w4f_wmid : forall mm fr mid l256 l296 l336 j c v (A : word) bs,
    W4FX mm fr mid l256 l296 l336 -> 0 < n -> cell_at mid j = Some c -> csize c = 8%nat ->
    A = wa (SPF + 104 + Z.of_nat j) -> bs = cbytes (C8 v) ->
    W4FX (CatExec.wbytes mm A bs) fr (cell_upd mid j (C8 v)) l256 l296 l336.
  Proof.
    intros mm fr mid l256 l296 l336 j c v A bs HF HN HC HS EA EB. subst A bs. rewrite wbytes_eq.
    pose proof (w4f_unp _ _ _ _ _ _ HF HN) as
      ((U1 & U2 & U3 & U4 & U5 & U6 & U7 & U8) & (T1 & T2 & T3 & T4 & T5 & T6 & T7) & (V1 & V2 & V3 & V4 & V5 & V6)
       & R480 & AP1 & AP2 & AP3 & B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
    destruct HF as ((buf & OUT & LBF) & HSS & HT4 & HT0 & STK & FRc & FRs & MIDc & MIDs & L1c & L1s & L2c & L2s & L3c & L3s
                    & FRSc & MI & MU & WM).
    pose proof (cell_at_split mid j c (C8 v) HC) as (pre & post & Emid & Epre & Eupd).
    assert (JB : (j + 8 <= 152)%nat) by (rewrite <- MIDs, Emid, cells_size_app; cbn [cells_size]; lia).
    assert (LBY : Z.of_nat (length (cbytes (C8 v))) = 8) by (rewrite cbytes_length by exact I; reflexivity).
    assert (LSM : Z.of_nat (length (map (Z_to_bv 8) src)) = n) by (rewrite length_map; reflexivity).
    assert (LCB' : Z.of_nat (length cbs) = 4096) by (rewrite LCB, TL11; reflexivity).
    unfold AIMG_HI, ATOP_MAX in *. pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
    unfold DTABLE_BYTES in *.
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj FRs (conj _ (conj _ (conj _ (conj L1s (conj _ (conj L2s
              (conj _ (conj L3s (conj _ (conj _ (conj _ _)))))))))))))))))).
    - exists buf. split; [| exact LBF]. apply u8arr_frame; [exact OUT | lia | lia |].
      rewrite length_map. left. lia.
    - apply bytes_at_write_other; [exact HSS | lia | lia | left; lia].
    - apply bytes_at_write_other; [exact HT4 | lia | lia | left; lia].
    - apply bytes_at_write_other; [exact HT0 | lia | lia | left; cbn [length Z.of_nat]; lia].
    - apply stk_write; [exact STK | lia | lia].
    - apply rw_cells_frame; [exact FRc | lia | lia | left; rewrite FRs; lia].
    - exact (rw_cells_write bsegs mm (SPF + 104) mid j c (C8 v) MIDc HC (eq_sym HS) I).
    - rewrite Eupd. rewrite Emid in MIDs. rewrite cells_size_app in *. cbn [cells_size csize] in *. lia.
    - apply rw_cells_frame; [exact L1c | lia | lia | right; lia].
    - apply rw_cells_frame; [exact L2c | lia | lia | right; lia].
    - apply rw_cells_frame; [exact L3c | lia | lia | right; lia].
    - apply rw_cells_frame; [exact FRSc | lia | lia | right; lia].
    - apply mem_inv_store_cbytes; [exact MI | exact I |].
      eapply rw_cells_store_ok_at; [exact MIDc | exact HC | cbn [csize]; exact (eq_sym HS) | reflexivity].
    - apply munch_write; [exact MU | lia | lia | cbn [inside]; left; lia].
    - apply wmono_write. exact WM.
  Time Qed.

  Ltac w4f_addr :=
    rewrite adenot_wa; unfold wa; f_equal; unfold estart; cbn [a_base a_off]; w4ez;
    rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite ?Z.mod_small by lia; lia.

  Ltac w4f_wend HF j :=
    lazymatch goal with |- context [CatExec.wbytes ?m ?A (word_to_le_bytes 8 ?V)] =>
      let HF' := fresh "HF'" in
      pose proof (w4f_wmid _ _ _ _ _ _ j _ V A (word_to_le_bytes 8 V) HF ltac:(lia) eq_refl eq_refl
                    ltac:(w4f_addr) eq_refl) as HF'
    end.

  Ltac w4f_gen HF' :=
    lazymatch goal with |- context [MS _ _ _ _ _ ?M _] =>
      revert HF'; generalize M; intros m1 HF' end.

  Lemma w4f_end : forall k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3,
    ((k < 3)%nat -> W4KF3 (S k) i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3) -> (k = 3%nat -> W4KFX2) ->
    W4KFEND k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3.
  Proof.
    intros k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 K3 KX.
    intros mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x16 x19 x22 x25 x27 x28 HM HSR HK HO.
    pose proof HSR as (H3 & H9 & _).
    pose proof (w4f_se k HK H3) as (SE1 & SE2 & SE3).
    pose proof (w4f_srk k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 HSR HK) as (IK1 & IK2 & OK1).
    destruct HM as (w0 & w8 & w16 & w24 & w32 & a0 & a1 & a2 & a3 & p0 & p1 & p2 & p3 & b0 & b1 & b2 & b3 & q0 & q1 & q2 & q3 & adt & oew & l256 & l296 & l336 & HF).
    pose proof (w4f_unp _ _ _ _ _ _ HF ltac:(lia)) as
      (_ & _ & _ & R480 & _ & _ & _ & B1 & B2 & _ & _ & B5 & B6 & B7 & B8 & B9 & B10).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX, AIMG_HI in *.
    rewrite w4f_x17. unfold AW4_FEND, AW4_F3, AW4_FERR, AW4_FX2, AW4_KSB, AW4_KTB.
    remember (w4se k) as se eqn:ESE.
    destruct k as [|[|[|[|k]]]]; [| | | | lia].
    - replace (SP + -344 + 8 * Z.of_nat 0) with (SP + -344) by lia.
      change (Z.of_nat 0) with 0 in *. cbn [w4nth nth] in *.
      pose proof HF as (_ & _ & _ & _ & _ & _ & _ & MIDc & _).
      unfold w4mid, w4sel in MIDc. cbn [firstn skipn app map] in MIDc.
      replace (SP + -480 + 104) with (SP + -376) in MIDc by lia.
      Time kx_runFmd [AW4_F3; AW4_FERR; AW4_FX2] 60%nat [true; true]
        [KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange se 4096 (2^47); KZRange o0 0 (2^32);
         KZRange (se - (DST + o0)) 0 (2^47); KZRange SP 8192 (2^47);
         KZWord (SP + -344) 8 (DST + o0); KZWr (SP + -376) 152]
        (@nil (Z * Z)) [(SP + -480, 480)] (@nil (Z * Z)).
      all: try w4br.
      all: try (kx_post_regs; cbn [mem_denot]).
      all: subst se.
      pose proof (K3 ltac:(lia)) as K3'. unfold W4KF3, AW4_F3 in K3'.
      w4f_wend HF 32%nat.
      unfold w4mid, w4sel in HF'; cbn [cell_upd firstn skipn app map csize Nat.eqb Nat.sub] in HF'.
      w4f_gen HF'.
      eapply w4f_st; [eapply (K3' m1 w0 w8 w16 w24 w32 _ a1 a2 a3 _ p1 p2 p3 _ b1 b2 b3 _ q1 q2 q3 adt oew l256 l296 l336) | ..]; try (lazymatch goal with |- @eq _ _ _ => w4f_eq end).
      all: try eassumption; try lia.
      unfold w4mid, w4sel; cbn [firstn skipn app map]. exact HF'.
    - replace (SP + -344 + 8 * Z.of_nat 1) with (SP + -336) by lia.
      change (Z.of_nat 1) with 1 in *. cbn [w4nth nth] in *.
      pose proof HF as (_ & _ & _ & _ & _ & _ & _ & MIDc & _).
      unfold w4mid, w4sel in MIDc. cbn [firstn skipn app map] in MIDc.
      replace (SP + -480 + 104) with (SP + -376) in MIDc by lia.
      Time kx_runFmd [AW4_F3; AW4_FERR; AW4_FX2] 60%nat [true; true]
        [KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange se 4096 (2^47); KZRange o1 0 (2^32);
         KZRange (se - (DST + o1)) 0 (2^47); KZRange SP 8192 (2^47);
         KZWord (SP + -336) 8 (DST + o1); KZWr (SP + -376) 152]
        (@nil (Z * Z)) [(SP + -480, 480)] (@nil (Z * Z)).
      all: try w4br.
      all: try (kx_post_regs; cbn [mem_denot]).
      all: subst se.
      pose proof (K3 ltac:(lia)) as K3'. unfold W4KF3, AW4_F3 in K3'.
      w4f_wend HF 40%nat.
      unfold w4mid, w4sel in HF'; cbn [cell_upd firstn skipn app map csize Nat.eqb Nat.sub] in HF'.
      w4f_gen HF'.
      eapply w4f_st; [eapply (K3' m1 w0 w8 w16 w24 w32 a0 _ a2 a3 p0 _ p2 p3 b0 _ b2 b3 q0 _ q2 q3 adt oew l256 l296 l336) | ..]; try (lazymatch goal with |- @eq _ _ _ => w4f_eq end).
      all: try eassumption; try lia.
      unfold w4mid, w4sel; cbn [firstn skipn app map]. exact HF'.
    - replace (SP + -344 + 8 * Z.of_nat 2) with (SP + -328) by lia.
      change (Z.of_nat 2) with 2 in *. cbn [w4nth nth] in *.
      pose proof HF as (_ & _ & _ & _ & _ & _ & _ & MIDc & _).
      unfold w4mid, w4sel in MIDc. cbn [firstn skipn app map] in MIDc.
      replace (SP + -480 + 104) with (SP + -376) in MIDc by lia.
      Time kx_runFmd [AW4_F3; AW4_FERR; AW4_FX2] 60%nat [true; true]
        [KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange se 4096 (2^47); KZRange o2 0 (2^32);
         KZRange (se - (DST + o2)) 0 (2^47); KZRange SP 8192 (2^47);
         KZWord (SP + -328) 8 (DST + o2); KZWr (SP + -376) 152]
        (@nil (Z * Z)) [(SP + -480, 480)] (@nil (Z * Z)).
      all: try w4br.
      all: try (kx_post_regs; cbn [mem_denot]).
      all: subst se.
      pose proof (K3 ltac:(lia)) as K3'. unfold W4KF3, AW4_F3 in K3'.
      w4f_wend HF 48%nat.
      unfold w4mid, w4sel in HF'; cbn [cell_upd firstn skipn app map csize Nat.eqb Nat.sub] in HF'.
      w4f_gen HF'.
      eapply w4f_st; [eapply (K3' m1 w0 w8 w16 w24 w32 a0 a1 _ a3 p0 p1 _ p3 b0 b1 _ b3 q0 q1 _ q3 adt oew l256 l296 l336) | ..]; try (lazymatch goal with |- @eq _ _ _ => w4f_eq end).
      all: try eassumption; try lia.
      unfold w4mid, w4sel; cbn [firstn skipn app map]. exact HF'.
    - replace (SP + -344 + 8 * Z.of_nat 3) with (SP + -320) by lia.
      change (Z.of_nat 3) with 3 in *. cbn [w4nth nth] in *.
      pose proof HF as (_ & _ & _ & _ & _ & _ & _ & MIDc & _).
      unfold w4mid, w4sel in MIDc. cbn [firstn skipn app map] in MIDc.
      replace (SP + -480 + 104) with (SP + -376) in MIDc by lia.
      Time kx_runFmd [AW4_F3; AW4_FERR; AW4_FX2] 60%nat [true; true]
        [KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange se 4096 (2^47); KZRange o3 0 (2^32);
         KZRange (se - (DST + o3)) 0 (2^47); KZRange SP 8192 (2^47);
         KZWord (SP + -320) 8 (DST + o3); KZWr (SP + -376) 152]
        (@nil (Z * Z)) [(SP + -480, 480)] (@nil (Z * Z)).
      all: try w4br.
      all: try (kx_post_regs; cbn [mem_denot]).
      all: subst se.
      pose proof (KX eq_refl) as KX'. unfold W4KFX2, AW4_FX2 in KX'.
      w4f_wend HF 56%nat.
      w4f_gen HF'.
      eapply w4f_st; [eapply (KX' m1 w0 w8 w16 w24 w32) | ..]; try (lazymatch goal with |- @eq _ _ _ => w4f_eq end).
      all: try eassumption; try lia.
  Time Qed.

  Definition W4KFTo (k : nat) (i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 : Z) (c0 c1 c2 c3 : word) (op : Z) : Prop :=
    forall (mm : amem) (x1 x6 x7 x8 x9 x11 x12 x14 x16 x19 x22 x25 x27 x28 : word),
    W4TM k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 mm ->
    W4SR i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> (k <= 3)%nat -> DST <= op < w4se k ->
    DST + w4nth k o0 o1 o2 o3 <= w4se k ->
    evtF bsegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp (Z_to_bv 64 op) x6 x7 x8 x9 (Z_to_bv 64 op) x11 x12 (Z_to_bv 64 (w4se k - op)) x14
               (Z_to_bv 64 (Z.of_nat k)) x16 (Z_to_bv 64 (2^64 - DT - 5)) (Z_to_bv 64 (w4se k - (DST + w4nth k o0 o1 o2 o3)))
               x19 (Z_to_bv 64 (w4se k)) (Z_to_bv 64 (SP + -344 + 8 * Z.of_nat k)) x22 (Z_to_bv 64 (DT + 4))
               (Z_to_bv 64 AW4_KSB) x25 (Z_to_bv 64 AW4_KTB) x27 x28 (Z_to_bv 64 2) (Z_to_bv 64 (-1)) (Z_to_bv 64 64))
          FR (Z_to_bv 64 AW4_FT) fc None mm (seg_rom bsegs)).

  Lemma w4f_negm : forall x M, M = 2^64 -> - M < x < 0 -> x mod M = x + M.
  Proof.
    intros x M EM HX. rewrite <- (Z.mod_add x 1 M) by lia. rewrite Z.mod_small; lia.
  Qed.

  Lemma w4f_geu : forall a b : word, 8192 <= bv_unsigned a -> bv_unsigned b < 8192 -> branch_taken BC_GEU a b = true.
  Proof.
    intros a b HA HB. unfold branch_taken. rewrite ?bv_ltu_Z.
    destruct (Z.ltb_spec (bv_unsigned a) (bv_unsigned b)); cbn [negb]; first [reflexivity | lia].
  Qed.

  Lemma w4f_q : forall E x, bv_unsigned (edenot E (EMd M_MUL (ELit 2) (EAlu ALU_SRL x (ELit 53)))) < 4096.
  Proof.
    intros E x. pose proof (kx_srl_tl E x (ELit 53) 11 eq_refl ltac:(lia)) as B.
    change (edenot E (EMd M_MUL (ELit 2) (EAlu ALU_SRL x (ELit 53))))
      with (mul_div M_MUL (edenot E (ELit 2)) (edenot E (EAlu ALU_SRL x (ELit 53)))).
    rewrite u_mul64. change (bv_unsigned (edenot E (ELit 2))) with 2.
    rewrite Z.mod_small; lia.
  Qed.

  Ltac w4f_x17c :=
    apply w4f_geu;
    [ w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; erewrite w4f_negm; [| reflexivity | lia]; lia
    | lazymatch goal with |- bv_unsigned (edenot ?E (EMd M_MUL (ELit 2) (EAlu ALU_SRL ?x (ELit 53)))) < _ =>
        pose proof (w4f_q E x); lia end ].

  Lemma w4f_tw : forall (Q : machine_state -> Prop) (mm : amem) (buf : list Z)
      (x1 x6 x7 x8 x9 x11 x12 x14 x15 x16 x18 x19 x20 x21 x22 x25 x27 x28 x30 : word) (se op : Z),
    u8arr bsegs mm DST (map (Z_to_bv 8) buf) -> Z.of_nat (length (map (Z_to_bv 8) buf)) = dcap ->
    bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 4096 ->
    unpoisoned mm DT (DT + DTL) -> rng RNG (shad DT) (shlen (DTL + 7)) -> DT mod 8 = 0 -> 0 <= DT -> DT + 4 + 4096 <= DT + DTL ->
    unpoisoned mm DST (DST + dcap) -> rng RNG (shad DST) (shlen (dcap + 7)) -> DST mod 8 = 0 -> 0 <= DST ->
    rng RNG (DT + 4) 4096 -> rng RNG op 1 -> rng RNG (SP + -480) 480 -> KXGoM.apart DST dcap (SP + -480) 480 ->
    mem_inv bsegs mm -> 1 <= dcap ->
    4096 <= DST <= 2^47 -> 4096 <= DT <= 2^47 -> 8192 <= SP <= 2^47 -> DST <= op -> op < se -> se <= DST + dcap ->
    DST + dcap <= 2^47 ->
    (op + 1 < se -> forall m1 buf' (y1 y6 y7 y8 y9 y11 y12 y14 y16 y19 y22 y25 y27 y28 : word), munch [(op, op + 1)] mm m1 -> wmono bsegs mm m1 -> mem_inv bsegs m1 -> u8arr bsegs m1 DST (map (Z_to_bv 8) buf') -> length buf' = length buf ->
       evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 SPF) gp tp (Z_to_bv 64 (op + 1)) y6 y7 y8 y9 (Z_to_bv 64 (op + 1)) y11 y12 (Z_to_bv 64 (se - (op + 1))) y14 x15 y16 (Z_to_bv 64 (- DT - 5)) x18 y19 x20 x21 y22 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 AW4_KSB) y25 (Z_to_bv 64 AW4_KTB) y27 y28 (Z_to_bv 64 2) x30 (Z_to_bv 64 64)) FR (Z_to_bv 64 AW4_FT) fc None m1 (seg_rom bsegs))) ->
    (op + 1 = se -> forall m1 buf' (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y16 y19 y22 y25 y27 y28 : word), munch [(op, op + 1)] mm m1 -> wmono bsegs mm m1 -> mem_inv bsegs m1 -> u8arr bsegs m1 DST (map (Z_to_bv 8) buf') -> length buf' = length buf ->
       evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 SPF) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 x15 y16 (Z_to_bv 64 (- DT - 5)) x18 y19 x20 x21 y22 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 AW4_KSB) y25 (Z_to_bv 64 AW4_KTB) y27 y28 (Z_to_bv 64 2) x30 (Z_to_bv 64 64)) FR (Z_to_bv 64 AW4_FEND) fc None m1 (seg_rom bsegs))) ->
    evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 SPF) gp tp (Z_to_bv 64 op) x6 x7 x8 x9 (Z_to_bv 64 op) x11 x12 (Z_to_bv 64 (se - op)) x14 x15 x16 (Z_to_bv 64 (- DT - 5)) x18 x19 x20 x21 x22 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 AW4_KSB) x25 (Z_to_bv 64 AW4_KTB) x27 x28 (Z_to_bv 64 2) x30 (Z_to_bv 64 64)) FR (Z_to_bv 64 AW4_FT) fc None mm (seg_rom bsegs)).
  Proof.
    intros Q mm buf x1 x6 x7 x8 x9 x11 x12 x14 x15 x16 x18 x19 x20 x21 x22 x25 x27 x28 x30 se op
      OUT LOB HT4 LCB' T1 T2 T3 T4 T7 V1 V2 V3 V4 RT4 RO R480 AP3 MI0 DC1 BD1 BD2 BD3 HO1 HO2 HO3 BD4 KT KE.
    clear AH HDB HDT SRCB.
    unfold AW4_FT, AW4_FEND, AW4_KSB, AW4_KTB.
    destruct (Z.eq_dec (se - op) 1) as [E1|E1].
    - Time kx_runFmd [AW4_FT; AW4_FEND] 80%nat [true; false; false; false]
        [KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange DT 4096 (2^47); KZRange SP 8192 (2^47);
         KZRange op 4096 (2^47); KZRange se 4096 (2^47); KZRange (se - op) 1 1; KZRange (DST + dcap - se) 0 (2^32);
         KZRange (op - DST) 0 (2^32); KZIdx 11 2048; KZWr op 1; KZDisj op 1 (DT + 4) 4096; KZDisj op 1 (SP + -480) 480]
        [(DT + 4, 4096)] [(SP + -480, 480); (DT + 4, 4096); (op, 1)] [(DT + 4, 4096); (op, 1)].
      all: try w4br.
      all: try w4f_x17c.
      Time kx_post_regs_keep.
      lazymatch goal with H : u8arr bsegs mm DST _, HL : log_flat _ _ |- _ =>
        destruct (kx_u8arr_ex bsegs _ mm _ DST buf H HL) as (buf' & OUT' & LB') end.
      pose proof (munch_refl [(op, op + 1)] mm) as MUW. pose proof (wmono_refl bsegs mm) as WMr.
      Time kx_munch_wins MUW [(op, 1)].
      Time kx_post_mem_free.
      lazymatch goal with |- context [mem_denot ?E mm ?l] => set (m1 := mem_denot E mm l) in * end.
      eapply w4f_st; [eapply (KE ltac:(lia) m1 buf') | ..];
        try (lazymatch goal with |- @eq _ _ _ => w4f_eq end); try eassumption; try lia.
    - Time kx_runFmd [AW4_FT; AW4_FEND] 80%nat [true; false; false; false]
        [KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange DT 4096 (2^47); KZRange SP 8192 (2^47);
         KZRange op 4096 (2^47); KZRange se 4096 (2^47); KZRange (se - op) 2 (2^47); KZRange (DST + dcap - se) 0 (2^32);
         KZRange (op - DST) 0 (2^32); KZIdx 11 2048; KZWr op 1; KZDisj op 1 (DT + 4) 4096; KZDisj op 1 (SP + -480) 480]
        [(DT + 4, 4096)] [(SP + -480, 480); (DT + 4, 4096); (op, 1)] [(DT + 4, 4096); (op, 1)].
      all: try w4br.
      all: try w4f_x17c.
      Time kx_post_regs_keep.
      lazymatch goal with H : u8arr bsegs mm DST _, HL : log_flat _ _ |- _ =>
        destruct (kx_u8arr_ex bsegs _ mm _ DST buf H HL) as (buf' & OUT' & LB') end.
      pose proof (munch_refl [(op, op + 1)] mm) as MUW. pose proof (wmono_refl bsegs mm) as WMr.
      Time kx_munch_wins MUW [(op, 1)].
      Time kx_post_mem_free.
      lazymatch goal with |- context [mem_denot ?E mm ?l] => set (m1 := mem_denot E mm l) in * end.
      eapply w4f_st; [eapply (KT ltac:(lia) m1 buf') | ..];
        try (lazymatch goal with |- @eq _ _ _ => w4f_eq end); try eassumption; try lia.
  Time Qed.

  Lemma w4f_t1 : forall k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 op,
    W4KFEND k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> (op + 1 < w4se k -> W4KFTo k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 (op + 1)) -> W4KFTo k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 op.
  Proof.
    intros k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 op KE IH.
    intros mm x1 x6 x7 x8 x9 x11 x12 x14 x16 x19 x22 x25 x27 x28 HM HSR HK HOP HO.
    pose proof HSR as (H3 & H9 & _).
    pose proof (w4f_se k HK H3) as (SE1 & _).
    pose proof (w4f_srk k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 HSR HK) as (IK1 & IK2 & OK1).
    destruct HM as (w0 & w8 & w16 & w24 & w32 & a0 & a1 & a2 & a3 & p0 & p1 & p2 & p3 & b0 & b1 & b2 & b3 & q0 & q1 & q2 & q3 & adt & oew & l256 & l296 & l336 & HF).
    pose proof (w4f_unp _ _ _ _ _ _ HF ltac:(lia)) as
      (_ & (T1 & T2 & T3 & T4 & T5 & T6 & T7) & (V1 & V2 & V3 & V4 & V5 & V6) & R480 & _ & AP2 & AP3
       & B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
    pose proof HF as ((buf & OUT & LBF) & _ & HT4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI0 & _ & _).
    assert (LOB : Z.of_nat (length (map (Z_to_bv 8) buf)) = dcap) by (rewrite length_map; exact LBF).
    assert (LCB' : Z.of_nat (length cbs) = 4096) by (rewrite LCB, TL11; reflexivity).
    assert (RT4 : rng RNG (DT + 4) 4096) by (apply (rng_sub RNG DT DTL); [exact T5 | lia | lia]).
    assert (RO : rng RNG op 1) by (apply (rng_sub RNG DST dcap); [exact V5 | lia | lia]).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX, AIMG_HI in *.
    rewrite w4f_x17.
    eapply (w4f_tw POST mm buf x1 x6 x7 x8 x9 x11 x12 x14 (Z_to_bv 64 (Z.of_nat k)) x16
              (Z_to_bv 64 (w4se k - (DST + w4nth k o0 o1 o2 o3))) x19 (Z_to_bv 64 (w4se k))
              (Z_to_bv 64 (SP + -344 + 8 * Z.of_nat k)) x22 x25 x27 x28 (Z_to_bv 64 (-1)) (w4se k) op);
      try eassumption; try lia.
    - intros HL m1 buf' y1 y6 y7 y8 y9 y11 y12 y14 y16 y19 y22 y25 y27 y28 MU WM MI OUT' LB'.
      assert (LB2 : zlen buf' = dcap) by (rewrite LB'; exact LBF).
      pose proof (w4f_wr mm m1 _ _ _ _ _ op 1 buf' HF ltac:(lia) ltac:(lia) MU WM MI OUT' LB2) as HF'.
      eapply w4f_st; [eapply (IH HL m1) | ..]; try (lazymatch goal with |- @eq _ _ _ => w4f_eq end); try eassumption; try lia.
      do 26 eexists. exact HF'.
    - intros HL m1 buf' y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y16 y19 y22 y25 y27 y28 MU WM MI OUT' LB'.
      assert (LB2 : zlen buf' = dcap) by (rewrite LB'; exact LBF).
      pose proof (w4f_wr mm m1 _ _ _ _ _ op 1 buf' HF ltac:(lia) ltac:(lia) MU WM MI OUT' LB2) as HF'.
      eapply w4f_st; [eapply (KE m1) | ..]; try (lazymatch goal with |- @eq _ _ _ => w4f_eq end); try eassumption; try lia.
      do 26 eexists. exact HF'.
  Time Qed.

  Lemma w4f_tail : forall k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3,
    W4KFEND k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 -> W4KFT k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3.
  Proof.
    intros k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 KE.
    assert (G : forall nn op, (Z.to_nat (w4se k - op) <= nn)%nat -> W4KFTo k i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 c0 c1 c2 c3 op).
    { induction nn as [|nn IHn]; intros op HN.
      - intros mm x1 x6 x7 x8 x9 x11 x12 x14 x16 x19 x22 x25 x27 x28 HM HSR HK HOP HO. exfalso. lia.
      - apply w4f_t1; [exact KE |]. intros HL. apply IHn. lia. }
    intros mm op. exact (G _ op (Nat.le_refl _) mm).
  Time Qed.

End W4FIN.
End CANSEC1.
