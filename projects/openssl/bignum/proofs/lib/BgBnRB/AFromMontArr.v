(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac ZBridge RzCPS. 
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnSpecs BnMInv BgState BgInv BgLib BgWords.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout R_unwind_chain RT_iface RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnArith BnTac BnMem BnTacX.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr ShiftPure.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnP Require Import BnLeaves.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import LibKitA ARun BnHeapA ImplA ImplAX UnwindA EdgesA AsStruct RtCallA W_cryptoA W_smallA AsStruct2.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require AW_mul_add_words.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnW2 Require W_from_mont_loops.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnR2 Require W_rshift1.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import BnAKitAF BnCallAF W_callsAF.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import UbKit.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import UbStructF.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2252644 => 2
  | 2252652 => 1
  | 2252656 => 2
  | 2252700 => 1
  | 2252704 => 1
  | 2252708 => 2
  | 2252740 => 1
  | 2252748 => 2
  | 2252932 => 2
  | 2252936 => 1
  | 2252940 => 1
  | 2252944 => 2
  | 2252948 => 2
  | 2253064 => 1
  | 2253076 => 2
  | 2253080 => 2
  | 2253120 => 2
  | 2253164 => 2
  | 2253236 => 2
  | 2253240 => 1
  | 2253244 => 1
  | 2253248 => 2
  | 2253360 => 2
  | 2253372 => 2
  | 2253376 => 1
  | 2253380 => 1
  | 2253384 => 1
  | 2253388 => 1
  | 2253392 => 2
  | 2253444 => 1
  | 2253448 => 1
  | 2253452 => 1
  | 2253456 => 1
  | 2253464 => 1
  | 2253468 => 1
  | 2253472 => 2
  | 2253476 => 2
  | 2253504 => 2
  | 2253508 => 1
  | 2253512 => 1
  | 2253516 => 2
  | 2253520 => 2
  | 2253588 => 1
  | 2253592 => 2
  | 2253596 => 1
  | 2253600 => 1
  | 2253604 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).
Local Ltac ub_unfold ::= unfold BnHeapA.ACEIL in *.
Ltac hide_ors := repeat match goal with H : _ \/ _ |- _ => apply hide_intro in H end.
Ltac unhide := repeat match goal with H : hide _ |- _ => apply hide_elim in H end.

Local Notation mixl := OSSVerify.Proofs.openssl.bignum.lib.BgBnW2.W_from_mont_loops.mixl.
Local Notation mixl_length := OSSVerify.Proofs.openssl.bignum.lib.BgBnW2.W_from_mont_loops.mixl_length.
Local Notation mixl_0 := OSSVerify.Proofs.openssl.bignum.lib.BgBnW2.W_from_mont_loops.mixl_0.
Local Notation mixl_all := OSSVerify.Proofs.openssl.bignum.lib.BgBnW2.W_from_mont_loops.mixl_all.
Local Notation mixl_nth := OSSVerify.Proofs.openssl.bignum.lib.BgBnW2.W_from_mont_loops.mixl_nth.
Local Notation mixl_nth_ge := OSSVerify.Proofs.openssl.bignum.lib.BgBnW2.W_from_mont_loops.mixl_nth_ge.
Local Notation mixl_step := OSSVerify.Proofs.openssl.bignum.lib.BgBnW2.W_from_mont_loops.mixl_step.
Local Notation clear_top := OSSVerify.Proofs.openssl.bignum.lib.BgBnW2.W_from_mont_loops.clear_top.
Local Notation clear_top_length := OSSVerify.Proofs.openssl.bignum.lib.BgBnW2.W_from_mont_loops.clear_top_length.
Local Notation clear_top_limbs := OSSVerify.Proofs.openssl.bignum.lib.BgBnW2.W_from_mont_loops.clear_top_limbs.
Local Notation clear_top_nth := OSSVerify.Proofs.openssl.bignum.lib.BgBnW2.W_from_mont_loops.clear_top_nth.
Local Notation clear_top_above := OSSVerify.Proofs.openssl.bignum.lib.BgBnW2.W_from_mont_loops.clear_top_above.
Local Notation select_words_length := OSSVerify.Proofs.openssl.bignum.lib.BgBnW2.W_from_mont_loops.select_words_length.
Local Notation select_words_nth := OSSVerify.Proofs.openssl.bignum.lib.BgBnW2.W_from_mont_loops.select_words_nth.
Local Notation select_words_limbs := OSSVerify.Proofs.openssl.bignum.lib.BgBnW2.W_from_mont_loops.select_words_limbs.
Local Notation sra31_mask := OSSVerify.Proofs.openssl.bignum.lib.BgBnW2.W_from_mont_loops.sra31_mask.
Local Notation mont_carry_eq := OSSVerify.Proofs.openssl.bignum.lib.BgBnW2.W_from_mont_loops.mont_carry_eq.
Local Notation sel_res := OSSVerify.Proofs.openssl.bignum.lib.BgBnW2.W_from_mont_loops.sel_res.
Local Notation sel_res_length := OSSVerify.Proofs.openssl.bignum.lib.BgBnW2.W_from_mont_loops.sel_res_length.
Local Notation sel_res_nth := OSSVerify.Proofs.openssl.bignum.lib.BgBnW2.W_from_mont_loops.sel_res_nth.
Local Notation sel_res_mixl := OSSVerify.Proofs.openssl.bignum.lib.BgBnW2.W_from_mont_loops.sel_res_mixl.
Local Notation mr_step := OSSVerify.Proofs.openssl.bignum.lib.BgBnW2.W_from_mont_loops.mr_step.
Local Notation mr_step_eq := OSSVerify.Proofs.openssl.bignum.lib.BgBnW2.W_from_mont_loops.mr_step_eq.
Local Notation wlimbs_nth := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_rshift1.wlimbs_nth.
Local Notation wlimbs_upd := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_rshift1.wlimbs_upd.

Lemma shad_next : forall a, shad a + 1 = shad (a + 8).
Proof. intros a. unfold shad. Z.div_mod_to_equations. lia. Qed.

Lemma sra31_maskA : forall z x, -2147483648 <= z < 2147483648 -> 0 <= x < 18446744073709551616 ->
  Z.land (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_swrap 32 (bv_unsigned (Z_to_bv 64 z))) 31)))) (bv_unsigned (Z_to_bv 64 x)) = (if z <? 0 then x else 0).
Proof.
  intros z x Hz Hx. rewrite (unsigned_lit x) by exact Hx. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616. apply sra31_mask; assumption.
Qed.

Lemma land64_range : forall a b, 0 <= a < 18446744073709551616 -> 0 <= b -> 0 <= Z.land a b < 18446744073709551616.
Proof.
  intros a b Ha Hb. split; [apply Z.land_nonneg; left; exact (proj1 Ha)|].
  pose proof (OSSVerify.Proofs.openssl.bignum.lib.BgBnW2.W_from_mont_loops.land_le_r b a (proj1 Ha)) as H. rewrite Z.land_comm in H. lia.
Qed.

Lemma sel_machine : forall r p mk, 0 <= r < 18446744073709551616 -> 0 <= p < 18446744073709551616 -> 0 <= mk < 18446744073709551616 ->
  Z.lor (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 r)) (bv_unsigned (Z_to_bv 64 (18446744073709551615 - mk))))))
        (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 p)) (bv_unsigned (Z_to_bv 64 mk)))))
  = Z.lor (Z.land mk p) (Z.land (18446744073709551616 - 1 - mk) r).
Proof.
  intros r p mk Hr Hp Hm.
  rewrite (unsigned_lit r), (unsigned_lit p), (unsigned_lit mk), (unsigned_lit (18446744073709551615 - mk)) by lia.
  rewrite (unsigned_lit (Z.land r _)) by (apply land64_range; lia). rewrite (unsigned_lit (Z.land p _)) by (apply land64_range; lia).
  rewrite Z.lor_comm, (Z.land_comm p mk), (Z.land_comm r). reflexivity.
Qed.

Lemma carry_machine : forall v C old vn, 0 <= v < 18446744073709551616 -> 0 <= C <= 1 -> 0 <= old < 18446744073709551616 -> vn = addw (addw v C) old ->
  Z.land (bv_unsigned (Z_to_bv 64 (Z.lxor (bv_unsigned (v_sltu (Z_to_bv 64 old) (Z_to_bv 64 vn))) 1)))
         (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 (v + C)))) (bv_unsigned (Z_to_bv 64 C)))))
  = (if vn <? old then 1 else if vn =? old then C else 0).
Proof.
  intros v C old vn Hv HC Ho ->.
  pose proof (mont_carry_eq v C old Hv HC Ho) as E. cbn zeta in E. rewrite <- E. clear E.
  rewrite !v_sltu_b2z.
  rewrite (unsigned_lit old) by lia. rewrite (unsigned_lit (addw (addw v C) old)) by (unfold addw, BW; apply Z.mod_pos_bound; lia).
  rewrite (unsigned_lit 0) by lia. rewrite (unsigned_lit C) by lia.
  rewrite (Z_to_bv_unsigned 64 (v + C)). unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
  replace (addw (addw v C) old) with ((v + C + old) mod 18446744073709551616) by (unfold addw, BW; rewrite Zplus_mod_idemp_l; reflexivity).
  assert (C = 0 \/ C = 1) as [-> | ->] by lia;
    destruct (old <? _); destruct (0 <? _); reflexivity.
Qed.

Lemma fm_clearA : forall (Q : machine_state -> Prop) (F : bvmap 5 word) (fc : bv 32)
    (x1 x2 gp tp x7 x8 x9 x10 x12 x18 x19 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (RP : Z) (B : list Z) (rtop mx : nat) (m0 : mem) (K j : nat) (m1 : mem) (x5 x6 : word),
  limbs B -> (mx <= length B)%nat -> Z.of_nat (length B) < 2 ^ 28 -> Z.of_nat rtop < 2 ^ 31 -> (rtop <= length B)%nat ->
  acc bgbsegs m0 RP (8 * Z.of_nat (length B)) -> RP mod 8 = 0 -> (0 <= RP /\ RP + 8 * Z.of_nat (length B) <= 140737488355328) -> 0 < RP ->
  offshW [(RP, RP + 8 * Z.of_nat (length B))] ->
  (j + S K = mx)%nat ->
  munch [(RP, RP + 8 * Z.of_nat (length B))] m0 m1 -> wmono bgbsegs m0 m1 ->
  u64arr bgbsegs m1 RP (wlimbs (mixl j (clear_top B rtop mx) B)) -> mem_inv bgbsegs m1 ->
  (forall (m' : mem) (y5 y6 y15 : word),
      u64arr bgbsegs m' RP (wlimbs (clear_top B rtop mx)) -> munch [(RP, RP + 8 * Z.of_nat (length B))] m0 m' -> wmono bgbsegs m0 m' -> mem_inv bgbsegs m' ->
      evt bgbsegs Q (MS (mkR x1 x2 gp tp y5 y6 x7 x8 x9 x10 (Z_to_bv 64 (RP + 8 * Z.of_nat mx)) x12 (Z_to_bv 64 1) (Z_to_bv 64 1) y15 (Z_to_bv 64 0)
                              (Z_to_bv 64 (RP + 8 * Z.of_nat mx))
                              x18 x19 (Z_to_bv 64 SHB) x21 x22 (Z_to_bv 64 RP) x24 x25 x26 x27 x28 x29 x30 x31)
                         F (Z_to_bv 64 0x2260cc) fc None m' (seg_rom bgbsegs))) ->
  evt bgbsegs Q (MS (mkR x1 x2 gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 (RP + 8 * Z.of_nat j)) x12 (Z_to_bv 64 1) (Z_to_bv 64 1)
                          (Z_to_bv 64 (Z.of_nat j - Z.of_nat rtop)) (Z_to_bv 64 (Z.of_nat (S K))) (Z_to_bv 64 (RP + 8 * Z.of_nat j))
                          x18 x19 (Z_to_bv 64 SHB) x21 x22 (Z_to_bv 64 RP) x24 x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x226084) fc None m1 (seg_rom bgbsegs)).
Proof.
  intros Q F fc x1 x2 gp tp x7 x8 x9 x10 x12 x18 x19 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 RP B rtop mx m0 K.
  induction K as [|K IH]; intros j m1 x5 x6 LB MX L28 RT31 RTB ACC AL BD P0 OFF EJ MU WM U MI KK.
  all: pose proof (clear_top_length B rtop mx MX) as LCT.
  all: assert (LMX : length (mixl j (clear_top B rtop mx) B) = length B) by (apply mixl_length; [exact LCT| clear - EJ MX; lia]).
  all: assert (JR : 0 <= Z.of_nat j /\ Z.of_nat j + 1 <= Z.of_nat (length B)) by (clear - EJ MX; lia).
  all: assert (NTH : nth_error (wlimbs (mixl j (clear_top B rtop mx) B)) (Z.to_nat (Z.of_nat j)) = Some (Z_to_bv 64 (nth j B 0))).
  1,3: rewrite <- (mixl_nth_ge j (clear_top B rtop mx) B j LCT ltac:(clear; lia) ltac:(clear - EJ MX; lia)); apply wlimbs_nth; rewrite LMX; clear - EJ MX; lia.
  all: assert (Rx : 0 <= nth j B 0 < 18446744073709551616) by (rewrite <- BW_lit; apply limbs_nth; exact LB).
  all: unfold SHLO, SHHI in OFF.
  all: assert (PJ : 0 < RP + 8 * Z.of_nat j /\ RP <= RP + 8 * Z.of_nat j /\ RP + 8 * Z.of_nat j < 18446744073709551616 /\ RP < 18446744073709551616) by (clear - P0 BD JR; lia).

  all: apply hide_intro in OFF.

  all: ub.
  all: apply hide_elim in OFF.

  all: do 2 step; shl_limb ACC AL BD (Z.of_nat j); chk0.

  all: pose proof (u64arr_read bgbsegs m1 RP _ (Z.of_nat j) _ (wa (RP + 8 * Z.of_nat j)) U NTH ltac:(clear; lia) eq_refl) as RD; step; clear RD.
  all: do 4 step.

  all: step.

  all: rewrite (sra31_maskA (Z.of_nat j - Z.of_nat rtop) (nth j B 0)) by (clear - L28 RT31 JR Rx; lia).

  all: assert (Ev : (if Z.of_nat j - Z.of_nat rtop <? 0 then nth j B 0 else 0) = nth j (clear_top B rtop mx) 0)
         by (rewrite clear_top_nth by (clear - EJ MX; lia);
             destruct (Z.ltb_spec (Z.of_nat j - Z.of_nat rtop) 0); destruct (Nat.ltb_spec j rtop); try reflexivity; exfalso; lia).
  all: rewrite Ev.
  all: assert (IDX : 0 <= Z.of_nat j < Z.of_nat (length (wlimbs (mixl j (clear_top B rtop mx) B)))) by (rewrite wlimbs_len, LMX; clear - JR; lia).
  all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
         pose proof (u64arr_store_ok bgbsegs mq RP _ (Z.of_nat j) (wa (RP + 8 * Z.of_nat j)) U IDX eq_refl) as SOKW;
         pose proof (u64arr_write bgbsegs mq RP _ (Z.of_nat j) (Z_to_bv 64 (nth j (clear_top B rtop mx) 0)) U IDX) as U2 end.
  all: rewrite Nat2Z.id, mixl_step in U2 by (rewrite ?LCT; clear - EJ MX; lia).
  all: assert (KR : RP <= RP + 8 * Z.of_nat j /\ RP + 8 * Z.of_nat j + 8 <= RP + 8 * Z.of_nat (length B)) by (clear - JR; lia).
  all: clear U; step; store_done.

  all: step.
  all: step; if_cases KE; zify_cond KE; rewrite ?unsigned_lit in KE by (clear - L28 EJ MX; lia).
  -   exfalso. clear - KE. lia.
  -
    assert (EM : S j = mx) by (clear - EJ; lia).
    setreg 11%Z (Z_to_bv 64 (RP + 8 * Z.of_nat mx)) ltac:(f_equal; clear - EM; lia).
    setreg 17%Z (Z_to_bv 64 (RP + 8 * Z.of_nat mx)) ltac:(f_equal; clear - EM; lia).
    setreg 16%Z (Z_to_bv 64 0) ltac:(f_equal; clear; lia).
    rewrite EM, clear_top_above in U2 by (clear - MX RTB; lia).
    eapply KK; [exact U2| eassumption| eassumption| assumption].
  -
    setreg 11%Z (Z_to_bv 64 (RP + 8 * Z.of_nat (S j))) ltac:(f_equal; clear; lia).
    setreg 17%Z (Z_to_bv 64 (RP + 8 * Z.of_nat (S j))) ltac:(f_equal; clear; lia).
    setreg 16%Z (Z_to_bv 64 (Z.of_nat (S K))) ltac:(f_equal; clear; lia).
    setreg 15%Z (Z_to_bv 64 (Z.of_nat (S j) - Z.of_nat rtop)) ltac:(f_equal; clear; lia).
    eapply (IH (S j)); [exact LB| exact MX| exact L28| exact RT31| exact RTB| exact ACC| exact AL| exact BD| exact P0| cbn [offshW]; unfold SHLO, SHHI; exact OFF
                       | clear - EJ; lia| eassumption| eassumption| exact U2| assumption|].
    intros m' y5 y6 y15 U' MU' WM' MI'. eapply KK; [exact U'| exact MU'| exact WM'| exact MI'].
  -   exfalso. clear - KE. lia.
Qed.

Lemma fm_selectA : forall (Q : machine_state -> Prop) (F : bvmap 5 word) (fc : bv 32)
    (x1 x2 gp tp x8 x10 x19 x22 x23 x24 x25 x26 x27 x30 x31 : word)
    (RPr AP mk : Z) (R P : list Z) (nl : nat) (m0 : mem) (K j : nat) (m1 : mem) (x7 x11 x12 x28 x29 : word),
  limbs R -> limbs P -> length P = nl -> (nl <= length R)%nat -> Z.of_nat (length R) < 2 ^ 28 -> 0 <= mk < 18446744073709551616 ->
  (AP + 8 * Z.of_nat nl <= RPr \/ RPr + 8 * Z.of_nat (length R) <= AP) ->
  acc bgbsegs m0 RPr (8 * Z.of_nat nl) -> RPr mod 8 = 0 -> (0 <= RPr /\ RPr + 8 * Z.of_nat nl <= 140737488355328) -> 0 < RPr ->
  acc bgbsegs m0 AP (8 * Z.of_nat nl) -> AP mod 8 = 0 -> (0 <= AP /\ AP + 8 * Z.of_nat nl <= 140737488355328) -> 0 < AP ->
  offshW [(RPr, RPr + 8 * Z.of_nat nl); (AP, AP + 8 * Z.of_nat nl)] ->
  (j + S K = nl)%nat ->
  munch [(RPr, RPr + 8 * Z.of_nat nl); (AP, AP + 8 * Z.of_nat nl)] m0 m1 -> wmono bgbsegs m0 m1 ->
  u64arr bgbsegs m1 RPr (wlimbs (mixl j (sel_res mk R P nl) R)) -> u64arr bgbsegs m1 AP (wlimbs (mixl j (repeat 0 nl) P)) -> mem_inv bgbsegs m1 ->
  (forall (m' : mem) (y7 y11 y12 y28 y29 : word),
      u64arr bgbsegs m' RPr (wlimbs (sel_res mk R P nl)) -> u64arr bgbsegs m' AP (wlimbs (repeat 0 nl)) ->
      munch [(RPr, RPr + 8 * Z.of_nat nl); (AP, AP + 8 * Z.of_nat nl)] m0 m' -> wmono bgbsegs m0 m' -> mem_inv bgbsegs m' ->
      evt bgbsegs Q (MS (mkR x1 x2 gp tp (Z_to_bv 64 (18446744073709551616 - 1 - mk)) (Z_to_bv 64 1) y7 x8 (Z_to_bv 64 RPr) x10 y11 y12
                              (Z_to_bv 64 (8 * Z.of_nat nl)) (Z_to_bv 64 mk) (Z_to_bv 64 (18446744073709551615 - AP)) (Z_to_bv 64 1) (Z_to_bv 64 0)
                              (Z_to_bv 64 AP) x19 (Z_to_bv 64 SHB) (Z_to_bv 64 (8 * Z.of_nat nl))
                              x22 x23 x24 x25 x26 x27 y28 y29 x30 x31)
                         F (Z_to_bv 64 0x226348) fc None m' (seg_rom bgbsegs))) ->
  evt bgbsegs Q (MS (mkR x1 x2 gp tp (Z_to_bv 64 (18446744073709551616 - 1 - mk)) (Z_to_bv 64 1) x7 x8 (Z_to_bv 64 RPr) x10 x11 x12
                          (Z_to_bv 64 (8 * Z.of_nat j)) (Z_to_bv 64 mk) (Z_to_bv 64 (18446744073709551615 - AP)) (Z_to_bv 64 1) (Z_to_bv 64 0)
                          (Z_to_bv 64 AP) x19 (Z_to_bv 64 SHB) (Z_to_bv 64 (8 * Z.of_nat nl))
                          x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x2262a0) fc None m1 (seg_rom bgbsegs)).
Proof.
  intros Q F fc x1 x2 gp tp x8 x10 x19 x22 x23 x24 x25 x26 x27 x30 x31 RPr AP mk R P nl m0 K.
  induction K as [|K IH]; intros j m1 x7 x11 x12 x28 x29 LR LP LENP LENR L28 MK DJ ACR ALR BDR PR0 ACP ALP BDP PP0 OFF EJ MU WM UR UP MI KK.
  all: assert (NL : (1 <= nl)%nat) by (clear - EJ; lia).
  all: pose proof (sel_res_length mk R P nl NL LENP LENR) as LS.
  all: assert (LMR : length (mixl j (sel_res mk R P nl) R) = length R) by (apply mixl_length; [exact LS| clear - EJ LENR; lia]).
  all: assert (LMP : length (mixl j (repeat 0 nl) P) = length P) by (apply mixl_length; [rewrite repeat_length; symmetry; exact LENP| clear - EJ LENP; lia]).
  all: assert (JR : 0 <= Z.of_nat j /\ Z.of_nat j + 1 <= Z.of_nat nl /\ Z.of_nat nl <= Z.of_nat (length R)) by (clear - EJ LENR; lia).
  all: assert (Rx : 0 <= nth j P 0 < 18446744073709551616) by (rewrite <- BW_lit; apply limbs_nth; exact LP).
  all: assert (Ry : 0 <= nth j R 0 < 18446744073709551616) by (rewrite <- BW_lit; apply limbs_nth; exact LR).
  all: assert (NTHP : nth_error (wlimbs (mixl j (repeat 0 nl) P)) (Z.to_nat (Z.of_nat j)) = Some (Z_to_bv 64 (nth j P 0))).
  1,3: rewrite <- (mixl_nth_ge j (repeat 0 nl) P j ltac:(rewrite repeat_length; symmetry; exact LENP) ltac:(clear; lia) ltac:(clear - EJ LENP; lia));
       apply wlimbs_nth; rewrite LMP; clear - EJ LENP; lia.
  all: assert (NTHR : nth_error (wlimbs (mixl j (sel_res mk R P nl) R)) (Z.to_nat (Z.of_nat j)) = Some (Z_to_bv 64 (nth j R 0))).
  1,3: rewrite <- (mixl_nth_ge j (sel_res mk R P nl) R j LS ltac:(clear; lia) ltac:(clear - EJ LENR; lia)); apply wlimbs_nth; rewrite LMR; clear - EJ LENR; lia.
  all: unfold SHLO, SHHI in OFF.
  all: pose proof (u64arr_bound bgbsegs _ _ _ UR) as UBR; rewrite wlimbs_len, LMR in UBR.
  all: assert (PJ : 0 < AP + 8 * Z.of_nat j /\ AP + 8 * Z.of_nat j < 140737488355328 /\ 0 < RPr + 8 * Z.of_nat j /\ RPr + 8 * Z.of_nat j < 140737488355328
                    /\ 0 <= 8 * Z.of_nat j < 140737488355328) by (clear - PR0 PP0 BDR BDP JR; lia).
  all: apply hide_intro in OFF; apply hide_intro in DJ.

  all: ub.

  all: apply hide_elim in OFF.
  all: step; rewrite ?(unsigned_lit AP), ?(unsigned_lit (8 * Z.of_nat j)) by (clear - PJ BDP; lia).
  all: do 2 step; shl_limb ACP ALP BDP (Z.of_nat j); chk0.

  all: step; rewrite ?(unsigned_lit RPr), ?(unsigned_lit (8 * Z.of_nat j)) by (clear - PJ BDR; lia).
  all: apply hide_intro in OFF.
  all: ub.
  all: apply hide_elim in OFF.
  all: do 2 step; shl_limb ACR ALR BDR (Z.of_nat j); chk0.

  all: pose proof (u64arr_read bgbsegs m1 AP _ (Z.of_nat j) _ (wa (AP + 8 * Z.of_nat j)) UP NTHP ltac:(clear; lia) eq_refl) as RD; step; clear RD.
  all: pose proof (u64arr_read bgbsegs m1 RPr _ (Z.of_nat j) _ (wa (RPr + 8 * Z.of_nat j)) UR NTHR ltac:(clear; lia) eq_refl) as RD; step; clear RD.
  all: do 3 step.

  all: rewrite (sel_machine (nth j R 0) (nth j P 0) mk Ry Rx MK).
  all: rewrite <- (sel_res_nth mk R P nl NL LENP LENR j) by (clear - EJ; lia).

  all: apply hide_elim in DJ.
  all: assert (IDXR : 0 <= Z.of_nat j < Z.of_nat (length (wlimbs (mixl j (sel_res mk R P nl) R)))) by (rewrite wlimbs_len, LMR; clear - JR; lia).
  all: assert (KR : RPr <= RPr + 8 * Z.of_nat j /\ RPr + 8 * Z.of_nat j + 8 <= RPr + 8 * Z.of_nat nl) by (clear - JR; lia).
  all: assert (KP : AP <= AP + 8 * Z.of_nat j /\ AP + 8 * Z.of_nat j + 8 <= AP + 8 * Z.of_nat nl) by (clear - JR; lia).
  all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
         pose proof (u64arr_store_ok bgbsegs mq RPr _ (Z.of_nat j) (wa (RPr + 8 * Z.of_nat j)) UR IDXR eq_refl) as SOKW;
         pose proof (u64arr_write bgbsegs mq RPr _ (Z.of_nat j) (Z_to_bv 64 (nth j (sel_res mk R P nl) 0)) UR IDXR) as UR2;
         pose proof (u64arr_frame bgbsegs mq AP _ (RPr + 8 * Z.of_nat j) (le8 (Z_to_bv 64 (nth j (sel_res mk R P nl) 0))) UP ltac:(clear - BDR JR; lia)
                       ltac:(rewrite length_le8; clear - BDR JR; lia)
                       ltac:(rewrite length_le8, wlimbs_len, LMP, LENP; clear - DJ JR; lia)) as UP2 end.
  all: rewrite Nat2Z.id, mixl_step in UR2 by (rewrite ?LS; clear - EJ LENR; lia).
  all: clear UR UP; step; store_done.

  all: shl_limb ACP ALP BDP (Z.of_nat j); chk0.
  all: step.
  all: assert (IDXP : 0 <= Z.of_nat j < Z.of_nat (length (wlimbs (mixl j (repeat 0 nl) P)))) by (rewrite wlimbs_len, LMP, LENP; clear - JR; lia).
  all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
         pose proof (u64arr_store_ok bgbsegs mq AP _ (Z.of_nat j) (wa (AP + 8 * Z.of_nat j)) UP2 IDXP eq_refl) as SOKW2;
         pose proof (u64arr_write bgbsegs mq AP _ (Z.of_nat j) (Z_to_bv 64 0) UP2 IDXP) as UP3;
         pose proof (u64arr_frame bgbsegs mq RPr _ (AP + 8 * Z.of_nat j) (le8 (Z_to_bv 64 0)) UR2 ltac:(clear - BDP JR; lia)
                       ltac:(rewrite length_le8; clear - BDP JR; lia)
                       ltac:(rewrite length_le8, wlimbs_len, mixl_length by (rewrite ?LS; clear - EJ LENR; lia); clear - DJ JR; lia)) as UR3 end.
  all: clear UR2 UP2; step; change (Z_to_le_bytes 8 0) with (le8 (Z_to_bv 64 0)); store_done.
  all: rewrite Nat2Z.id in UP3; replace (Z_to_bv 64 0) with (Z_to_bv 64 (nth j (repeat 0 nl) 0)) in UP3 by (rewrite nth_repeat; reflexivity).
  all: rewrite mixl_step in UP3 by (rewrite ?repeat_length; clear - EJ LENP; lia).

  all: step; if_cases KE; zify_cond KE; rewrite ?unsigned_lit in KE by (clear - L28 EJ LENR; lia).
  - exfalso. clear - KE EJ. lia.
  -
    assert (EM : S j = nl) by (clear - EJ; lia).
    step.
    setreg 13%Z (Z_to_bv 64 (8 * Z.of_nat nl)) ltac:(f_equal; clear - EM; lia).
    rewrite EM, (sel_res_mixl mk R P nl NL LENP LENR) in UR3. rewrite EM, mixl_all in UP3 by (rewrite ?repeat_length; clear - LENP; lia).
    eapply KK; [exact UR3| exact UP3| eassumption| eassumption| assumption].
  -
    setreg 13%Z (Z_to_bv 64 (8 * Z.of_nat (S j))) ltac:(f_equal; clear; lia).
    eapply (IH (S j)); [exact LR| exact LP| exact LENP| exact LENR| exact L28| exact MK| exact DJ| exact ACR| exact ALR| exact BDR| exact PR0| exact ACP| exact ALP| exact BDP| exact PP0
                       | cbn [offshW]; unfold SHLO, SHHI; exact OFF| clear - EJ; lia| eassumption| eassumption| exact UR3| exact UP3| assumption|].
    intros m' y7 y11 y12 y28 y29 UR' UP' MU' WM' MI'. eapply KK; [exact UR'| exact UP'| exact MU'| exact WM'| exact MI'].
  - exfalso. clear - KE EJ. lia.
Qed.

Section ReduceA.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m0 : mem) (lo RP NP n0 : Z) (np : list Z) (nl LB : nat) (c0 c1 c2 c3 c4 : word).
  Notation FB := (bv_unsigned sp + -160).
  Notation W := [(RP, RP + 8 * (2 * Z.of_nat nl)); (FB - 128, FB)]%Z.
  Hypothesis LNP : limbs np.
  Hypothesis LENNP : length np = nl.
  Hypothesis NL : (1 <= nl)%nat.
  Hypothesis LB2 : (2 * nl <= LB)%nat.
  Hypothesis LB28 : Z.of_nat LB < 2 ^ 28.
  Hypothesis N0 : 0 <= n0 < 18446744073709551616.
  Hypothesis DJ : NP + 8 * Z.of_nat nl <= RP \/ RP + 8 * Z.of_nat LB <= NP.
  Hypothesis LO : lo <= FB - 128.
  Hypothesis LOSH : SHHI <= lo.
  Hypothesis SEPR : RP + 8 * Z.of_nat LB <= FB - 128.
  Hypothesis SEPN : NP + 8 * Z.of_nat nl <= FB - 128.
  Hypothesis ACR : acc bgbsegs m0 RP (8 * Z.of_nat LB).
  Hypothesis ALR : RP mod 8 = 0.
  Hypothesis BDR : 0 <= RP /\ RP + 8 * Z.of_nat LB <= 140737488355328.
  Hypothesis ACN : acc bgbsegs m0 NP (8 * Z.of_nat nl).
  Hypothesis ALN : NP mod 8 = 0.
  Hypothesis BDN : 0 <= NP /\ NP + 8 * Z.of_nat nl <= 140737488355328.
  Hypothesis PR0 : 0 < RP.
  Hypothesis PN0 : 0 < NP.
  Hypothesis OFFR : RP + 8 * Z.of_nat LB <= SHLO \/ SHHI <= RP.
  Hypothesis SHBM : forall m', munch W m0 m' -> shb_cells bgbsegs g_GOT_shadow_offset_cell g_shadow_memory_dynamic_address m'.
  Hypothesis SPHI : bv_unsigned sp <= 140737488355328.

  Definition RBA (m1 : mem) (B : list Z) : Prop :=
    limbs B /\ length B = LB /\ limbs_at bgbsegs m1 RP B /\ limbs_at bgbsegs m1 NP np /\ wr_at bgbsegs m1 RP (8 * Z.of_nat LB)
    /\ stk bgbsegs m1 lo FB /\ mem_inv bgbsegs m1 /\ munch W m0 m1 /\ wmono bgbsegs m0 m1
    /\ rw_cells bgbsegs m1 FB [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 (Z_to_bv 64 NP); C8 (Z_to_bv 64 (Z.of_nat nl))].

  Lemma RBA_init : forall B, limbs B -> length B = LB -> u64arr bgbsegs m0 RP (wlimbs B) -> limbs_at bgbsegs m0 NP np -> stk bgbsegs m0 lo FB -> mem_inv bgbsegs m0 ->
    rw_cells bgbsegs m0 FB [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 (Z_to_bv 64 NP); C8 (Z_to_bv 64 (Z.of_nat nl))] -> RBA m0 B.
  Proof.
    intros B L1 L2 U HN ST MI FR. apply limbarr_limbs_at in U. destruct U as [HB WB]. rewrite L2 in WB.
    split; [exact L1|]. split; [exact L2|]. split; [exact HB|]. split; [exact HN|]. split; [exact WB|]. split; [exact ST|]. split; [exact MI|].
    split; [apply munch_refl|]. split; [apply wmono_refl| exact FR].
  Qed.

  Lemma offW : offshW W.
  Proof. cbn [offshW]. unfold SHLO, SHHI in *. split; [clear - OFFR LB2; lia|]. split; [clear - LO LOSH; lia| exact I]. Qed.

  Lemma rba_upd : forall m1 B k v ad,
    RBA m1 B -> (k < 2 * nl)%nat -> 0 <= v < 18446744073709551616 -> ad = RP + 8 * Z.of_nat k ->
    store_ok bgbsegs m1 (Z_to_bv 64 ad) 8 = true /\
    RBA (write_to_mem m1 (Z_to_bv 64 ad) (le8 (Z_to_bv 64 v))) (upd B k v).
  Proof.
    intros m1 B k v ad (LBl & LenB & HR & HN & WR & ST & MI & MU & WM & FR) Hk Hv ->.
    pose proof (limbs_at_bound _ _ _ _ HN) as BN. rewrite LENNP in BN.
    destruct WR as (W0 & W1 & WR'). pose proof (conj W0 (conj W1 WR')) as WR.
    change (2 ^ 64) with 18446744073709551616 in *.
    assert (L8 : length (le8 (Z_to_bv 64 v)) = 8%nat) by apply length_le8.
    assert (SOK : store_ok bgbsegs m1 (Z_to_bv 64 (RP + 8 * Z.of_nat k)) 8 = true).
    { change (Z_to_bv 64 (RP + 8 * Z.of_nat k)) with (wa (RP + 8 * Z.of_nat k)). apply (wr_at_store_ok bgbsegs m1 RP (8 * Z.of_nat LB)); [exact WR | lia | lia]. }
    split; [exact SOK|].
    change (Z_to_bv 64 (RP + 8 * Z.of_nat k)) with (wa (RP + 8 * Z.of_nat k)).
    assert (ER : B = firstn k B ++ [nth k B 0] ++ skipn (S k) B).
    { rewrite app_assoc, <- (OSSVerify.Proofs.openssl.bignum.lib.BgBnW2.W_from_mont_loops.firstn_S_nth B k) by lia. symmetry. apply firstn_skipn. }
    assert (EU : upd B k v = firstn k B ++ [v] ++ skipn (S k) B).
    { unfold upd, splice. cbn [length app]. rewrite Nat.add_1_r. reflexivity. }
    unfold RBA.
    split. { apply upd_limbs; [exact LBl | unfold limb, BW; exact Hv]. }
    split. { rewrite upd_length by lia. exact LenB. }
    split.
    { rewrite EU. rewrite ER in HR. apply limbs_at_app in HR. destruct HR as [H1 H23]. apply limbs_at_app in H23. destruct H23 as [H2 H3].
      rewrite length_firstn in H2, H3. cbn [length] in H3. replace (Nat.min k (length B)) with k in H2, H3 by lia.
      rewrite app_assoc. apply limbs_at_app. split.
      - replace (RP + 8 * Z.of_nat k) with (RP + 8 * Z.of_nat (length (firstn k B))) by (rewrite length_firstn; f_equal; lia).
        apply limbs_at_snoc_write; [exact H1 | rewrite length_firstn; lia].
      - rewrite length_app, length_firstn. cbn [length]. replace (Nat.min k (length B) + 1)%nat with (S k) by lia.
        replace (RP + 8 * Z.of_nat k + 8 * Z.of_nat 1) with (RP + 8 * Z.of_nat (S k)) in H3 by lia.
        apply limbs_at_write_other; [exact H3 | lia | rewrite L8; lia | rewrite L8, length_skipn; lia]. }
    split. { apply limbs_at_write_other; [exact HN | lia | rewrite L8; lia | rewrite L8, LENNP; lia]. }
    split. { apply wr_at_write. exact WR. }
    split. { apply stk_write; [exact ST | lia | rewrite L8; lia]. }
    split. { apply mem_inv_store; [exact MI | rewrite L8; exact SOK]. }
    split. { apply munch_write; [exact MU | lia | rewrite L8; lia | rewrite L8; cbn [inside]; left; lia]. }
    split. { apply wmono_write. exact WM. }
    apply rw_cells_frame; [exact FR | lia | rewrite L8; lia | rewrite L8; cbn [cells_size csize Nat.add]; lia].
  Qed.

  Lemma rba_call : forall m1 m2 B (st : nat) seg,
    RBA m1 B -> (st + length seg <= 2 * nl)%nat ->
    munch [(RP + 8 * Z.of_nat st, RP + 8 * Z.of_nat st + 8 * Z.of_nat (length seg)); (FB - 128, FB)]%Z m1 m2 ->
    wmono bgbsegs m1 m2 -> mem_inv bgbsegs m2 -> limbs_at bgbsegs m2 (RP + 8 * Z.of_nat st) seg -> stk bgbsegs m2 lo FB ->
    limbs seg ->
    RBA m2 (splice B st seg).
  Proof.
    intros m1 m2 B st seg (LBl & LenB & HR & HN & WR & ST & MI & MU & WM & FR) Hst MUc WMc MIc HS STc LS.
    pose proof (limbs_at_bound _ _ _ _ HN) as BN. rewrite LENNP in BN.
    destruct WR as (W0 & W1 & WR'). pose proof (conj W0 (conj W1 WR')) as WR.
    change (2 ^ 64) with 18446744073709551616 in *.
    unfold RBA.
    split. { apply splice_limbs; [exact LBl | exact LS]. }
    split. { rewrite splice_length by lia. exact LenB. }
    split.
    { unfold splice. rewrite <- (firstn_skipn st B) in HR. apply limbs_at_app in HR. destruct HR as [H1 H23].
      rewrite <- (firstn_skipn (length seg) (skipn st B)) in H23. apply limbs_at_app in H23. destruct H23 as [_ H3].
      rewrite !length_firstn, length_skipn, skipn_skipn in H3.
      replace (Nat.min st (length B)) with st in H3 by lia. replace (Nat.min (length seg) (length B - st)) with (length seg) in H3 by lia.
      replace (length seg + st)%nat with (st + length seg)%nat in H3 by lia.
      apply limbs_at_app. split.
      - eapply limbs_at_transport; [exact H1 | exact MUc | cbn [disjoint_from]; rewrite length_firstn; lia].
      - rewrite length_firstn. replace (Nat.min st (length B)) with st by lia. apply limbs_at_app. split; [exact HS|].
        eapply limbs_at_transport; [exact H3 | exact MUc | cbn [disjoint_from]; rewrite length_skipn; lia]. }
    split. { eapply limbs_at_transport; [exact HN | exact MUc | cbn [disjoint_from]; rewrite LENNP; lia]. }
    split. { eapply wr_at_transport; [exact WR | exact WMc]. }
    split; [exact STc|]. split; [exact MIc|].
    split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MUc]. unfold sub_fp. cbn [outside]. intros x Hx. lia. }
    split. { eapply wmono_trans; [exact WM | exact WMc]. }
    eapply rw_cells_transport; [exact FR | exact MUc | exact WMc |]. cbn [disjoint_from cells_size csize Nat.add]. lia.
  Qed.

  Lemma fm_reduce_bodyA : forall (Q : machine_state -> Prop) (i : nat) (m1 : mem) (B : list Z) (C : Z) (cnt : Z)
      (x1 x5 x6 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    (i < nl)%nat -> RBA m1 B -> 0 <= C <= 1 -> 1 <= cnt < 2 ^ 28 ->
    (forall (m2 : mem) (Bn : list Z) (Cn : Z) (y1 y5 y6 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
        mr_step n0 np nl i B C = (Bn, Cn) -> RBA m2 Bn -> 0 <= Cn <= 1 ->
        evt bgbsegs Q (MS (mkR y1 (Z_to_bv 64 FB) gp tp y5 y6 (Z_to_bv 64 (Z.of_nat nl)) sp (Z_to_bv 64 (cnt - 1)) y10 y11 y12 y13 y14 y15 y16 y17
                                (Z_to_bv 64 (-9)) (Z_to_bv 64 (8 * Z.of_nat nl)) (Z_to_bv 64 SHB) (Z_to_bv 64 (18446744073709551615 - RP - 8 * Z.of_nat (S i)))
                                (Z_to_bv 64 (RP + 8 * Z.of_nat (S i))) (Z_to_bv 64 (RP + 8 * Z.of_nat (S i))) (Z_to_bv 64 Cn)
                                (Z_to_bv 64 (shad (RP + 8 * Z.of_nat (S i)))) (Z_to_bv 64 0) (Z_to_bv 64 n0) y28 y29 y30 y31)
                           F (Z_to_bv 64 0x226198) fc None m2 (seg_rom bgbsegs))) ->
    evt bgbsegs Q (MS (mkR x1 (Z_to_bv 64 FB) gp tp x5 x6 (Z_to_bv 64 (Z.of_nat nl)) sp (Z_to_bv 64 cnt) x10 x11 x12 x13 x14 x15 x16 x17
                            (Z_to_bv 64 (-9)) (Z_to_bv 64 (8 * Z.of_nat nl)) (Z_to_bv 64 SHB) (Z_to_bv 64 (18446744073709551615 - RP - 8 * Z.of_nat i))
                            (Z_to_bv 64 (RP + 8 * Z.of_nat i)) (Z_to_bv 64 (RP + 8 * Z.of_nat i)) (Z_to_bv 64 C)
                            (Z_to_bv 64 (shad (RP + 8 * Z.of_nat i))) (Z_to_bv 64 0) (Z_to_bv 64 n0) x28 x29 x30 x31)
                       F (Z_to_bv 64 0x226114) fc None m1 (seg_rom bgbsegs)).
  Proof.
    intros Q i m1 B C cnt x1 x5 x6 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 Hi I HC HCNT KK.
    pose proof I as (LBl & LenB & HR & HN & WR & ST & MI & MU & WM & FR).
    pose proof offW as OFF.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (LO0 : 0 <= lo) by (unfold SHHI in LOSH; clear - LOSH; lia).
    assert (ESP : bv_unsigned (Z_to_bv 64 FB) = FB) by (apply unsigned_lit; clear - LO LO0 SPR; lia).
    assert (NI : nth_error B i = Some (nth i B 0)) by (apply nth_error_nth'; clear - Hi LB2 LenB; lia).
    assert (Rx : 0 <= nth i B 0 < 18446744073709551616) by (rewrite <- BW_lit; apply limbs_nth; exact LBl).
    assert (IR : 0 <= Z.of_nat i /\ Z.of_nat i + Z.of_nat nl + 1 <= Z.of_nat LB /\ 1 <= Z.of_nat nl) by (clear - Hi LB2 NL; lia).
    assert (PI : 0 < RP + 8 * Z.of_nat i /\ RP + 8 * Z.of_nat i + 8 * Z.of_nat nl + 8 <= 140737488355328 /\ 0 <= 8 * Z.of_nat nl < 140737488355328)
      by (clear - PR0 BDR IR; lia).
    apply hide_intro in DJ. apply hide_intro in OFFR.

    ub.

    (let ad := cur_mem_addr in
     pose proof (acc_rd_limb bgbsegs _ m0 m1 RP (Z.of_nat LB) 0 (Z.of_nat i) ad ACR MU OFF ALR BDR eq_refl
                             ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - IR; lia)
                             ltac:(unfold wa; f_equal; f_equal; clear; lia)) as RD); step; clear RD; chk0.

    pose proof (limbs_at_read_nth bgbsegs _ RP B i _ (wa (RP + 8 * Z.of_nat i)) HR NI eq_refl) as RD; step; clear RD.
    step. step.

    step. step. step.

    rewrite (unsigned_lit (nth i B 0)), (unsigned_lit n0) by (clear - Rx N0; lia).

    set (w := mulw (nth i B 0) n0).
    assert (Rw : 0 <= w < 18446744073709551616) by (subst w; unfold mulw, BW; apply Z.mod_pos_bound; clear; lia).
    assert (Ew : bv_unsigned (Z_to_bv 64 (nth i B 0 * n0)) = w) by (subst w; unfold mulw, BW; rewrite Z_to_bv_unsigned; reflexivity).
    assert (Erp : bv_unsigned (Z_to_bv 64 (RP + 8 * Z.of_nat i)) = RP + 8 * Z.of_nat i) by (apply unsigned_lit; clear - BDR IR; lia).
    assert (Enp : bv_unsigned (Z_to_bv 64 NP) = NP) by (apply unsigned_lit; clear - BDN; lia).
    assert (Enl : bv_unsigned (Z_to_bv 64 (Z.of_nat nl)) = Z.of_nat nl) by (apply unsigned_lit; clear - LB28 LB2; lia).
    assert (LS : length (slice B i nl) = length np) by (rewrite slice_length, LENNP by (clear - Hi LB2 LenB; lia); reflexivity).
    pose proof (mul_add_words_spec (slice B i nl) np w (slice_limbs _ _ _ LBl) LNP LS ltac:(unfold limb, BW; exact Rw)) as MSP.
    assert (HRi : limbs_at bgbsegs m1 (RP + 8 * Z.of_nat i) (slice B i nl)).
    { unfold slice. rewrite <- (firstn_skipn i B) in HR. apply limbs_at_app in HR. destruct HR as [_ HR2].
      rewrite <- (firstn_skipn nl (skipn i B)) in HR2. apply limbs_at_app in HR2. destruct HR2 as [HR2 _].
      rewrite length_firstn in HR2. replace (Nat.min i (length B)) with i in HR2 by (clear - Hi LB2 LenB; lia). exact HR2. }
    eapply evt_cut.
    { eapply OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth.AW_mul_add_words.bn_mul_add_words_aspec with (a := np) (r := slice B i nl) (lo := lo) (m := m1).
      - exact LNP.
      - apply slice_limbs. exact LBl.
      - exact LS.
      - rewrite LENNP. clear - LB28 LB2. lia.
      - rewrite Enl, LENNP. reflexivity.
      - rewrite Enp. exact HN.
      - rewrite Erp. exact HRi.
      - rewrite Erp, LENNP. apply (wr_at_sub bgbsegs m1 RP (8 * Z.of_nat LB) (8 * Z.of_nat i) (8 * Z.of_nat nl) WR); clear - IR; lia.
      - rewrite Erp, Enp, LENNP. unfold alias_ok. right. apply hide_elim in DJ. clear - DJ IR. lia.
      - rewrite ESP. exact ST.
      - rewrite ESP. exact LO.
      - rewrite Erp, ESP, LENNP. left. clear - SEPR IR. lia.
      - rewrite Enp, ESP, LENNP. left. clear - SEPN. lia.
      - exact MI.
      - exact (SHBM m1 MU).
      - rewrite Erp, LENNP. eapply acc_sub; [exact (acc_munch bgbsegs _ m0 m1 _ _ ACR MU OFF (proj1 BDR) (proj2 BDR)) | clear - IR; lia | clear - IR; lia].
      - rewrite Enp, LENNP. exact (acc_munch bgbsegs _ m0 m1 _ _ ACN MU OFF (proj1 BDN) (proj2 BDN)).
      - rewrite Erp, Enp, LENNP. unfold aptrs3. split; [clear - ALR; Z.div_mod_to_equations; lia|]. split; [exact ALN|]. split; [clear - ALR; Z.div_mod_to_equations; lia|].
        split; [apply hide_elim in OFFR; unfold SHLO, SHHI in *; clear - OFFR IR; lia| exact LOSH].
      - rewrite Erp, LENNP. intros _. split; [clear - PI; lia | clear - ALR; Z.div_mod_to_equations; lia].
      - rewrite Enp, LENNP. intros _. split; [exact PN0 | exact ALN]. }
    intros ms' PO. unfold OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth.AW_mul_add_words.maw_apost, OSSVerify.Proofs.openssl.bignum.lib.BnW.BnLoop.wl_post in PO.
    destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & HS & STc).
    subst ms'. rewrite Erp, Ew, LENNP, ESP in *. rewrite (ret_pc_even 0x22613c) by (clear; lia).
    destruct (mul_add_words (slice B i nl) np w) as [seg v] eqn:EMA. cbn [fst snd] in *.
    destruct MSP as (Lseg & Eseg & Lv & _). unfold limb, BW in Lv. try rewrite LENNP in Eseg. try rewrite LS, LENNP in Eseg.
    assert (I2 : RBA m2 (splice B i seg)).
    { eapply (rba_call m1 m2 B i seg I); [rewrite Eseg; clear - Hi; lia| rewrite Eseg; replace (FB - 128) with (FB - 128) by reflexivity; exact MUc| exact WMc| exact MIc| exact HS| exact STc| exact Lseg]. }
    clear I HR HN WR ST MI MU WM FR MUc WMc MIc HS STc HRi NI.
    pose proof I2 as (LB0 & LenB0 & HR0 & HN0 & WR0 & ST0 & MI0 & MU0 & WM0 & FR0).

    step.

    ub.
    do 3 step. shl_limb ACR ALR BDR (Z.of_nat i + Z.of_nat nl). chk0.

    step.
    set (B0 := splice B i seg) in *.
    set (old := nth (i + nl) B0 0).
    assert (NI2 : nth_error B0 (i + nl) = Some old) by (subst old; apply nth_error_nth'; clear - Hi LB2 LenB0; lia).
    assert (Ro : 0 <= old < 18446744073709551616) by (subst old; rewrite <- BW_lit; apply limbs_nth; exact LB0).
    (let ad := cur_mem_addr in
     pose proof (limbs_at_read_nth bgbsegs _ RP B0 (i + nl) _ ad HR0 NI2 ltac:(unfold wa; f_equal; clear; lia)) as RD); step; clear RD.
    do 2 step.

    set (vn := addw (addw v C) old).
    assert (Evn : Z_to_bv 64 (old + (v + C)) = Z_to_bv 64 vn).
    { subst vn. unfold addw, BW. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
      rewrite Zplus_mod_idemp_l, Z.mod_mod by (clear; lia). f_equal. clear. lia. }
    rewrite ?(unsigned_lit old) by (clear - Ro; lia).

    rewrite Evn.
    assert (Rvn : 0 <= vn < 18446744073709551616) by (subst vn; unfold addw, BW; apply Z.mod_pos_bound; clear; lia).

    destruct (rba_upd m2 B0 (i + nl) vn (RP + 8 * Z.of_nat i + 8 * Z.of_nat nl) I2 ltac:(clear - Hi; lia) Rvn ltac:(clear; lia)) as [SOK I3].
    step. clear SOK I2 HR0 HN0 WR0 ST0 MI0 MU0 WM0 FR0.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) => let m' := fresh "m" in gen_mem mq m' end.

    ub.
    do 10 step.

    rewrite (carry_machine v C old vn Lv HC Ro eq_refl).
    set (Cn := if vn <? old then 1 else if vn =? old then C else 0).
    assert (HCn : 0 <= Cn <= 1) by (subst Cn; destruct (vn <? old); [clear; lia|]; destruct (vn =? old); clear - HC; lia).
    setreg 9%Z (Z_to_bv 64 (cnt - 1)) ltac:(f_equal; rewrite unsigned_lit by (clear - HCNT; lia); rewrite bn_swrap32_small by (clear - HCNT; lia); clear; lia).
    setreg 22%Z (Z_to_bv 64 (RP + 8 * Z.of_nat (S i))) ltac:(f_equal; clear; lia).
    setreg 25%Z (Z_to_bv 64 (shad (RP + 8 * Z.of_nat (S i)))) ltac:(f_equal; rewrite shad_next; f_equal; clear; lia).
    setreg 21%Z (Z_to_bv 64 (18446744073709551615 - RP - 8 * Z.of_nat (S i))) ltac:(f_equal; clear; lia).

    eapply (KK _ (upd B0 (i + nl) vn) Cn); [| exact I3 | exact HCn].
    unfold OSSVerify.Proofs.openssl.bignum.lib.BgBnW2.W_from_mont_loops.mr_step. fold w. rewrite EMA. reflexivity.
  Qed.

  Lemma fm_reduceA : forall (Q : machine_state -> Prop) (K i : nat) (m1 : mem) (B : list Z) (C cnt : Z)
      (x1 x5 x6 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    (i + S K = nl)%nat -> cnt = Z.of_nat (S K) -> RBA m1 B -> 0 <= C <= 1 ->
    (forall (m2 : mem) (Bn : list Z) (Cn : Z) (y1 y5 y6 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
        mont_reduce_loop np n0 nl (S K) i B C = (Bn, Cn) -> RBA m2 Bn -> 0 <= Cn <= 1 ->
        evt bgbsegs Q (MS (mkR y1 (Z_to_bv 64 FB) gp tp y5 y6 (Z_to_bv 64 (Z.of_nat nl)) sp (Z_to_bv 64 0) y10 y11 y12 y13 y14 y15 y16 y17
                                (Z_to_bv 64 (-9)) (Z_to_bv 64 (8 * Z.of_nat nl)) (Z_to_bv 64 SHB) (Z_to_bv 64 (18446744073709551615 - RP - 8 * Z.of_nat nl))
                                (Z_to_bv 64 (RP + 8 * Z.of_nat nl)) (Z_to_bv 64 (RP + 8 * Z.of_nat nl)) (Z_to_bv 64 Cn)
                                (Z_to_bv 64 (shad (RP + 8 * Z.of_nat nl))) (Z_to_bv 64 0) (Z_to_bv 64 n0) y28 y29 y30 y31)
                           F (Z_to_bv 64 0x22619c) fc None m2 (seg_rom bgbsegs))) ->
    evt bgbsegs Q (MS (mkR x1 (Z_to_bv 64 FB) gp tp x5 x6 (Z_to_bv 64 (Z.of_nat nl)) sp (Z_to_bv 64 cnt) x10 x11 x12 x13 x14 x15 x16 x17
                            (Z_to_bv 64 (-9)) (Z_to_bv 64 (8 * Z.of_nat nl)) (Z_to_bv 64 SHB) (Z_to_bv 64 (18446744073709551615 - RP - 8 * Z.of_nat i))
                            (Z_to_bv 64 (RP + 8 * Z.of_nat i)) (Z_to_bv 64 (RP + 8 * Z.of_nat i)) (Z_to_bv 64 C)
                            (Z_to_bv 64 (shad (RP + 8 * Z.of_nat i))) (Z_to_bv 64 0) (Z_to_bv 64 n0) x28 x29 x30 x31)
                       F (Z_to_bv 64 0x226114) fc None m1 (seg_rom bgbsegs)).
  Proof.
    intros Q K. induction K as [|K IH]; intros i m1 B C cnt x1 x5 x6 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 EI -> I HC KK.
    - eapply (fm_reduce_bodyA Q i m1 B C (Z.of_nat 1)); [clear - EI; lia | exact I | exact HC | clear; lia |].
      intros m2 Bn Cn y1 y5 y6 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 EST I2 HCn.
      step. if_cases KE; zify_cond KE; [exfalso; rewrite ?unsigned_lit in KE by (clear; lia); clear - KE; lia|]. clear KE.
      replace (S i) with nl by (clear - EI; lia).
      setreg 9%Z (Z_to_bv 64 0) ltac:(f_equal; clear; lia).
      eapply (KK m2 Bn Cn); [| exact I2 | exact HCn].
      rewrite mr_step_eq, EST. reflexivity.
    - eapply (fm_reduce_bodyA Q i m1 B C (Z.of_nat (S (S K)))); [clear - EI; lia | exact I | exact HC | clear - EI LB2 LB28; lia |].
      intros m2 Bn Cn y1 y5 y6 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 EST I2 HCn.
      step. if_cases KE; zify_cond KE; [| exfalso; rewrite ?unsigned_lit in KE by (clear - EI LB2 LB28; lia); clear - KE; lia]. clear KE.
      setreg 9%Z (Z_to_bv 64 (Z.of_nat (S K))) ltac:(f_equal; clear; lia).
      eapply (IH (S i) m2 Bn Cn); [clear - EI; lia | reflexivity | exact I2 | exact HCn |].
      intros m3 Bn3 Cn3 z1 z5 z6 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 EL I3 HC3.
      eapply (KK m3 Bn3 Cn3); [| exact I3 | exact HC3].
      rewrite mr_step_eq, EST. exact EL.
  Qed.
End ReduceA.
