(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import Tac ZBridge.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.TUX Require Import DgBaseU.
Set Default Proof Mode "Classic".
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DG.
Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable F : bvmap 5 word.
Variable fc : bv 32.
Variable m0 : word -> option byte.
Variables buf lenp kp : Z.
Local Notation SP0 := (DgBaseU.SP0 sp).
Hypothesis BUFR : (4096 <= buf /\ buf + 21 <= 2^47)%Z.
Hypothesis LENR : (4096 <= lenp /\ lenp + 4 <= 2^47)%Z.
Hypothesis KPR : (4096 <= kp /\ kp + 4 <= 2^47)%Z.
Hypothesis SPR0 : (2^40 <= SP0 /\ SP0 + 8 <= 2^47)%Z.
Hypothesis SEP_B : (buf + 21 <= SP0 - 64 \/ SP0 + 8 <= buf)%Z.
Hypothesis SEP_L : (lenp + 4 <= SP0 - 64 \/ SP0 + 8 <= lenp)%Z.
Hypothesis SEP_K : (kp + 4 <= SP0 - 64 \/ SP0 + 8 <= kp)%Z.
Hypothesis SEP_BL : (buf + 21 <= lenp \/ lenp + 4 <= buf)%Z.
Hypothesis SEP_BK : (buf + 21 <= kp \/ kp + 4 <= buf)%Z.
Hypothesis SEP_LK : (lenp + 4 <= kp \/ kp + 4 <= lenp)%Z.
Hypothesis LA : (lenp mod 4 = 0)%Z.
Hypothesis KA : (kp mod 4 = 0)%Z.
Local Notation DG_W := (DgBaseU.DG_W sp buf lenp kp).
Local Notation dg_post := (DgBaseU.dg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 buf lenp kp).
Local Notation dg_mem := (DgBaseU.dg_mem ra sp s0 s1 s2 s3 s4 s5 s6 m0 buf lenp kp).
Local Notation dg_ret' := (DgBaseU.dg_ret' ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 buf lenp kp BUFR LENR KPR SPR0 SEP_B SEP_L SEP_K SEP_BL SEP_BK SEP_LK LA KA).
Ltac dg_mem_tac := unfold DgBaseU.dg_mem, DgBaseU.DG_W; dg_conjs; try eassumption; try (rewrite ?upd_length; assumption).
Ltac dg_mem_intro H := destruct H as (ST & FR & MU & WM & MI & BU & BL & LE & KC); unfold DgBaseU.DG_W in MU.

Hypothesis dg_l2exit : forall (fr len D U Uo unit kappa s Ks : Z) s1' a4' s2' s3' s4' s5' s6' (m : word -> option byte) (bs : list byte),
  dg_mem m len Ks bs -> (2 <= len <= 21)%Z -> (- 2 ^ 31 + 18 <= Ks <= 2 ^ 31 - 3)%Z -> (56 <= s <= 59)%Z ->
  (0 <= fr < U)%Z -> (U < 2 ^ 64)%Z -> U = (Uo * 10)%Z -> (0 <= Uo)%Z -> (0 <= D < 2 ^ 64)%Z -> (0 <= unit < 2 ^ 64)%Z ->
  (-18 <= kappa <= -1)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 64)) gp tp (Z_to_bv 64 kp) (Z_to_bv 64 s) (Z_to_bv 64 fr) (Z_to_bv 64 kappa) s1'
                                  (Z_to_bv 64 D) (Z_to_bv 64 U) (Z_to_bv 64 (2 ^ s)) (Z_to_bv 64 1) a4' (Z_to_bv 64 unit)
                                  (Z_to_bv 64 buf) (Z_to_bv 64 lenp) s2' s3' s4' s5' s6' s7 s8 s9 s10 s11
                                  (Z_to_bv 64 (2 ^ s - 1)) (Z_to_bv 64 Uo) (Z_to_bv 64 10) (Z_to_bv 64 kappa))
                              F (Z_to_bv 64 0x44ee8) fc None m (seg_rom rsegs)).

Lemma dg_loop2 : forall (n : nat) (i p2 len D U unit kap s Ks : Z) s0' s1' a4' s2' t4' s3' s4' s5' s6' (m : word -> option byte) (bs : list byte),
  Z.to_nat (17 - i) = n ->
  dg_mem m len Ks bs -> (1 <= len <= 3 + i)%Z -> (0 <= i <= 17)%Z -> (- 2 ^ 31 + 18 <= Ks <= 2 ^ 31 - 3)%Z ->
  (56 <= s <= 59)%Z -> (U <= p2 < 2 ^ s)%Z -> (2 * 10 ^ i <= U)%Z -> (0 <= D < 2 ^ 64)%Z -> unit = (10 ^ i)%Z -> kap = (- i)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 64)) gp tp (Z_to_bv 64 kp) (Z_to_bv 64 s) (Z_to_bv 64 p2) s0' s1'
                                  (Z_to_bv 64 D) (Z_to_bv 64 U) (Z_to_bv 64 (2 ^ s)) (Z_to_bv 64 1) a4' (Z_to_bv 64 unit)
                                  (Z_to_bv 64 buf) (Z_to_bv 64 lenp) s2' s3' s4' s5' s6' s7 s8 s9 s10 s11
                                  (Z_to_bv 64 (2 ^ s - 1)) t4' (Z_to_bv 64 10) (Z_to_bv 64 kap))
                              F (Z_to_bv 64 0x44e6c) fc None m (seg_rom rsegs)).
Proof using BUFR LENR KPR SPR0 SEP_B SEP_L SEP_K SEP_BL SEP_BK SEP_LK LA KA dg_l2exit.
  induction n as [n IH] using lt_wf_ind.
  intros i p2 len D U unit kap s Ks s0' s1' a4' s2' t4' s3' s4' s5' s6' m bs Hn DM Hlen Hi HKs Hs Hp2 HU HD Hunit Hkap.
  pose proof DM as DM0. destruct DM as (ST & FR & MU & WM & MI & BU & BL & LE & KC). unfold DgBaseU.DG_W in MU. unfold DgBaseU.SP0 in *.
  subst unit kap.
  assert (IDX : dg_idx buf len) by exact I.
  assert (P17 : (10 ^ i <= 10 ^ 17)%Z) by (apply Z.pow_le_mono_r; lia).
  change (10 ^ 17)%Z with 100000000000000000%Z in P17.
  assert (P0 : (1 <= 10 ^ i)%Z) by (pose proof (Z.pow_le_mono_r 10 0 i ltac:(lia) ltac:(lia)) as Q; rewrite Z.pow_0_r in Q; exact Q).
  assert (E1 : (10 ^ (i + 1) = 10 ^ i * 10)%Z) by (rewrite Z.pow_add_r by lia; rewrite Z.pow_1_r; reflexivity).
  assert (Hs4 : s = 56%Z \/ s = 57%Z \/ s = 58%Z \/ s = 59%Z) by lia.
  destruct Hs4 as [-> | [-> | [-> | ->]]].
  all: dg_xstep; dg_solve 12%nat [0x44e6c; 0x44ee8]%Z.
  all: first
    [ dg_at [0x44ee8]%Z;
      l2_landfacts;
      match goal with |- context [(_ mod (2 ^ ?S))%Z] =>
        eapply (dg_l2exit _ _ D _ U _ _ S Ks) end;
      [ dg_mem_tac | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia ]
    | dg_at [0x44e6c]%Z;
      l2_landfacts;
      assert (H18 : (i + 1 <= 17)%Z) by
        (destruct (Z_le_gt_dec (i + 1) 17) as [h | h]; [exact h |]; exfalso;
         pose proof (Z.pow_le_mono_r 10 18 (i + 1) ltac:(lia) ltac:(lia)) as Q; rewrite E1 in Q;
         change (10 ^ 18)%Z with 1000000000000000000%Z in Q; lia);
      match goal with |- context [(_ mod (2 ^ ?S))%Z] =>
        eapply (IH (Z.to_nat (17 - (i + 1))) ltac:(lia) (i + 1)%Z _ _ D _ _ _ S Ks) end;
      [ reflexivity | dg_mem_tac | lia | lia | lia | lia | lia | rewrite E1; lia | lia | rewrite E1; lia | lia ] ].
Qed.

End DG.
