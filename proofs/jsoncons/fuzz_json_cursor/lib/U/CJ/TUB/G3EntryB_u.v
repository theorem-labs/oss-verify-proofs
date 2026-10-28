(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import Tac ZBridge FP.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.TU Require Import G3Pure_u G3Lem_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.TUB Require Import DgWalkB_u G3PureB_u CeilB_u G3WalkB_u G3SpecB_u.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation rsegs := DgWalkB_u.rsegs.

Lemma swrap32_sub64 : forall x y, (- 2 ^ 31 <= x - y < 2 ^ 31)%Z -> bv_swrap 32 (x mod 18446744073709551616 - y mod 18446744073709551616) = (x - y)%Z.
Proof.
  intros x y H. change 18446744073709551616%Z with (2 ^ 64)%Z. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn -[Z.pow]. change (2 ^ 32 / 2)%Z with (2 ^ 31)%Z.
  rewrite (Z.mod_eq x (2 ^ 64)), (Z.mod_eq y (2 ^ 64)) by lia.
  replace (x - 2 ^ 64 * (x / 2 ^ 64) - (y - 2 ^ 64 * (y / 2 ^ 64)) + 2 ^ 31)%Z
    with (x - y + 2 ^ 31 + (- (2 ^ 32) * (x / 2 ^ 64 - y / 2 ^ 64)) * 2 ^ 32)%Z by (change (2 ^ 64)%Z with (2 ^ 32 * 2 ^ 32)%Z; ring).
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma zbv_sub64 : forall x y, Z_to_bv 64 (x mod 18446744073709551616 - y mod 18446744073709551616) = Z_to_bv 64 (x - y).
Proof. intros x y. apply zbv_eqm. change 18446744073709551616%Z with (2 ^ 64)%Z. rewrite Zminus_mod, !Z.mod_mod, <- Zminus_mod by lia. reflexivity. Qed.

Section G3B3.
Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable F : bvmap 5 word.
Variable m0 : word -> option byte.
Variables buf lenp kp : Z.
Local Notation GSP := (G3WalkB_u.GSP sp).
Hypothesis BUFR : (4096 <= buf /\ buf + 22 <= 2^47)%Z.
Hypothesis SPR0 : (2^41 <= GSP /\ GSP + 16 <= 2^47)%Z.
Hypothesis KPR : (GSP <= kp /\ kp + 8 <= 2^47)%Z.
Hypothesis KL : lenp = (kp + 4)%Z.
Hypothesis KA : (kp mod 4 = 0)%Z.
Hypothesis SEP_B : (buf + 22 <= GSP - 160 \/ GSP <= buf)%Z.
Hypothesis SEP_BK : (buf + 22 <= kp \/ kp + 8 <= buf)%Z.

Local Notation G3_W := (G3WalkB_u.G3_W sp buf lenp kp).
Local Notation g3_post := (G3WalkB_u.g3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 buf lenp kp).
Local Notation L x := (x ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m0 buf lenp kp BUFR SPR0 KPR KL KA SEP_B SEP_BK).
Local Notation g3_tail2 := (L G3SpecB_u.g3_tail2).
Ltac pgoal := match goal with |- ?G => idtac "GOAL:" G end.

Ltac ubr K := zify_cond K;
  repeat first [ rewrite swrap32_modl in K by lia | rewrite swrap32_mod64 in K by lia | rewrite swrap32_small in K by lia ];
  rewrite ?sgn_small in K by lia; ub_norm_in K;
  first [ lia | unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in K; cbn -[Z.pow] in K; change (2 ^ 32 / 2)%Z with (2 ^ 31)%Z in K; lia ].
Ltac ubg := repeat first [ rewrite swrap32_modl by lia | rewrite swrap32_mod64 by lia | rewrite swrap32_small by lia ].

Lemma g3_tail : forall a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s8' fc (m : word -> option byte) (plf ple wf we mif x : Z) (bs : list byte) lj kj j16,
  frm0 fc ->
  stk rsegs m (GSP - 160) (GSP - 96) ->
  rw_cells rsegs m (GSP - 96) [CB 16 j16; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  munch G3_W m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  u8arr rsegs m buf bs -> length bs = 22%nat -> rw_cells rsegs m lenp [C4 lj] -> rw_cells rsegs m kp [C4 kj] ->
  (-1127 <= ple <= 971)%Z -> we = (ple + 1)%Z -> (2 ^ 53 <= plf < 2 ^ 54)%Z -> (2 ^ 52 <= wf < 2 ^ 53)%Z ->
  (9 <= x <= 62)%Z -> (1 <= mif < 2 ^ 54)%Z -> (2 ^ 61 <= mif * 2 ^ x <= wf * 2 ^ 11)%Z -> (wf * 2 ^ 11 <= plf * 2 ^ 10)%Z ->
  evt rsegs g3_post (MS (mkR ra (Z_to_bv 64 (GSP - 96)) gp tp t0' t1' t2' (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
                             (Z_to_bv 64 we) a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 kp) (Z_to_bv 64 wf) (Z_to_bv 64 plf) (Z_to_bv 64 x)
                             (Z_to_bv 64 (ple - 10)) (Z_to_bv 64 mif) s8' s9 s10 s11 t3' t4' t5' t6')
                        F (Z_to_bv 64 0x44298) fc None m (seg_rom rsegs)).
Proof using All.
  intros until j16. intros FRM ST FR MU WM MI BU BL LE KC Hple Hwe Hplf Hwf Hx Hmif Hxm Hxw.
  unfold G3WalkB_u.G3_W in MU. unfold G3WalkB_u.GSP in *.
  assert (Hpx : (2 ^ 9 <= 2 ^ x <= 2 ^ 62)%Z) by (split; apply Z.pow_le_mono_r; lia).
  zstep. zstep. if_cases Kw; [ubr Kw | ]. clear Kw. ubg.
  zstep. zstep. if_cases Kq; [ubr Kq | ]. clear Kq. ubg.
  zstep. zstep. zstep. zstep.

  assert (EA1 : Z_to_bv 64 (18446744073709551557 - (ple - 10 + 64) mod 18446744073709551616) = Z_to_bv 64 (-113 - ple)) by (apply zbv_eqm; clear - Hple; lia).
  assert (EA2 : bv_swrap 32 (18446744073709551557 - (ple - 10 + 64) mod 18446744073709551616) = (-113 - ple)%Z).
  { rewrite (Z.mod_eq (ple - 10 + 64) 18446744073709551616) by (clear; lia).
    replace (18446744073709551557 - (ple - 10 + 64 - 18446744073709551616 * ((ple - 10 + 64) / 18446744073709551616)))%Z
      with (-113 - ple + (4294967296 * (1 + (ple - 10 + 64) / 18446744073709551616)) * 2 ^ 32)%Z by ring.
    rewrite swrap32_mod. apply swrap32_small. clear - Hple; lia. }
  rewrite EA2, EA1. unfold bv_eqb at 1. rewrite Z.eqb_refl. cbn [negb]. clear EA1 EA2.
  zstep. zstep. zstep. if_cases Kb; [ubr Kb | ]. clear Kb. ubg.

  replace (-113 - ple + 63)%Z with (-50 - ple)%Z by lia.
  do 4 zstep.
  zstep.
  assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 96)) = (bv_unsigned sp - 96)%Z) by (apply unsigned_lit; lia).
  eapply evt_cut.
  { eapply (CeilB_u.ceil_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp - 160)).
    all: unfold CeilB_u.CSP; rewrite ?USP.
    all: try lia.
    all: try exact FRM.
    all: try exact MI.
    all: try exact ST.
    fget_simp. reflexivity. }
  cbv beta. intros ms' P. unfold CeilB_u.ceil_post, CeilB_u.CSP in P. rewrite USP in P.
  destruct P as (c0 & c1 & c2 & F2 & fc2 & m2 & -> & HF2 & FRM2 & MUc & WMc & MI2 & ST2).
  lazymatch type of MUc with munch _ ?mm _ => transport_after_call rsegs mm m2 MUc WMc; clear MUc WMc; try clear MI end.
  replace (ret_pc (Z_to_bv 64 0x442d8)) with (Z_to_bv 64 0x442d8) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  eapply g3_tail2; try eassumption; reflexivity.
  Unshelve. unfold CeilB_u.CSP; rewrite USP; clear - SPR0; unfold G3WalkB_u.GSP in SPR0; lia.
Qed.

Lemma g3_loopB : forall (n : nat) (i kA vf a0v a1v plf xv mif s6v : Z) t0' t1' t2' a2' a3' a4' a5' a6' a7' s3' s8' t3' t4' t5' t6' fc (m : word -> option byte) (bs : list byte) lj kj j16,
  Z.to_nat (52 - i) = n ->
  frm0 fc ->
  stk rsegs m (GSP - 160) (GSP - 96) ->
  rw_cells rsegs m (GSP - 96) [CB 16 j16; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  munch G3_W m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  u8arr rsegs m buf bs -> length bs = 22%nat -> rw_cells rsegs m lenp [C4 lj] -> rw_cells rsegs m kp [C4 kj] ->
  (1 <= vf < 2 ^ 52)%Z -> (0 <= i)%Z -> a0v = (-1074 - i)%Z -> a1v = (vf * 2 ^ i)%Z -> (a1v < 2 ^ 52)%Z ->
  (1 <= kA <= 52)%Z -> plf = ((2 * vf + 1) * 2 ^ kA)%Z -> (2 ^ 53 <= plf < 2 ^ 54)%Z -> xv = (kA + 10)%Z -> mif = (2 * vf - 1)%Z -> s6v = (-1075 - kA - 10)%Z ->
  evt rsegs g3_post (MS (mkR ra (Z_to_bv 64 (GSP - 96)) gp tp t0' t1' t2' (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
        (Z_to_bv 64 a0v) (Z_to_bv 64 a1v) a2' a3' a4' a5' a6' a7' (Z_to_bv 64 kp) s3'
        (Z_to_bv 64 plf) (Z_to_bv 64 xv) (Z_to_bv 64 s6v) (Z_to_bv 64 mif) s8' s9 s10 s11 t3' t4' t5' t6')
     F (Z_to_bv 64 0x4427c) fc None m (seg_rom rsegs)).
Proof using All.
  induction n as [n IH] using lt_wf_ind.
  intros i kA vf a0v a1v plf xv mif s6v t0' t1' t2' a2' a3' a4' a5' a6' a7' s3' s8' t3' t4' t5' t6' fc m bs lj kj j16 Hn FRM ST FR MU WM MI BU BL LE KC
         Hvf Hi E0 E1 H6 HkA Ep HpA Ex Em E6.
  assert (Pi : (1 <= 2 ^ i)%Z) by (apply (Z.pow_le_mono_r 2 0 i); lia).
  subst a0v a1v.
  assert (Hi52 : (i < 52)%Z).
  { destruct (Z_lt_le_dec i 52) as [?|L]; [lia|]. assert (2 ^ 52 <= 2 ^ i)%Z by (apply Z.pow_le_mono_r; lia). clear - H H6 Hvf. nia. }
  zstep. zstep. ubg.
  zstep. if_cases Ko; [ubr Ko | ]. clear Ko.
  do 4 zstep.
  rewrite (Z.shiftl_mul_pow2 (vf * 2 ^ i) 12), (Z.shiftl_mul_pow2 (vf * 2 ^ i) 1) by lia.
  if_cases K; zify_cond K.
  -
    assert (Hi51 : (i < 51)%Z).
    { destruct (Z_lt_le_dec i 51) as [?|L]; [lia|]. assert (2 ^ 51 <= 2 ^ i)%Z by (apply Z.pow_le_mono_r; lia). clear - K H Hvf. nia. }
    eapply (IH (Z.to_nat (52 - (i + 1)))); [lia | reflexivity | eassumption .. | | | | | | | | | | ].
    all: try (clear - Hvf; lia).
    all: try (clear - Hi; lia).
    all: try (clear - HkA; lia).
    all: try eassumption.
    + rewrite Z.pow_add_r by lia. ring.
    + clear - K. lia.
  -
    assert (Hw : (2 ^ 52 <= vf * 2 ^ (i + 1) < 2 ^ 53)%Z) by (rewrite Z.pow_add_r by lia; clear - K H6; lia).
    assert (EkA : kA = (i + 1)%Z) by (subst plf; apply (nrm_unique vf); lia).
    subst kA plf xv mif s6v.
    replace (Z_to_bv 64 (vf * 2 ^ i * 2 ^ 1)) with (Z_to_bv 64 (vf * 2 ^ (i + 1))) by (f_equal; rewrite Z.pow_add_r by lia; ring).
    assert (PP : (1 <= 2 ^ (i + 1))%Z) by (apply (Z.pow_le_mono_r 2 0 (i + 1)); lia).
    eapply g3_tail; try eassumption.
    all: try (clear - Hi Hi52; lia).
    all: try (clear - Hvf; lia).
    all: try (replace (2 ^ (i + 1 + 10))%Z with (2 ^ (i + 1) * 2 ^ 10)%Z by (rewrite <- Z.pow_add_r by lia; reflexivity);
              set (P := (2 ^ (i + 1))%Z) in *; clearbody P; clear - HpA Hvf PP; nia).
    all: (set (P := (2 ^ (i + 1))%Z) in *; clearbody P; clear - Hvf PP; nia).
Qed.

Lemma g3_mid : forall (vf ve k E a0v a1v s3v a4v a5v a7v s4v s7v : Z) t0' t1' t2' a6' s5' s6' s8' t3' t4' t5' t6' fc (m : word -> option byte) (bs : list byte) lj kj j16,
  frm0 fc ->
  stk rsegs m (GSP - 160) (GSP - 96) ->
  rw_cells rsegs m (GSP - 96) [CB 16 j16; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  munch G3_W m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  u8arr rsegs m buf bs -> length bs = 22%nat -> rw_cells rsegs m lenp [C4 lj] -> rw_cells rsegs m kp [C4 kj] ->
  (0 <= E <= 2047)%Z -> (0 <= k <= 52)%Z -> (1 <= vf < 2 ^ 53)%Z -> (2 ^ 53 <= (2 * vf + 1) * 2 ^ k < 2 ^ 54)%Z ->
  (E <> 0 -> k = 0 /\ 2 ^ 52 <= vf /\ a0v = ve /\ s3v = vf /\ ve = E - 1075)%Z ->
  (E = 0 -> 1 <= k /\ vf < 2 ^ 52 /\ a1v = vf /\ ve = -1074)%Z ->
  a4v = ve -> a5v = (ve - 1)%Z -> a7v = (ve - 1 - k)%Z -> s4v = ((2 * vf + 1) * 2 ^ k)%Z -> s7v = (2 * vf)%Z ->
  evt rsegs g3_post (MS (mkR ra (Z_to_bv 64 (GSP - 96)) gp tp t0' t1' t2' (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
        (Z_to_bv 64 a0v) (Z_to_bv 64 a1v) (Z_to_bv 64 E) (Z_to_bv 64 vf) (Z_to_bv 64 a4v) (Z_to_bv 64 a5v) a6' (Z_to_bv 64 a7v)
        (Z_to_bv 64 kp) (Z_to_bv 64 s3v) (Z_to_bv 64 s4v) s5' s6' (Z_to_bv 64 s7v) s8' s9 s10 s11 t3' t4' t5' t6')
     F (Z_to_bv 64 0x44224) fc None m (seg_rom rsegs)).
Proof using All.
  intros until j16. intros FRM ST FR MU WM MI BU BL LE KC HE Hk Hvf Hpl HN HS E4 E5 E7 E4s E7s. subst a4v a5v a7v s4v s7v.
  assert (Pk : (1 <= 2 ^ k <= 2 ^ 52)%Z) by (split; [apply (Z.pow_le_mono_r 2 0 k) | apply Z.pow_le_mono_r]; lia).
  assert (Hve : (-1074 <= ve <= 972)%Z) by (destruct (Z.eq_dec E 0) as [E0|E0]; [destruct (HS E0) as (_ & _ & _ & ->); lia | destruct (HN E0) as (_ & _ & _ & _ & ->); lia]).
  zstep. ubg. zstep. if_cases K0; [ubr K0 | ]. clear K0.
  do 2 zstep.
  zstep. if_cases K1; zify_cond K1.
  -
    zstep. zstep.
    rewrite (swrap32_sub64 (ve - 1) (ve - 1 - k + -10)) by lia. rewrite zbv_sub64.
    replace (ve - 1 - (ve - 1 - k + -10))%Z with (k + 10)%Z by lia.
    zstep. unfold bv_eqb at 1. rewrite Z.eqb_refl. cbn [negb].
    zstep. ubg. do 2 zstep. if_cases K3; [zify_cond K3; lia | ]. clear K3.
    do 3 zstep. if_cases K4; zify_cond K4; [ | exfalso; lia ]. clear K4.
    zstep. zstep. if_cases K5; zify_cond K5.
    +
      destruct (HN K5) as (-> & Hv52 & -> & -> & HveE). clear HN HS.
      rewrite Z.pow_0_r in *. rewrite Z.mul_1_r in *.
      replace (Z_to_bv 64 (ve - 1 - 0 + -10)) with (Z_to_bv 64 ((ve - 1) - 10)) by (f_equal; lia).
      replace (Z_to_bv 64 (0 + 10)) with (Z_to_bv 64 10) by reflexivity.
      eapply g3_tail; try eassumption.
      all: lia.
    +
      destruct (HS K5) as (Hk1 & Hv52 & -> & ->). clear HN HS.
      zstep.
      eapply (g3_loopB (Z.to_nat (52 - 0)) 0 k vf); try reflexivity; try eassumption.
      all: rewrite ?Z.pow_0_r; lia.
  -
    assert (E0 : E <> 0%Z) by (intros E0; destruct (HS E0) as (_ & ? & _); lia).
    destruct (HN E0) as (-> & _ & -> & -> & HveE). clear HN HS.
    rewrite Z.pow_0_r in *. rewrite Z.mul_1_r in *.
    zstep. zstep. zstep.
    rewrite (swrap32_sub64 (ve + -2) (ve - 1 - 0 + -10)) by lia. rewrite zbv_sub64.
    replace (ve + -2 - (ve - 1 - 0 + -10))%Z with 9%Z by lia.
    zstep. unfold bv_eqb at 1. rewrite Z.eqb_refl. cbn [negb].
    zstep. ubg. do 2 zstep. if_cases K3; [zify_cond K3; lia | ]. clear K3.
    do 3 zstep. if_cases K4; zify_cond K4; [ exfalso; lia | ]. clear K4.
    do 3 zstep. if_cases K5; zify_cond K5; [ exfalso; lia | ]. clear K5.
    zstep.
    replace (Z_to_bv 64 (ve - 1 - 0 + -10)) with (Z_to_bv 64 ((ve - 1) - 10)) by (f_equal; lia).
    eapply g3_tail; try eassumption.
    all: lia.
Qed.

Lemma g3_loopA : forall (n : nat) (i vf t0v a7v a0v : Z) t1' t2' s3' s4' s5' s6' s8' t3' t4' t5' t6' fc (m : word -> option byte) (bs : list byte) lj kj j16,
  Z.to_nat (52 - i) = n ->
  frm0 fc ->
  stk rsegs m (GSP - 160) (GSP - 96) ->
  rw_cells rsegs m (GSP - 96) [CB 16 j16; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  munch G3_W m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  u8arr rsegs m buf bs -> length bs = 22%nat -> rw_cells rsegs m lenp [C4 lj] -> rw_cells rsegs m kp [C4 kj] ->
  (1 <= vf < 2 ^ 52)%Z -> (0 <= i)%Z -> t0v = ((2 * vf + 1) * 2 ^ i)%Z -> a7v = (-1075 - i)%Z -> (t0v < 2 ^ 53)%Z ->
  evt rsegs g3_post (MS (mkR ra (Z_to_bv 64 (GSP - 96)) gp tp (Z_to_bv 64 t0v) t1' t2' (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
        (Z_to_bv 64 a0v) (Z_to_bv 64 vf) (Z_to_bv 64 0) (Z_to_bv 64 vf) (Z_to_bv 64 (-1074)) (Z_to_bv 64 (-1075)) (Z_to_bv 64 4503599627370496) (Z_to_bv 64 a7v)
        (Z_to_bv 64 kp) s3' s4' s5' s6' (Z_to_bv 64 (2 * vf)) s8' s9 s10 s11 t3' t4' t5' t6')
     F (Z_to_bv 64 0x44208) fc None m (seg_rom rsegs)).
Proof using All.
  induction n as [n IH] using lt_wf_ind.
  intros i vf t0v a7v a0v t1' t2' s3' s4' s5' s6' s8' t3' t4' t5' t6' fc m bs lj kj j16 Hn FRM ST FR MU WM MI BU BL LE KC Hvf Hi E0 E7 H0.
  assert (Pi : (1 <= 2 ^ i)%Z) by (apply (Z.pow_le_mono_r 2 0 i); lia).
  assert (Hi51 : (i <= 51)%Z).
  { destruct (Z_le_gt_dec i 51) as [?|L]; [lia|]. assert (2 ^ 52 <= 2 ^ i)%Z by (apply Z.pow_le_mono_r; lia). clear - E0 H0 H Hvf. nia. }
  subst t0v a7v.
  zstep. ubg. zstep. ubg. zstep. if_cases K0; [ubr K0 | ]. clear K0.
  do 3 zstep.
  rewrite (Z.shiftl_mul_pow2 ((2 * vf + 1) * 2 ^ i) 1) by lia.
  assert (LB := land_bit ((2 * vf + 1) * 2 ^ i) 52 ltac:(lia) ltac:(split; [lia | exact H0])).
  change (2 ^ 52)%Z with 4503599627370496%Z in LB.
  zstep.
  if_cases K; zify_cond K.
  -
    apply LB in K.
    eapply (IH (Z.to_nat (52 - (i + 1)))); [lia | reflexivity | eassumption .. | | | | | ].
    all: try (rewrite Z.pow_add_r by lia; ring).
    all: try (clear - Hvf Hi Hi51; lia).
    all: (clear - K; lia).
  -
    assert (K' : (4503599627370496 <= (2 * vf + 1) * 2 ^ i)%Z) by (destruct (Z_lt_le_dec ((2 * vf + 1) * 2 ^ i) 4503599627370496) as [L|L]; [exfalso; apply K; apply LB; exact L | exact L]).
    rewrite <- (Z_to_bv_bv_unsigned s3').
    eapply (g3_mid vf (-1074) (i + 1) 0); try reflexivity; try eassumption.
    all: try (intros Hc; exfalso; apply Hc; reflexivity).
    all: try (intros _; repeat split; lia).
    all: try (rewrite Z.pow_add_r by lia; ring).
    all: try (rewrite Z.pow_add_r by lia; clear - K' H0; lia).
    all: (clear - Hvf Hi Hi51; lia).
Qed.

Lemma g3_spec : forall t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fc (m : word -> option byte) (b : Z) (bs : list byte) lj kj,
  bv_unsigned (reg_get F 10) = b -> (1 <= b < 2 ^ 63)%Z -> frm0 fc ->
  stk rsegs m (GSP - 160) GSP -> u8arr rsegs m buf bs -> length bs = 22%nat ->
  rw_cells rsegs m lenp [C4 lj] -> rw_cells rsegs m kp [C4 kj] ->
  mem_inv rsegs m -> m = m0 ->
  evt rsegs g3_post (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 buf) (Z_to_bv 64 lenp) (Z_to_bv 64 kp) a3 a4 a5 a6 a7
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x44178) fc None m (seg_rom rsegs)).
Proof using All.
  intros until kj. intros Hb HbR FRM ST BU BL LE KC MI ->.
  pose proof (munch_refl G3_W m0) as MU. pose proof (wmono_refl rsegs m0) as WM. unfold G3WalkB_u.G3_W in MU.
  unfold G3WalkB_u.GSP in *.
  carve_frame 96%nat ST.
  do 12 zstep.
  do 5 zstep.
  set (bw := reg_get F 10) in *.
  do 7 zstep.
  rewrite Hb. rewrite exp_bits by lia. rewrite mant_bits.
  assert (Eb : (b = Z.shiftr b 52 * 2 ^ 52 + b mod 2 ^ 52)%Z) by (rewrite Z.shiftr_div_pow2 by lia; pose proof (Z.div_mod b (2 ^ 52)); lia).
  assert (RE : (0 <= Z.shiftr b 52 <= 2047)%Z) by (rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia | apply Z.lt_succ_r, Z.div_lt_upper_bound; lia]).
  assert (Rmm : (0 <= b mod 2 ^ 52 < 2 ^ 52)%Z) by (apply Z.mod_pos_bound; lia).
  set (E := Z.shiftr b 52) in *. set (mm := (b mod 2 ^ 52)%Z) in *. clearbody E mm.
  replace (bv_unsigned sp + -96)%Z with (bv_unsigned sp - 96)%Z in * by lia.
  if_cases K0; zify_cond K0.
  -
    do 2 zstep. rewrite lor_hidden by lia.
    zstep. if_cases K1; zify_cond K1; [exfalso; lia | ]. clear K1.
    do 6 zstep.
    rewrite (Z.shiftl_mul_pow2 (mm + 4503599627370496) 1) by lia.
    if_cases K2; zify_cond K2; [exfalso; lia | ]. clear K2.
    do 2 zstep.
    eapply (g3_mid (mm + 2 ^ 52) (E + -1075) 0 E); try reflexivity; try eassumption.
    all: try (intros; repeat split; lia).
    all: rewrite ?Z.pow_0_r; lia.
  -
    subst E.
    assert (Hmm : (1 <= mm)%Z) by (clear - Eb HbR; lia).
    zstep. do 2 zstep. rewrite lor_hidden by lia.
    zstep. if_cases K1; zify_cond K1; [ | exfalso; lia ]. clear K1.
    do 5 zstep.
    rewrite (Z.shiftl_mul_pow2 mm 1) by lia. replace (mm * 2 ^ 1)%Z with (2 * mm)%Z by ring.
    if_cases K2; zify_cond K2; [ | exfalso; lia ]. clear K2.
    eapply (g3_loopA (Z.to_nat (52 - 0)) 0 mm); try reflexivity; try eassumption.
    all: rewrite ?Z.pow_0_r; lia.
Qed.

End G3B3.
