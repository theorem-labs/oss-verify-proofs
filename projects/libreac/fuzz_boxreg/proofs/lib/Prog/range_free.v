From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame Step Tac Bytes Arr.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Import Boxreg range_free_c.
Import ListNotations.
Open Scope Z_scope.

Section RF.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (t base nch fabric : Z) (bs : list byte).
  Hypothesis Hbase : -2^31 <= base < 2^31.
  Hypothesis Hnch : 1 <= nch <= 40.
  Hypothesis Hfab : 1 <= fabric <= 40.
  Hypothesis HB : bytes_at rsegs m t bs.
  Hypothesis HL : length bs = 288%nat.
  Hypothesis H1 : boxreg_B1 bs.
  Hypothesis H2 : boxreg_B2 bs.
  Hypothesis H3 : boxreg_B3 bs.

  Notation POST := (fun ms' : machine_state => exists (t0' t1' t2' r a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 r a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m (seg_rom rsegs) /\
         ((r = Z_to_bv 64 1 /\ range_free_ok bs base nch fabric) \/
          (r = Z_to_bv 64 0 /\ ~ range_free_ok bs base nch fabric))).
  Notation ST pc x10 x11 x12 x13 x14 x15 x16 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 x13 x14 x15 x16 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

  Lemma Tb : 0 <= t /\ t + 288 <= 2^64.
  Proof. pose proof (bytes_at_bound rsegs m t bs HB) as R. rewrite HL in R. exact R. Qed.

  Lemma ret0 : forall x11 x12 x13 x14 x15 x16, ~ range_free_ok bs base nch fabric ->
    evt rsegs POST (ST 0x136d4 (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16).
  Proof.
    intros x11 x12 x13 x14 x15 x16 N. step.
    apply evt_done. do 15 eexists. split; [reflexivity|]. right. split; [reflexivity|exact N].
  Qed.

  Lemma ret1 : forall x11 x12 x13 x14 x15 x16, range_free_ok bs base nch fabric ->
    evt rsegs POST (ST 0x136d4 (Z_to_bv 64 1) x11 x12 x13 x14 x15 x16).
  Proof.
    intros x11 x12 x13 x14 x15 x16 OK. step.
    apply evt_done. do 15 eexists. split; [reflexivity|]. left. split; [reflexivity|exact OK].
  Qed.

  Lemma loop : forall k i x15 x16,
    Z.of_nat k = bx_n bs - i -> 0 <= i < bx_n bs -> 0 <= base <= fabric - nch ->
    (forall j, 0 <= j < i -> ~ meets base nch (bx_base bs j) (bx_nch bs j)) ->
    evt rsegs POST (ST 0x136b4 (Z_to_bv 64 1) (Z_to_bv 64 base) (Z_to_bv 64 (nch + base))
                       (Z_to_bv 64 (bx_n bs - i)) (Z_to_bv 64 (t + 12 + 56 * i)) x15 x16).
  Proof.
    pose proof Tb as TB. unfold boxreg_B1 in H1.
    induction k as [|k IH]; intros i x15 x16 Hk Hi Hr P; [lia|].
    destruct (B3_bounds bs i H2 H3 Hi) as (Bb & Bn & Be).
    pose proof (rd4_read m t bs (56 * i + 8) HB ltac:(lia) ltac:(rewrite HL; lia)) as RB.
    pose proof (rd4_read m t bs (56 * i + 12) HB ltac:(lia) ltac:(rewrite HL; lia)) as RN.
    step.
    rewrite lw_rd4 by (apply bsub_length; rewrite ?HL; lia). fold (bx_base bs i).
    step.
    rewrite lw_rd4 by (apply bsub_length; rewrite ?HL; lia). fold (bx_nch bs i).
    step.
    rewrite swrap_add by lia.
    step.
    rewrite lts_lit by lia.
    assert (NEXT : ~ meets base nch (bx_base bs i) (bx_nch bs i) ->
      evt rsegs POST (ST 0x136c8 (Z_to_bv 64 1) (Z_to_bv 64 base) (Z_to_bv 64 (nch + base))
                         (Z_to_bv 64 (bx_n bs - i)) (Z_to_bv 64 (t + 12 + 56 * i))
                         (Z_to_bv 64 (bx_base bs i)) (Z_to_bv 64 (bx_nch bs i + bx_base bs i)))).
    { intros NM. step. step.
      rewrite ?addi_lit.
      step.
      rewrite eqb_lit by lia.
      destruct (Z.eqb_spec (bx_n bs - i + -1) 0) as [Z0|Z1].
      - cbn [negb]. apply ret1. split; [exact Hr|]. intros j Hj.
        destruct (Z.eq_dec j i) as [->|NE]; [exact NM|]. apply P. lia.
      - cbn [negb].
        replace (bx_n bs - i + -1) with (bx_n bs - (i + 1)) by lia.
        replace (t + 12 + 56 * i + 56) with (t + 12 + 56 * (i + 1)) by lia.
        apply (IH (i + 1)); try lia.
        intros j Hj. destruct (Z.eq_dec j i) as [->|NE]; [exact NM|]. apply P. lia. }
    destruct (Z.ltb_spec base (bx_nch bs i + bx_base bs i)) as [Lt|Ge].
    - cbn [negb]. step. rewrite lts_lit by lia.
      destruct (Z.ltb_spec (bx_base bs i) (nch + base)) as [Lt2|Ge2].
      + step. step. apply evt_done. do 15 eexists. split; [reflexivity|]. right. split; [reflexivity|].
        intros [_ OK]. apply (OK i Hi). unfold meets. lia.
      + apply NEXT. unfold meets. lia.
    - cbn [negb]. apply NEXT. unfold meets. lia.
  Qed.

  Lemma entry : forall a0 a1 a2 a3 a4 a5 a6, a0 = Z_to_bv 64 t -> a1 = Z_to_bv 64 base -> a2 = Z_to_bv 64 nch ->
    a3 = Z_to_bv 64 fabric -> evt rsegs POST (ST 0x1368c a0 a1 a2 a3 a4 a5 a6).
  Proof.
    intros a0 a1 a2 a3 a4 a5 a6 -> -> -> ->.
    pose proof Tb as TB. unfold boxreg_B1 in H1.
    step. step. step.
    rewrite lts_lit by lia.
    destruct (Z.ltb_spec base 0) as [Hn|Hp].
    - apply ret0. intros [Hr _]. lia.
    - step.
      rewrite swrap_sub by lia.
      step.
      rewrite lts_lit by lia.
      destruct (Z.ltb_spec (fabric - nch) base) as [Hg|Hl].
      + apply ret0. intros [Hr _]. lia.
      + pose proof (rd4_read m t bs 280 HB ltac:(lia) ltac:(rewrite HL; lia)) as RN.
        step.
        rewrite lw_rd4 by (apply bsub_length; rewrite ?HL; lia). fold (bx_n bs).
        step. step.
        rewrite lts_lit by lia.
        destruct (Z.ltb_spec 0 (bx_n bs)) as [Pos|Npos].
        * cbn [negb]. step.
          rewrite swrap_add by lia.
          step.
          rewrite ?addi_lit.
          replace (bx_n bs) with (bx_n bs - 0) by lia.
          replace (t + 12) with (t + 12 + 56 * 0) by lia.
          apply (loop (Z.to_nat (bx_n bs - 0)) 0); try lia.
        * cbn [negb]. apply ret1. split; [lia|]. intros i Hi. lia.
  Qed.
End RF.

Theorem range_free_holds : range_free_contract.
Proof.
  unfold range_free_contract, RANGE_FREE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
         t base nch fabric bs E0 E1 E2 E3 Hb Hn Hf HB HL B1 B2 B3.
  exact (entry ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m t base nch fabric bs
           Hb Hn Hf HB HL B1 B2 B3 a0 a1 a2 a3 a4 a5 a6 E0 E1 E2 E3).
Qed.
