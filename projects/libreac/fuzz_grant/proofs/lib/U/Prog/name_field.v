From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import RcModel RcLib RcRec RcRecLib RcBox RcBoxLib.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import memset_c name_field_c.
Import ListNotations.
Open Scope Z_scope.

Section NF.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (wm wn name : word) (nb : list byte).
  Hypothesis Rsp : 32 <= bv_unsigned sp < 2^64.
  Hypothesis Hm288 : bv_unsigned wm + 288 <= 2^64.
  Hypothesis HN16 : bv_unsigned wn + 16 <= 2^64.
  Hypothesis Hname : bv_unsigned name <> 0 -> name_ok nb /\ bv_unsigned name + Z.of_nat (length nb) <= 2^64.
  Hypothesis Dfm : bv_unsigned sp <= bv_unsigned wm + 280 \/ bv_unsigned wm + 288 <= bv_unsigned sp + -32.
  Hypothesis Dfn : bv_unsigned sp <= bv_unsigned name \/ bv_unsigned name + Z.of_nat (length nb) <= bv_unsigned sp + -32.
  Hypothesis DfN : bv_unsigned sp <= bv_unsigned wn \/ bv_unsigned wn + 16 <= bv_unsigned sp + -32.
  Hypothesis DNm : bv_unsigned wn + 16 <= bv_unsigned wm + 280 \/ bv_unsigned wm + 288 <= bv_unsigned wn.
  Hypothesis DNn : bv_unsigned wn + 16 <= bv_unsigned name \/ bv_unsigned name + Z.of_nat (length nb) <= bv_unsigned wn.

  Definition Qn : machine_state -> Prop :=
    fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ bytes_at rsegs m' (bv_unsigned wn) (nmf nb)
      /\ munch [(bv_unsigned sp + -32, bv_unsigned sp); (bv_unsigned wn, bv_unsigned wn + 16)] m m'
      /\ wmono rsegs m m'
      /\ mem_inv rsegs m'
      /\ stk rsegs m' (bv_unsigned sp + -32) (bv_unsigned sp).

  Definition ninv (m' : word -> option byte) (cur : list byte) : Prop :=
    wr_at rsegs m' (bv_unsigned wn) 16 /\ length cur = 16%nat /\ bytes_at rsegs m' (bv_unsigned wn) cur /\
    (exists j, rw_cells rsegs m' (bv_unsigned sp + -32) [CB 8 j; C8 s1; C8 s0; C8 ra]) /\
    bytes_at rsegs m' (bv_unsigned wm + 280) (le8 name) /\ bytes_at rsegs m' (bv_unsigned name) nb /\
    munch [(bv_unsigned sp + -32, bv_unsigned sp); (bv_unsigned wn, bv_unsigned wn + 16)] m m' /\
    wmono rsegs m m' /\ mem_inv rsegs m'.

  Lemma epi : forall u0 u1 u2 x10 x11 x12 x13 x14 x15 x16 u7 u3 u4 u5 u6 m',
    ninv m' (nmf nb) ->
    evt rsegs Qn
      (MS (mkR (Z_to_bv 64 86660) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp u0 u1 u2 wn wm
               x10 x11 x12 x13 x14 x15 x16 u7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x152dc) fc None m' (seg_rom rsegs)).
  Proof.
    intros u0 u1 u2 x10 x11 x12 x13 x14 x15 x16 u7 u3 u4 u5 u6 m' (HW & _ & HB & (j & FR) & HM & HNm & MU & WM & MI).
    step. step. step. step. step.
    apply evt_done. unfold Qn. do 15 eexists. exists m'.
    split; [reflexivity|].
    split; [exact HB|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    apply stk_of_rw_cells in FR. cbn [cells_size csize Nat.add] in FR.
    replace (bv_unsigned sp + -32 + Z.of_nat 32) with (bv_unsigned sp) in FR by lia. exact FR.
  Qed.

  Lemma ninv_store : forall m' cur i (c : byte), ninv m' cur -> (i < 16)%nat ->
    ninv (write_to_mem m' (wa (bv_unsigned wn + Z.of_nat i)) [c]) (upd_bytes cur i [c]).
  Proof.
    intros m' cur i c (HW & Hlen & HB & (j & FR) & HM & HNm & MU & WM & MI) Hi.
    pose proof (bytes_at_bound rsegs m' _ _ HB) as BB.
    pose proof (bytes_at_bound rsegs m' _ _ HNm) as BN.
    pose proof (wr_at_store_ok rsegs m' (bv_unsigned wn) 16 (Z.of_nat i) 1 HW ltac:(lia) ltac:(lia)) as HS.
    split; [apply wr_at_write; exact HW|].
    split; [rewrite upd_bytes_length by (cbn [length]; lia); exact Hlen|].
    split.
    { pose proof (bytes_at_write_inside rsegs m' (bv_unsigned wn) cur (Z.of_nat i) [c] HB ltac:(lia)
                    ltac:(rewrite Nat2Z.id; cbn [length]; lia)) as H.
      rewrite Nat2Z.id in H. exact H. }
    split.
    { exists j. apply rw_cells_frame; [exact FR | lia | cbn [length]; lia |].
      cbn [cells_size csize Nat.add length]. lia. }
    split; [apply bytes_at_write_other; [exact HM | lia | cbn [length]; lia | rewrite length_le8; cbn [length]; lia]|].
    split; [apply bytes_at_write_other; [exact HNm | lia | cbn [length]; lia | cbn [length]; lia]|].
    split; [apply munch_write; [exact MU | lia | cbn [length]; lia | cbn [inside length]; right; left; split; lia]|].
    split; [apply wmono_write; exact WM|].
    apply mem_inv_store; [exact MI | exact HS].
  Qed.

  Lemma loop : forall k i u0 u1 u2 x11 x13 x14 x15 x16 u7 u3 u4 u5 u6 m',
    (i + k = 16)%nat -> (0 < k)%nat ->
    bv_unsigned name <> 0 ->
    (forall j, (j < i)%nat -> bv_unsigned (nth j nb (Z_to_bv 8 0)) <> 0) ->
    bv_unsigned x11 = 18446744073709551615 - bv_unsigned wn ->
    ninv m' (firstn i nb ++ repeat (Z_to_bv 8 0) (16 - i)) ->
    evt rsegs Qn
      (MS (mkR (Z_to_bv 64 86660) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp u0 u1 u2 wn wm
               (Z_to_bv 64 (Z.of_nat i)) x11 (Z_to_bv 64 16) x13 x14 x15 x16 u7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x152a0) fc None m' (seg_rom rsegs)).
  Proof.
    induction k as [|k IH]; intros i u0 u1 u2 x11 x13 x14 x15 x16 u7 u3 u4 u5 u6 m' Hik Hk NZ Hnz H11 NI; [lia|].
    destruct (Hname NZ) as (OK & Lnb).
    pose proof (name_ok_lt nb i OK ltac:(lia) Hnz) as Hi.
    pose proof NI as (HW & Hlen & HB & (j & FR) & HM & HNm & MU & WM & MI).
    pose proof (rd_le8 rsegs m' _ name HM) as HR.
    pose proof (rd_byte rsegs m' (bv_unsigned name) nb i HNm Hi) as RD.
    pose proof (zr_word name) as Rn. unfold inr64 in Rn.
    pose proof (zr_word wn) as RN. unfold inr64 in RN.
    step. step. step.
    rewrite (rc_ltu_ge name (Z_to_bv 64 (bv_unsigned name + Z.of_nat i))) by (rewrite unsigned_lit by lia; lia).
    step. step. step. step.
    rewrite (rc_ubchk name (Z_to_bv 64 (bv_unsigned name + Z.of_nat i))) by (try rewrite unsigned_lit by lia; lia).
    step.
    rewrite (rc_neq0w name NZ).
    step. step.
    rewrite rc_zxb_eqb0.
    destruct (Z.eqb_spec (bv_unsigned (nth i nb (Z_to_bv 8 0))) 0) as [C0 | CNZ].
    - cbv iota.
      rewrite <- (nmf_stop nb i Hi ltac:(lia) Hnz C0) in NI.
      apply epi. exact NI.
    - cbv iota.
      step.
      rewrite (rc_ltu_ge (Z_to_bv 64 (Z.of_nat i)) x11) by (rewrite unsigned_lit by lia; lia).
      pose proof (wr_at_store_ok rsegs m' (bv_unsigned wn) 16 (Z.of_nat i) 1 HW ltac:(lia) ltac:(lia)) as HS.
      step. step. step.
      rewrite le1_zxb.
      pose proof (ninv_store m' _ i (nth i nb (Z_to_bv 8 0)) NI ltac:(lia)) as NI'.
      rewrite upd_prefix in NI' by lia.
      step.
      rewrite (rc_eqb_lit (Z.of_nat i + 1) 16) by lia.
      destruct k as [|k].
      + replace (Z.of_nat i + 1 =? 16) with true by (symmetry; apply Z.eqb_eq; lia).
        cbn [negb]. cbv iota.
        assert (L16 : length nb = 16%nat) by (destruct OK as (OKl & _ & _); lia).
        replace (S i) with 16%nat in NI' by lia.
        rewrite <- (nmf_full nb L16) in NI'.
        2:{ intros j' Hj'. destruct (Nat.eq_dec j' i) as [->|Ne]; [exact CNZ | apply Hnz; lia]. }
        apply epi. exact NI'.
      + replace (Z.of_nat i + 1 =? 16) with false by (symmetry; apply Z.eqb_neq; lia).
        cbn [negb]. cbv iota.
        replace (Z.of_nat i + 1) with (Z.of_nat (S i)) by lia.
        apply (IH (S i)); [lia | lia | exact NZ | | exact H11 | exact NI'].
        intros j' Hj'. destruct (Nat.eq_dec j' i) as [->|Ne]; [exact CNZ | apply Hnz; lia].
  Qed.
End NF.

Theorem name_field_holds : memset_contract -> name_field_contract.
Proof.
  intros HMS. unfold name_field_contract, NAME_FIELD.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    name nb junk ST Hm0 Hm8 Hm288 HNW HN16 HN HNB Dfm Dfn DfN DNm DNn MI.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof ST as (Rlo & _ & _).
  assert (HBn : bytes_at rsegs m (bv_unsigned name) nb /\
                (bv_unsigned name <> 0 -> name_ok nb /\ bv_unsigned name + Z.of_nat (length nb) <= 2^64) /\
                (bv_unsigned name = 0 -> nb = [])).
  { destruct HNB as [(E & ->) | (E & OK & L & B)].
    - split; [apply bytes_at_nil; pose proof (zr_word name) as R; unfold inr64 in R; lia|]. split; [tauto|]. auto.
    - split; [exact B|]. split; [auto|]. intros; contradiction. }
  clear HNB. destruct HBn as (HBn & Hname & Hnil).
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (bv_unsigned a1, bv_unsigned a1 + 16)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step.
  carve_frame 32%nat ST.
  clear ST.
  step. step. step. step. step. step. step. step. step.
  eapply evt_cut; [eapply HMS; [exact HN | exact MI] |].
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & E & MU1 & WM1 & MI1 & RW1).
  subst ms'.
  change (bv_unsigned (Z_to_bv 64 16)) with 16 in MU1, RW1.
  change (Z.to_nat 16) with 16%nat in RW1.
  change (bv_unsigned (Z_to_bv 64 0) mod 256) with 0 in RW1.
  transport_after_call rsegs m0 m1 MU1 WM1.
  clear MU1 WM1.
  replace (ret_pc (Z_to_bv 64 86660)) with (Z_to_bv 64 86660) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  destruct RW1 as [[_ HB1] HW1]. cbn [cells_bytes cbytes cells_size csize Nat.add] in HB1, HW1.
  rewrite app_nil_r in HB1.
  assert (NI : ninv ra sp s0 s1 m a0 a1 name nb m1 (repeat (Z_to_bv 8 0) 16)).
  { split; [exact HW1|]. split; [reflexivity|]. split; [exact HB1|]. split; [eexists; eassumption|].
    split; [assumption|]. split; [assumption|]. split; [assumption|]. split; assumption. }
  pose proof (rd_le8 rsegs m1 _ name HNW) as HR.
  step. step.
  replace (Z.land (bv_unsigned a0) 7) with 0
    by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3) with 8; rewrite Hm8; reflexivity).
  if_false.
  step. step.
  destruct (Z.eq_dec (bv_unsigned name) 0) as [Z0 | NZ].
  - rewrite (rc_eq0w name Z0). cbv iota.
    assert (EN : nmf nb = repeat (Z_to_bv 8 0) 16) by (rewrite (Hnil Z0); reflexivity).
    rewrite <- EN in NI.
    eapply epi. all: first [exact NI | eassumption | lia].
  - rewrite (rc_neq0w name NZ). cbv iota.
    step. step. step.
    pose proof (zr_word a1) as RN. unfold inr64 in RN.
    eapply loop with (k := 16%nat) (i := 0%nat); try eassumption; try lia.
    rewrite (zb_lxor_ones (bv_unsigned a1)) by lia. rewrite unsigned_lit by lia. reflexivity.
Qed.
