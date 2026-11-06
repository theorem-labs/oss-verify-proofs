From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes ZBridge Step.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import HeadampModel reac_headamp_tx_set_c.
Import ListNotations.
Open Scope Z_scope.

Lemma length_le1 : forall w, length (le1 w) = 1%nat.
Proof. intros. apply length_Z_to_le_bytes. Qed.

Ltac trap_off H :=
  exfalso; rewrite ?Z.shiftl_mul_pow2 in H by lia; try change (2 ^ 1) with 2 in H;
  rewrite ?Z.mod_small in H by lia; rewrite ?zb_lxor_ones in H by lia; lia.

Ltac set_tail_u t ch p m HW :=
  zstep;
  let HT1 := fresh "HT" in if_cases HT1; zify_cond HT1; [ exfalso; lia | ];
  zstep; zstep;
  let HT2 := fresh "HT" in if_cases HT2; zify_cond HT2;
  [ exfalso; replace (Z.land t 3) with (t mod 4) in HT2
      by (symmetry; change 3 with (Z.ones 2); rewrite Z.land_ones by lia; reflexivity); lia | ];
  zstep; zstep; zstep; zstep;
  let HT3 := fresh "HT" in if_cases HT3; zify_cond HT3; [ trap_off HT3 | ];
  zstep; zstep; zstep; zstep; zstep;
  let HT4 := fresh "HT" in if_cases HT4; zify_cond HT4; [ trap_off HT4 | ];
  zstep; zstep; zstep;
  rewrite ?Z.shiftl_mul_pow2 by lia; try change (2 ^ 1) with 2;
  assert (HS1 : store_ok rsegs m (wa (t + (3 * ch + p))) 1 = true)
    by (apply (wr_at_store_ok rsegs m t 460 (3 * ch + p) 1 HW); lia);
  zstep;
  change (Z_to_bv 64 (t + (3 * ch + p))) with (wa (t + (3 * ch + p)));
  let m1 := fresh "m1" in
  set (m1 := write_to_mem m (wa (t + (3 * ch + p))) _);
  let HW1 := fresh "HW1" in
  assert (HW1 : wr_at rsegs m1 t 460) by (apply wr_at_write; exact HW);
  zstep;
  let HT5 := fresh "HT" in if_cases HT5; zify_cond HT5; [ trap_off HT5 | ];
  zstep; zstep; zstep;
  let HT6 := fresh "HT" in if_cases HT6; zify_cond HT6; [ trap_off HT6 | ];
  zstep; zstep; zstep; zstep;
  assert (HS2 : store_ok rsegs m1 (wa (t + (144 + 3 * ch + p))) 1 = true)
    by (apply (wr_at_store_ok rsegs m1 t 460 (144 + 3 * ch + p) 1 HW1); lia);
  zstep;
  change (Z_to_bv 64 (t + (144 + 3 * ch + p))) with (wa (t + (144 + 3 * ch + p)));
  let m2 := fresh "m2" in
  set (m2 := write_to_mem m1 (wa (t + (144 + 3 * ch + p))) _);
  let HW2 := fresh "HW2" in
  assert (HW2 : wr_at rsegs m2 t 460) by (apply wr_at_write; exact HW1);
  zstep;
  let HT7 := fresh "HT" in if_cases HT7; zify_cond HT7; [ trap_off HT7 | ];
  zstep; zstep; zstep;
  let HT8 := fresh "HT" in if_cases HT8; zify_cond HT8; [ trap_off HT8 | ];
  zstep; zstep; zstep;
  assert (HS3 : store_ok rsegs m2 (wa (t + (288 + 3 * ch + p))) 1 = true)
    by (apply (wr_at_store_ok rsegs m2 t 460 (288 + 3 * ch + p) 1 HW2); lia);
  zstep;
  change (Z_to_bv 64 (t + (288 + 3 * ch + p))) with (wa (t + (288 + 3 * ch + p)));
  let m3 := fresh "m3" in
  set (m3 := write_to_mem m2 (wa (t + (288 + 3 * ch + p))) _);
  let HW3 := fresh "HW3" in
  assert (HW3 : wr_at rsegs m3 t 460) by (apply wr_at_write; exact HW2);
  assert (HS4 : store_ok rsegs m3 (wa (t + 432)) 4 = true)
    by (apply (wr_at_store_ok rsegs m3 t 460 432 4 HW3); lia);
  zstep;
  change (Z_to_bv 64 (t + 432)) with (wa (t + 432));
  zstep; zstep.

Lemma upd_len : forall (T bs : list byte) k n, length T = n -> (k + length bs <= n)%nat -> length (upd_bytes T k bs) = n.
Proof. intros. subst n. apply upd_bytes_length. assumption. Qed.

Ltac set_finish t ch p v T HL HB m1 m2 m3 :=
  assert (L1 : length (upd_bytes T (Z.to_nat (3 * ch + p)) (le1 (Z_to_bv 64 v))) = 460%nat)
    by (apply upd_len; [exact HL | rewrite length_le1; lia]);
  assert (L2 : length (upd_bytes (upd_bytes T (Z.to_nat (3 * ch + p)) (le1 (Z_to_bv 64 v)))
                         (Z.to_nat (144 + 3 * ch + p)) (le1 (Z_to_bv 64 1))) = 460%nat)
    by (apply upd_len; [exact L1 | rewrite length_le1; lia]);
  assert (L3 : length (upd_bytes (upd_bytes (upd_bytes T (Z.to_nat (3 * ch + p)) (le1 (Z_to_bv 64 v)))
                         (Z.to_nat (144 + 3 * ch + p)) (le1 (Z_to_bv 64 1)))
                         (Z.to_nat (288 + 3 * ch + p)) (le1 (Z_to_bv 64 1))) = 460%nat)
    by (apply upd_len; [exact L2 | rewrite length_le1; lia]);
  apply evt_done; do 15 eexists; eexists; split; [reflexivity|];
  split; [reflexivity|];
  split; [|split];
  [ unfold set_T; change 432%nat with (Z.to_nat 432);
    apply bytes_at_write_inside; [ | lia | rewrite length_le4, L3; lia ];
    apply bytes_at_write_inside; [ | lia | rewrite length_le1, L2; lia ];
    apply bytes_at_write_inside; [ | lia | rewrite length_le1, L1; lia ];
    apply bytes_at_write_inside; [ exact HB | lia | rewrite length_le1, HL; lia ]
  | apply munch_write; [ | lia | rewrite length_le4; lia | cbn [inside]; rewrite length_le4; lia ];
    apply munch_write; [ | lia | rewrite length_le1; lia | cbn [inside]; rewrite length_le1; lia ];
    apply munch_write; [ | lia | rewrite length_le1; lia | cbn [inside]; rewrite length_le1; lia ];
    apply munch_write; [ apply munch_refl | lia | rewrite length_le1; lia | cbn [inside]; rewrite length_le1; lia ]
  | repeat apply wmono_write; apply wmono_refl ].

Theorem reac_headamp_tx_set_holds : reac_headamp_tx_set_contract.
Proof.
  unfold reac_headamp_tx_set_contract, REAC_HEADAMP_TX_SET.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m t ch p v T -> -> -> -> HCH HP HV HL HB HW H0 H4.
  pose proof (bytes_at_bound rsegs m t T HB) as Ht. rewrite HL in Ht. change (Z.of_nat 460) with 460 in Ht.
  assert (Ht' : 0 <= t < 2^64) by lia.
  pose proof Ht as Htl. change (2 ^ 64) with 18446744073709551616 in Htl.
  zstep. zstep. zstep.
  if_cases HC1; zify_cond HC1.
  - zstep. zstep. apply evt_done. do 16 eexists. split; [reflexivity|].
    rewrite (proj2 (Z.ltb_ge ch 48)) by lia. cbn [andb]. split; reflexivity.
  - zstep. zstep.
    if_cases HC2; zify_cond HC2.
    + zstep.
      if_cases HC3; zify_cond HC3.
      * zstep. zstep. apply evt_done. do 16 eexists. split; [reflexivity|].
        replace ((ch <? 48) && legalb p v) with false
          by (unfold legalb; rewrite (proj2 (Z.eqb_neq p 2)) by lia;
              rewrite (proj2 (Z.ltb_ge p 2)) by lia; rewrite andb_false_r; reflexivity).
        split; reflexivity.
      * zstep. zstep.
        if_cases HC4; zify_cond HC4.
        -- zstep. zstep. apply evt_done. do 16 eexists. split; [reflexivity|].
           replace ((ch <? 48) && legalb p v) with false
             by (unfold legalb; rewrite (proj2 (Z.eqb_eq p 2)) by lia; rewrite (proj2 (Z.ltb_ge p 2)) by lia;
                 rewrite (proj2 (Z.leb_gt v 55)) by lia; rewrite andb_false_r; reflexivity).
           split; reflexivity.
        -- set_tail_u t ch p m HW.
           replace ((ch <? 48) && legalb p v) with true
             by (unfold legalb; rewrite (proj2 (Z.ltb_lt ch 48)) by lia; rewrite (proj2 (Z.eqb_eq p 2)) by lia;
                 rewrite (proj2 (Z.leb_le v 55)) by lia; rewrite orb_true_r; reflexivity).
           set_finish t ch p v T HL HB m1 m2 m3.
    + zstep. zstep.
      if_cases HC3; zify_cond HC3.
      * set_tail_u t ch p m HW.
        replace ((ch <? 48) && legalb p v) with true
          by (unfold legalb; rewrite (proj2 (Z.ltb_lt ch 48)) by lia; rewrite (proj2 (Z.ltb_lt p 2)) by lia;
              rewrite (proj2 (Z.leb_le v 1)) by lia; reflexivity).
        set_finish t ch p v T HL HB m1 m2 m3.
      * zstep. zstep. zstep. apply evt_done. do 16 eexists. split; [reflexivity|].
        replace ((ch <? 48) && legalb p v) with false
          by (unfold legalb; rewrite (proj2 (Z.ltb_lt p 2)) by lia; rewrite (proj2 (Z.leb_gt v 1)) by lia;
              rewrite (proj2 (Z.eqb_neq p 2)) by lia; rewrite andb_false_r; reflexivity).
        split; reflexivity.
Qed.
