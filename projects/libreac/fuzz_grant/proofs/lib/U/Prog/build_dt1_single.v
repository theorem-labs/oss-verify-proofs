From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import RcModel RcLib RcRec RcRecLib RcBox RcBoxLib.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import dt1_head_c memcpy_c build_dt1_single_c.
Import ListNotations.
Open Scope Z_scope.

Section BDS.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (wo wv wd wn : word) (ob D P5 : list byte) (nn : nat).
  Hypothesis Rsp : 32 <= bv_unsigned sp < 2^64.
  Hypothesis Ro : 0 <= bv_unsigned wo.
  Hypothesis Ho32 : bv_unsigned wo + 32 <= 2^64.
  Hypothesis Hnn : Z.of_nat nn = bv_unsigned wn.
  Hypothesis Hn9 : (nn <= 9)%nat.
  Hypothesis HLD : length D = nn.
  Hypothesis Lob : length ob = 32%nat.
  Hypothesis EP5 : P5 = firstn (9 - nn) (skipn (22 + nn) ob).
  Hypothesis DfO : bv_unsigned sp <= bv_unsigned wo \/ bv_unsigned wo + 32 <= bv_unsigned sp + -32.

  Definition Wb : list ivl :=
    [(bv_unsigned sp + -32, bv_unsigned sp);
     (bv_unsigned wo, bv_unsigned wo + 22 + bv_unsigned wn);
     (bv_unsigned wo + 31, bv_unsigned wo + 32)].

  Definition Qb : machine_state -> Prop :=
    fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ bytes_at rsegs m' (bv_unsigned wo) (dt1_out nn (bv_unsigned wv) D ob)
      /\ psum (skipn 16 (dt1_out nn (bv_unsigned wv) D ob)) (nn + 5) mod 128 = 0
      /\ psum (dt1_out nn (bv_unsigned wv) D ob) 32 mod 256 = 0
      /\ munch Wb m m'
      /\ wmono rsegs m m'
      /\ mem_inv rsegs m'
      /\ stk rsegs m' (bv_unsigned sp + -32) (bv_unsigned sp).

  Definition fr (m' : word -> option byte) : Prop :=
    rw_cells rsegs m' (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra].

  Lemma ost : forall m' j (b : byte), 0 <= j < 32 -> inside Wb (bv_unsigned wo + j) 1 ->
    fr m' -> wr_at rsegs m' (bv_unsigned wo) 32 -> munch Wb m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
    fr (write_to_mem m' (wa (bv_unsigned wo + j)) [b]) /\
    wr_at rsegs (write_to_mem m' (wa (bv_unsigned wo + j)) [b]) (bv_unsigned wo) 32 /\
    munch Wb m (write_to_mem m' (wa (bv_unsigned wo + j)) [b]) /\
    wmono rsegs m (write_to_mem m' (wa (bv_unsigned wo + j)) [b]) /\
    mem_inv rsegs (write_to_mem m' (wa (bv_unsigned wo + j)) [b]) /\
    bytes_at rsegs (write_to_mem m' (wa (bv_unsigned wo + j)) [b]) (bv_unsigned wo + j) [b].
  Proof.
    intros m' j b Hj Hin FR WO MU WM MI.
    pose proof (wr_at_store_ok rsegs m' (bv_unsigned wo) 32 j 1 WO ltac:(lia) ltac:(lia)) as HS.
    split; [apply rw_cells_frame; [exact FR | lia | cbn [length]; lia | cbn [cells_size csize Nat.add length]; lia]|].
    split; [apply wr_at_write; exact WO|].
    split; [apply munch_write; [exact MU | lia | cbn [length]; lia | exact Hin]|].
    split; [apply wmono_write; exact WM|].
    split; [apply mem_inv_store; [exact MI | exact HS]|].
    apply bytes_at_write_same; cbn [length]; lia.
  Qed.

  Lemma epi : forall x1 x8 x9 x18 u0 u1 u2 x10 x11 x12 x13 x14 x15 x16 x17 u3 u4 u5 u6 m',
    fr m' -> bytes_at rsegs m' (bv_unsigned wo) (dt1_out nn (bv_unsigned wv) D ob) ->
    munch Wb m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
    evt rsegs Qb
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
               x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x15128) fc None m' (seg_rom rsegs)).
  Proof.
    intros x1 x8 x9 x18 u0 u1 u2 x10 x11 x12 x13 x14 x15 x16 x17 u3 u4 u5 u6 m' FR HB MU WM MI.
    unfold fr in FR.
    step. step. step. step. step. step.
    apply evt_done. unfold Qb. do 15 eexists. exists m'.
    split; [reflexivity|].
    split; [exact HB|].
    split; [apply dt1_so128; exact HLD|].
    split; [apply dt1_so256; assumption|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    apply stk_of_rw_cells in FR. cbn [cells_size csize Nat.add] in FR.
    replace (bv_unsigned sp + -32 + Z.of_nat 32) with (bv_unsigned sp) in FR by lia. exact FR.
  Qed.

  Lemma outer : forall k i u0 u1 u2 x9 x10 x14 x15 x16 x17 u3 u4 u5 u6 m',
    (i + k = 31)%nat -> (0 < k)%nat ->
    bv_unsigned x10 = 18446744073709551615 - bv_unsigned wo ->
    fr m' -> wr_at rsegs m' (bv_unsigned wo) 32 ->
    bytes_at rsegs m' (bv_unsigned wo) (dt1_body nn (bv_unsigned wv) D ob) ->
    munch Wb m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
    evt rsegs Qb
      (MS (mkR (Z_to_bv 64 86152) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp u0 u1 u2 wo x9 x10
               (Z_to_bv 64 (psum (dt1_body nn (bv_unsigned wv) D ob) i)) (Z_to_bv 64 (Z.of_nat i)) (Z_to_bv 64 31)
               x14 x15 x16 x17 wd s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x15100) fc None m' (seg_rom rsegs)).
  Proof.
    induction k as [|k IH]; intros i u0 u1 u2 x9 x10 x14 x15 x16 x17 u3 u4 u5 u6 m' Hik Hk H10 FR WO HB MU WM MI; [lia|].
    pose proof (dt1_body_length nn (bv_unsigned wv) D ob HLD Lob Hn9) as LB.
    pose proof (rd_byte rsegs m' (bv_unsigned wo) _ i HB ltac:(lia)) as RD.
    pose proof (psum_range (dt1_body nn (bv_unsigned wv) D ob) i) as PR.
    step.
    rewrite (rc_ltu_ge (Z_to_bv 64 (Z.of_nat i)) x10) by (rewrite unsigned_lit by lia; lia).
    step. step. step. step.
    rewrite psum_S_zxb.
    step.
    rewrite (rc_eqb_lit (Z.of_nat i + 1) 31) by lia.
    destruct k as [|k].
    - replace (Z.of_nat i + 1 =? 31) with true by (symmetry; apply Z.eqb_eq; lia).
      cbn [negb]. cbv iota.
      replace (S i) with 31%nat by lia.
      step. step.
      if_false.
      step.
      pose proof (wr_at_store_ok rsegs m' (bv_unsigned wo) 32 31 1 WO ltac:(lia) ltac:(lia)) as HS.
      step.
      rewrite rc_le1_negw.
      destruct (ost m' 31 (Z_to_bv 8 ((- psum (dt1_body nn (bv_unsigned wv) D ob) 31) mod 256)) ltac:(lia)
                  ltac:(cbn [inside Wb]; right; right; left; split; lia) FR WO MU WM MI)
        as (FR' & WO' & MU' & WM' & MI' & B31).
      eapply epi; [exact FR' | | exact MU' | exact WM' | exact MI'].
      unfold dt1_out. eapply bytes_at_cat; [ | exact B31 | rewrite LB; lia].
      apply bytes_at_write_other; [exact HB | lia | cbn [length]; lia | rewrite LB; cbn [length]; lia].
    - replace (Z.of_nat i + 1 =? 31) with false by (symmetry; apply Z.eqb_neq; lia).
      cbn [negb]. cbv iota.
      replace (Z.of_nat i + 1) with (Z.of_nat (S i)) by lia.
      apply (IH (S i)); first [lia | assumption].
  Qed.

  Lemma inner : forall k i u0 u1 u2 x12 x13 x14 x15 x16 x17 u3 u4 u5 u6 m',
    (i + k = nn + 4)%nat -> (0 < k)%nat ->
    bv_unsigned x12 = Z.of_nat nn + 4 ->
    bv_unsigned x13 = 18446744073709551615 - (bv_unsigned wo + 16) ->
    fr m' -> wr_at rsegs m' (bv_unsigned wo) 32 ->
    bytes_at rsegs m' (bv_unsigned wo) (dt1_hdr nn (bv_unsigned wv) ++ D) ->
    bytes_at rsegs m' (bv_unsigned wo + 22 + bv_unsigned wn) P5 ->
    munch Wb m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
    evt rsegs Qb
      (MS (mkR (Z_to_bv 64 86152) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp u0 u1 u2 wo wn
               (Z_to_bv 64 (Z.of_nat i)) (Z_to_bv 64 (psum (skipn 16 (dt1_hdr nn (bv_unsigned wv)) ++ D) i))
               x12 x13 x14 x15 x16 x17 wd s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x150ac) fc None m' (seg_rom rsegs)).
  Proof.
    induction k as [|k IH];
      intros i u0 u1 u2 x12 x13 x14 x15 x16 x17 u3 u4 u5 u6 m' Hik Hk H12 H13 FR WO Bhd B5 MU WM MI; [lia|].
    assert (LP5 : length P5 = (9 - nn)%nat) by (rewrite EP5, length_firstn, length_skipn; lia).
    assert (LHD : length (dt1_hdr nn (bv_unsigned wv) ++ D) = (20 + nn)%nat)
      by (rewrite length_app, dt1_hdr_length, HLD; lia).
    pose proof (bytes_at_skip16 rsegs m' _ _ D (dt1_hdr_length nn (bv_unsigned wv)) Bhd) as B16.
    assert (L4D : length (skipn 16 (dt1_hdr nn (bv_unsigned wv)) ++ D) = (4 + nn)%nat)
      by (rewrite length_app, dt1_s4_length, HLD; lia).
    pose proof (rd_byte rsegs m' (bv_unsigned wo + 16) _ i B16 ltac:(lia)) as RD.
    replace (bv_unsigned wo + 16 + Z.of_nat i) with (bv_unsigned wo + Z.of_nat i + 16) in RD by lia.
    pose proof (psum_range (skipn 16 (dt1_hdr nn (bv_unsigned wv)) ++ D) i) as PR.
    step.
    rewrite (rc_ltu_ge (Z_to_bv 64 (Z.of_nat i)) x13) by (rewrite unsigned_lit by lia; lia).
    step. step. step. step.
    rewrite psum_S_zxb.
    step.
    rewrite (rc_eqb_w x12 (Z.of_nat nn + 4) (Z.of_nat i + 1) H12) by lia.
    destruct k as [|k].
    - replace (Z.of_nat nn + 4 =? Z.of_nat i + 1) with true by (symmetry; apply Z.eqb_eq; lia).
      cbn [negb]. cbv iota.
      replace (S i) with (nn + 4)%nat by lia.
      step.
      rewrite (rc_swrap_small (bv_unsigned wn + 20)) by lia.
      step.
      rewrite (zb_lxor_ones (bv_unsigned wo)) by lia.
      step.
      rewrite rc_ltu_lit by lia.
      if_false.
      step. step. step. step.
      rewrite (rc_swrap_small (bv_unsigned wn + 21)) by lia.
      pose proof (wr_at_store_ok rsegs m' (bv_unsigned wo) 32 (bv_unsigned wn + 20) 1 WO ltac:(lia) ltac:(lia)) as HS1.
      step.
      rewrite rc_le1_stamp.
      change ((- psum (skipn 16 (dt1_hdr nn (bv_unsigned wv)) ++ D) (nn + 4)) mod 128) with (dt1_ick nn (bv_unsigned wv) D).
      destruct (ost m' (bv_unsigned wn + 20) (Z_to_bv 8 (dt1_ick nn (bv_unsigned wv) D)) ltac:(lia)
                  ltac:(cbn [inside Wb]; right; left; split; lia) FR WO MU WM MI)
        as (FR1 & WO1 & MU1 & WM1 & MI1 & Bick).
      pose proof (bytes_at_write_other rsegs m' (bv_unsigned wo + (bv_unsigned wn + 20))
                    [Z_to_bv 8 (dt1_ick nn (bv_unsigned wv) D)] _ _ Bhd ltac:(lia) ltac:(cbn [length]; lia)
                    ltac:(rewrite LHD; cbn [length]; lia)) as Bhd1.
      pose proof (bytes_at_write_other rsegs m' (bv_unsigned wo + (bv_unsigned wn + 20))
                    [Z_to_bv 8 (dt1_ick nn (bv_unsigned wv) D)] _ _ B5 ltac:(lia) ltac:(cbn [length]; lia)
                    ltac:(rewrite LP5; cbn [length]; lia)) as B51.
      unfold wa, fr in *.
      remember (write_to_mem m' (Z_to_bv 64 (bv_unsigned wo + (bv_unsigned wn + 20)))
                  [Z_to_bv 8 (dt1_ick nn (bv_unsigned wv) D)]) as m1 eqn:Em1.
      clear Em1.
      step.
      rewrite rc_ltu_lit by lia.
      if_false.
      step. step. step. step.
      pose proof (wr_at_store_ok rsegs m1 (bv_unsigned wo) 32 (bv_unsigned wn + 21) 1 WO1 ltac:(lia) ltac:(lia)) as HS2.
      step.
      rewrite rc_le1_lit.
      replace (Z_to_bv 8 (-9)) with (Z_to_bv 8 247) by (apply Z_to_bv8_mod; reflexivity).
      destruct (ost m1 (bv_unsigned wn + 21) (Z_to_bv 8 247) ltac:(lia)
                  ltac:(cbn [inside Wb]; right; left; split; lia) FR1 WO1 MU1 WM1 MI1)
        as (FR2 & WO2 & MU2 & WM2 & MI2 & Bf7).
      pose proof (bytes_at_write_other rsegs m1 (bv_unsigned wo + (bv_unsigned wn + 21))
                    [Z_to_bv 8 247] _ _ Bhd1 ltac:(lia) ltac:(cbn [length]; lia)
                    ltac:(rewrite LHD; cbn [length]; lia)) as Bhd2.
      pose proof (bytes_at_write_other rsegs m1 (bv_unsigned wo + (bv_unsigned wn + 21))
                    [Z_to_bv 8 247] _ _ B51 ltac:(lia) ltac:(cbn [length]; lia)
                    ltac:(rewrite LP5; cbn [length]; lia)) as B52.
      pose proof (bytes_at_write_other rsegs m1 (bv_unsigned wo + (bv_unsigned wn + 21))
                    [Z_to_bv 8 247] _ _ Bick ltac:(lia) ltac:(cbn [length]; lia)
                    ltac:(cbn [length]; lia)) as Bick2.
      unfold wa, fr in *.
      remember (write_to_mem m1 (Z_to_bv 64 (bv_unsigned wo + (bv_unsigned wn + 21))) [Z_to_bv 8 247])
        as m2 eqn:Em2.
      clear Em2.
      step.
      eapply outer with (k := 31%nat) (i := 0%nat); [lia | lia | | exact FR2 | exact WO2 | | exact MU2 | exact WM2 | exact MI2].
      + rewrite unsigned_lit by lia. reflexivity.
      + unfold dt1_body. rewrite <- EP5. rewrite app_assoc.
        apply (bytes_at_cat _ _ _ (bv_unsigned wo + (bv_unsigned wn + 20))); [exact Bhd2 | | rewrite LHD; lia].
        change ([Z_to_bv 8 (dt1_ick nn (bv_unsigned wv) D); Z_to_bv 8 247] ++ P5)
          with ([Z_to_bv 8 (dt1_ick nn (bv_unsigned wv) D)] ++ ([Z_to_bv 8 247] ++ P5)).
        apply (bytes_at_cat _ _ _ (bv_unsigned wo + (bv_unsigned wn + 21))); [exact Bick2 | | cbn [length]; lia].
        apply (bytes_at_cat _ _ _ (bv_unsigned wo + 22 + bv_unsigned wn)); [exact Bf7 | exact B52 | cbn [length]; lia].
    - replace (Z.of_nat nn + 4 =? Z.of_nat i + 1) with false by (symmetry; apply Z.eqb_neq; lia).
      cbn [negb]. cbv iota.
      replace (Z.of_nat i + 1) with (Z.of_nat (S i)) by lia.
      apply (IH (S i)); first [lia | assumption].
  Qed.
End BDS.

Theorem build_dt1_single_holds : dt1_head_contract -> memcpy_contract -> build_dt1_single_contract.
Proof.
  intros HDT HMC. unfold build_dt1_single_contract, BUILD_DT1_SINGLE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    ob D ST Hn Ho0 Ho32 HO Hd HLD HD DdO DfO Dfd MI.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word a0) as Ro. unfold inr64 in Ro.
  pose proof (zr_word a2) as Rd. unfold inr64 in Rd.
  pose proof (zr_word a3) as Rn. unfold inr64 in Rn.
  pose proof ST as (Rlo & _ & _).
  destruct HO as [[Hwf HOB] WO]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Lob _].
  cbn [cells_bytes cbytes cells_size csize Nat.add] in HOB, WO. rewrite app_nil_r in HOB.
  change (Z.of_nat 32) with 32 in WO.
  remember (Z.to_nat (bv_unsigned a3)) as nn eqn:Enn.
  assert (Hnn : Z.of_nat nn = bv_unsigned a3) by lia.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp);
                   (bv_unsigned a0, bv_unsigned a0 + 22 + bv_unsigned a3);
                   (bv_unsigned a0 + 31, bv_unsigned a0 + 32)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step.
  carve_frame 32%nat ST.
  clear ST.
  step. step. step. step. step. step. step. step. step. step. step.
  pose proof (bytes_at_sub rsegs _ _ ob 20 nn HOB ltac:(lia)) as B20.
  pose proof (bytes_at_sub rsegs _ _ ob (22 + nn) (9 - nn) HOB ltac:(lia)) as B5.
  remember (firstn nn (skipn 20 ob)) as J20 eqn:EJ20.
  assert (LJ20 : length J20 = nn) by (subst J20; rewrite length_firstn, length_skipn; lia).
  clear EJ20.
  remember (firstn (9 - nn) (skipn (22 + nn) ob)) as P5 eqn:EP5.
  assert (LP5 : length P5 = (9 - nn)%nat) by (subst P5; rewrite length_firstn, length_skipn; lia).
  change (Z.of_nat 20) with 20 in B20.
  apply (bytes_at_addr _ _ _ (bv_unsigned a0 + 22 + bv_unsigned a3)) in B5; [|lia].
  clear HOB.
  eapply evt_cut; [eapply HDT; [lia | apply (wr_at_prefix _ _ _ 32); [eassumption | lia]] |].
  intros ms' PO.
  destruct PO as (a1' & a2' & a4' & a5' & m2 & E & BH & MU2 & WM2 & MI2).
  subst ms'.
  pose proof (dt1_hdr_length nn (bv_unsigned a1)) as LH.
  replace (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (bv_unsigned a3 + 13)))) with (Z.of_nat nn + 13) in BH
    by (rewrite rc_swrap_small by lia; rewrite unsigned_lit by lia; lia).
  change (bv_unsigned (Z_to_bv 64 3)) with 3 in BH.
  change (dt1_bytes 3 (Z.of_nat nn + 13) (bv_unsigned a1)) with (dt1_hdr nn (bv_unsigned a1)) in BH.
  specialize (MI2 MI).
  transport_after_call rsegs m1 m2 MU2 WM2.
  clear MU2 WM2 MI.
  replace (ret_pc (Z_to_bv 64 86128)) with (Z_to_bv 64 86128) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  step. step.
  if_false.
  step. step. step. step.
  eapply evt_cut.
  { eapply HMC with (junk := J20); [exact HD | lia | | | exact MI2].
    - rewrite unsigned_lit by lia. split; [split|].
      + cbn [cells_wf cell_wf]. split; [lia | exact I].
      + cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B20.
      + cbn [cells_size csize]. rewrite Nat.add_0_r.
        replace (Z.of_nat (Z.to_nat (bv_unsigned a3))) with (bv_unsigned a3) by lia.
        apply (wr_at_sub _ _ _ 32 20 (bv_unsigned a3) WO); lia.
    - rewrite unsigned_lit by lia. lia. }
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & a1'' & a2'' & a3' & a4'' & a5'' & a6' & a7' & t3' & t4' & t5' & t6' & m3 & E & MU3 & WM3 & MI3 & RW3 & BD3).
  subst ms'.
  rewrite unsigned_lit in MU3, RW3 by lia.
  clear BD3.
  transport_after_call rsegs m2 m3 MU3 WM3.
  clear MU3 WM3 MI2.
  destruct RW3 as [[_ BD] _]. cbn [cells_bytes cbytes] in BD. rewrite app_nil_r in BD.
  replace (ret_pc (Z_to_bv 64 86152)) with (Z_to_bv 64 86152) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  step. step.
  if_false.
  step. step. step. step. step. step. step.
  assert (Bhd : bytes_at rsegs m3 (bv_unsigned a0) (dt1_hdr nn (bv_unsigned a1) ++ D))
    by (apply (bytes_at_cat _ _ _ (bv_unsigned a0 + 20)); [exact BH | exact BD | rewrite LH; lia]).
  eapply inner with (k := (nn + 4)%nat) (i := 0%nat); try eassumption; try lia.
  - rewrite (unsigned_lit (bv_unsigned a3 + 4)) by lia. rewrite Z.shiftl_mul_pow2 by lia.
    rewrite (unsigned_lit ((bv_unsigned a3 + 4) * 2^32)) by lia. rewrite Z.shiftr_div_pow2 by lia.
    rewrite Z.div_mul by lia. rewrite unsigned_lit by lia. lia.
  - rewrite (unsigned_lit (bv_unsigned a0 + 16)) by lia. rewrite zb_lxor_ones by lia.
    rewrite unsigned_lit by lia. reflexivity.
Qed.
