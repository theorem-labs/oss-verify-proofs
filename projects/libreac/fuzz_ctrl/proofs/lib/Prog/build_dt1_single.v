From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcRec RcRecLib RcBox RcBoxLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import memcpy_c build_dt1_single_c.
Import ListNotations.
Open Scope Z_scope.

Section BDP.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (wo wv wd wn : word) (ob D P5 J20 : list byte) (nn : nat).
  Hypothesis HMC : memcpy_contract.
  Hypothesis Rsp : 48 <= bv_unsigned sp < 2^64.
  Hypothesis Ro : 0 <= bv_unsigned wo.
  Hypothesis Ho32 : bv_unsigned wo + 32 <= 2^64.
  Hypothesis Rd : 0 <= bv_unsigned wd.
  Hypothesis Hd : bv_unsigned wd + bv_unsigned wn <= 2^64.
  Hypothesis Hnn : Z.of_nat nn = bv_unsigned wn.
  Hypothesis Hn9 : (nn <= 9)%nat.
  Hypothesis HLD : length D = nn.
  Hypothesis Lob : length ob = 32%nat.
  Hypothesis LJ20 : length J20 = nn.
  Hypothesis EP5 : P5 = firstn (9 - nn) (skipn (22 + nn) ob).
  Hypothesis DfO : bv_unsigned sp <= bv_unsigned wo \/ bv_unsigned wo + 32 <= bv_unsigned sp + -48.
  Hypothesis DdO : bv_unsigned wd + bv_unsigned wn <= bv_unsigned wo \/ bv_unsigned wo + 32 <= bv_unsigned wd.

  Definition Wp : list ivl :=
    [(bv_unsigned sp + -48, bv_unsigned sp);
     (bv_unsigned wo, bv_unsigned wo + 22 + bv_unsigned wn);
     (bv_unsigned wo + 31, bv_unsigned wo + 32)].

  Definition Qp : machine_state -> Prop :=
    fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ bytes_at rsegs m' (bv_unsigned wo) (dt1_out nn (bv_unsigned wv) D ob)
      /\ psum (skipn 16 (dt1_out nn (bv_unsigned wv) D ob)) (nn + 5) mod 128 = 0
      /\ psum (dt1_out nn (bv_unsigned wv) D ob) 32 mod 256 = 0
      /\ munch Wp m m'
      /\ wmono rsegs m m'
      /\ mem_inv rsegs m'
      /\ stk rsegs m' (bv_unsigned sp + -48) (bv_unsigned sp).

  Definition frp (m' : word -> option byte) : Prop :=
    exists j, rw_cells rsegs m' (bv_unsigned sp + -48) [CB 8 j; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Lemma ostp : forall m' j (b : byte), 0 <= j < 32 -> inside Wp (bv_unsigned wo + j) 1 ->
    frp m' -> wr_at rsegs m' (bv_unsigned wo) 32 -> munch Wp m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
    frp (write_to_mem m' (wa (bv_unsigned wo + j)) [b]) /\
    wr_at rsegs (write_to_mem m' (wa (bv_unsigned wo + j)) [b]) (bv_unsigned wo) 32 /\
    munch Wp m (write_to_mem m' (wa (bv_unsigned wo + j)) [b]) /\
    wmono rsegs m (write_to_mem m' (wa (bv_unsigned wo + j)) [b]) /\
    mem_inv rsegs (write_to_mem m' (wa (bv_unsigned wo + j)) [b]) /\
    bytes_at rsegs (write_to_mem m' (wa (bv_unsigned wo + j)) [b]) (bv_unsigned wo + j) [b].
  Proof.
    intros m' j b Hj Hin (jk & FR) WO MU WM MI.
    pose proof (wr_at_store_ok rsegs m' (bv_unsigned wo) 32 j 1 WO ltac:(lia) ltac:(lia)) as HS.
    split; [exists jk; apply rw_cells_frame; [exact FR | lia | cbn [length]; lia | cbn [cells_size csize Nat.add length]; lia]|].
    split; [apply wr_at_write; exact WO|].
    split; [apply munch_write; [exact MU | lia | cbn [length]; lia | exact Hin]|].
    split; [apply wmono_write; exact WM|].
    split; [apply mem_inv_store; [exact MI | exact HS]|].
    apply bytes_at_write_same; cbn [length]; lia.
  Qed.

  Lemma epip : forall x1 x8 x9 x18 x19 u0 u1 u2 x10 x11 x12 x13 x14 x15 x16 x17 u3 u4 u5 u6 m',
    frp m' -> bytes_at rsegs m' (bv_unsigned wo) (dt1_out nn (bv_unsigned wv) D ob) ->
    munch Wp m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
    evt rsegs Qp
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x154dc) fc None m' (seg_rom rsegs)).
  Proof.
    intros x1 x8 x9 x18 x19 u0 u1 u2 x10 x11 x12 x13 x14 x15 x16 x17 u3 u4 u5 u6 m' (jk & FR) HB MU WM MI.
    step. step. step. step. step. step. step.
    apply evt_done. unfold Qp. do 15 eexists. exists m'.
    split; [reflexivity|].
    split; [exact HB|].
    split; [apply dt1_so128; exact HLD|].
    split; [apply dt1_so256; assumption|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    apply stk_of_rw_cells in FR. cbn [cells_size csize Nat.add] in FR.
    replace (bv_unsigned sp + -48 + Z.of_nat 48) with (bv_unsigned sp) in FR by lia. exact FR.
  Qed.

  Lemma outerp : forall k i u0 u1 u2 x9 x12 x13 x14 x15 x16 x17 x18 x19 u3 u4 u5 u6 m',
    (i + k = 31)%nat -> (0 < k)%nat ->
    x12 = Z_to_bv 64 (bv_unsigned wo + Z.of_nat i) ->
    frp m' -> wr_at rsegs m' (bv_unsigned wo) 32 ->
    bytes_at rsegs m' (bv_unsigned wo) (dt1_body nn (bv_unsigned wv) D ob) ->
    munch Wp m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
    evt rsegs Qp
      (MS (mkR (Z_to_bv 64 0x15488) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0 u1 u2 wo x9
               (Z_to_bv 64 (psum (dt1_body nn (bv_unsigned wv) D ob) i)) (Z_to_bv 64 (bv_unsigned wo + 31))
               x12 x13 x14 x15 x16 x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x154c4) fc None m' (seg_rom rsegs)).
  Proof.
    induction k as [|k IH]; intros i u0 u1 u2 x9 x12 x13 x14 x15 x16 x17 x18 x19 u3 u4 u5 u6 m' Hik Hk E12 FR WO HB MU WM MI;
      [lia|].
    subst x12.
    pose proof (dt1_body_length nn (bv_unsigned wv) D ob HLD Lob Hn9) as LB.
    pose proof (rd_byte rsegs m' (bv_unsigned wo) _ i HB ltac:(lia)) as RD.
    pose proof (psum_range (dt1_body nn (bv_unsigned wv) D ob) i) as PR.
    step. step. step.
    rewrite psum_S_zxb.
    step.
    rewrite (rc_eqb_lit (bv_unsigned wo + Z.of_nat i + 1) (bv_unsigned wo + 31)) by lia.
    destruct k as [|k].
    - replace (bv_unsigned wo + Z.of_nat i + 1 =? bv_unsigned wo + 31) with true by (symmetry; apply Z.eqb_eq; lia).
      cbn [negb]. cbv iota.
      replace (S i) with 31%nat by lia.
      step.
      pose proof (wr_at_store_ok rsegs m' (bv_unsigned wo) 32 31 1 WO ltac:(lia) ltac:(lia)) as HS.
      step.
      rewrite rc_le1_negw.
      destruct (ostp m' 31 (Z_to_bv 8 ((- psum (dt1_body nn (bv_unsigned wv) D ob) 31) mod 256)) ltac:(lia)
                  ltac:(cbn [inside Wp]; right; right; left; split; lia) FR WO MU WM MI)
        as (FR' & WO' & MU' & WM' & MI' & B31).
      eapply epip; [exact FR' | | exact MU' | exact WM' | exact MI'].
      unfold dt1_out. eapply bytes_at_cat; [ | exact B31 | rewrite LB; lia].
      apply bytes_at_write_other; [exact HB | lia | cbn [length]; lia | rewrite LB; cbn [length]; lia].
    - replace (bv_unsigned wo + Z.of_nat i + 1 =? bv_unsigned wo + 31) with false by (symmetry; apply Z.eqb_neq; lia).
      cbn [negb]. cbv iota.
      apply (IH (S i)); first [lia | assumption | f_equal; lia].
  Qed.

  Lemma innerp : forall k i u0 u1 u2 x10 x12 x13 x14 x15 x16 x17 x18 x19 u3 u4 u5 u6 m',
    (i + k = nn + 4)%nat -> (0 < k)%nat ->
    x19 = Z_to_bv 64 (bv_unsigned wo + 16 + Z.of_nat i) ->
    bv_unsigned x18 = bv_unsigned wo + 20 + bv_unsigned wn ->
    frp m' -> wr_at rsegs m' (bv_unsigned wo) 32 ->
    bytes_at rsegs m' (bv_unsigned wo) (dt1_hdr nn (bv_unsigned wv) ++ D) ->
    bytes_at rsegs m' (bv_unsigned wo + 22 + bv_unsigned wn) P5 ->
    munch Wp m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
    evt rsegs Qp
      (MS (mkR (Z_to_bv 64 0x15488) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0 u1 u2 wo wn
               x10 (Z_to_bv 64 (psum (skipn 16 (dt1_hdr nn (bv_unsigned wv)) ++ D) i))
               x12 x13 x14 x15 x16 x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x15490) fc None m' (seg_rom rsegs)).
  Proof.
    induction k as [|k IH];
      intros i u0 u1 u2 x10 x12 x13 x14 x15 x16 x17 x18 x19 u3 u4 u5 u6 m' Hik Hk E19 H18 FR WO Bhd B5 MU WM MI; [lia|].
    subst x19.
    assert (LP5 : length P5 = (9 - nn)%nat) by (rewrite EP5, length_firstn, length_skipn; lia).
    assert (LHD : length (dt1_hdr nn (bv_unsigned wv) ++ D) = (20 + nn)%nat)
      by (rewrite length_app, dt1_hdr_length, HLD; lia).
    pose proof (bytes_at_skip16 rsegs m' _ _ D (dt1_hdr_length nn (bv_unsigned wv)) Bhd) as B16.
    assert (L4D : length (skipn 16 (dt1_hdr nn (bv_unsigned wv)) ++ D) = (4 + nn)%nat)
      by (rewrite length_app, dt1_s4_length, HLD; lia).
    pose proof (rd_byte rsegs m' (bv_unsigned wo + 16) _ i B16 ltac:(lia)) as RD.
    pose proof (psum_range (skipn 16 (dt1_hdr nn (bv_unsigned wv)) ++ D) i) as PR.
    step. step. step.
    rewrite psum_S_zxb.
    step.
    rewrite (rc_eqb_w2 (Z_to_bv 64 (bv_unsigned wo + 16 + Z.of_nat i + 1)) x18
               (bv_unsigned wo + 16 + Z.of_nat i + 1) (bv_unsigned wo + 20 + bv_unsigned wn)) by (try rewrite unsigned_lit; lia).
    destruct k as [|k].
    - replace (bv_unsigned wo + 16 + Z.of_nat i + 1 =? bv_unsigned wo + 20 + bv_unsigned wn) with true
        by (symmetry; apply Z.eqb_eq; lia).
      cbn [negb]. cbv iota.
      replace (S i) with (nn + 4)%nat by lia.
      step. step. step. step. step.
      pose proof (wr_at_store_ok rsegs m' (bv_unsigned wo) 32 (bv_unsigned wn + 20) 1 WO ltac:(lia) ltac:(lia)) as HS1.
      step.
      rewrite rc_le1_stamp.
      change ((- psum (skipn 16 (dt1_hdr nn (bv_unsigned wv)) ++ D) (nn + 4)) mod 128) with (dt1_ick nn (bv_unsigned wv) D).
      destruct (ostp m' (bv_unsigned wn + 20) (Z_to_bv 8 (dt1_ick nn (bv_unsigned wv) D)) ltac:(lia)
                  ltac:(cbn [inside Wp]; right; left; split; lia) FR WO MU WM MI)
        as (FR1 & WO1 & MU1 & WM1 & MI1 & Bick).
      pose proof (bytes_at_write_other rsegs m' (bv_unsigned wo + (bv_unsigned wn + 20))
                    [Z_to_bv 8 (dt1_ick nn (bv_unsigned wv) D)] _ _ Bhd ltac:(lia) ltac:(cbn [length]; lia)
                    ltac:(rewrite LHD; cbn [length]; lia)) as Bhd1.
      pose proof (bytes_at_write_other rsegs m' (bv_unsigned wo + (bv_unsigned wn + 20))
                    [Z_to_bv 8 (dt1_ick nn (bv_unsigned wv) D)] _ _ B5 ltac:(lia) ltac:(cbn [length]; lia)
                    ltac:(rewrite LP5; cbn [length]; lia)) as B51.
      unfold wa in *.
      remember (write_to_mem m' (Z_to_bv 64 (bv_unsigned wo + (bv_unsigned wn + 20)))
                  [Z_to_bv 8 (dt1_ick nn (bv_unsigned wv) D)]) as m1 eqn:Em1.
      clear Em1.
      pose proof (wr_at_store_ok rsegs m1 (bv_unsigned wo) 32 (bv_unsigned wn + 21) 1 WO1 ltac:(lia) ltac:(lia)) as HS2.
      step.
      rewrite rc_le1_lit.
      replace (Z_to_bv 8 (-9)) with (Z_to_bv 8 247) by (apply Z_to_bv8_mod; reflexivity).
      destruct (ostp m1 (bv_unsigned wn + 21) (Z_to_bv 8 247) ltac:(lia)
                  ltac:(cbn [inside Wp]; right; left; split; lia) FR1 WO1 MU1 WM1 MI1)
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
      unfold wa in *.
      remember (write_to_mem m1 (Z_to_bv 64 (bv_unsigned wo + (bv_unsigned wn + 21))) [Z_to_bv 8 247])
        as m2 eqn:Em2.
      clear Em2.
      step. step.
      eapply outerp with (k := 31%nat) (i := 0%nat); [lia | lia | | exact FR2 | exact WO2 | | exact MU2 | exact WM2 | exact MI2].
      + rewrite Z.add_0_r. symmetry. apply Z_to_bv_lit_self.
      + unfold dt1_body. rewrite <- EP5. rewrite app_assoc.
        apply (bytes_at_cat _ _ _ (bv_unsigned wo + (bv_unsigned wn + 20))); [exact Bhd2 | | rewrite LHD; lia].
        change ([Z_to_bv 8 (dt1_ick nn (bv_unsigned wv) D); Z_to_bv 8 247] ++ P5)
          with ([Z_to_bv 8 (dt1_ick nn (bv_unsigned wv) D)] ++ ([Z_to_bv 8 247] ++ P5)).
        apply (bytes_at_cat _ _ _ (bv_unsigned wo + (bv_unsigned wn + 21))); [exact Bick2 | | cbn [length]; lia].
        apply (bytes_at_cat _ _ _ (bv_unsigned wo + 22 + bv_unsigned wn)); [exact Bf7 | exact B52 | cbn [length]; lia].
    - replace (bv_unsigned wo + 16 + Z.of_nat i + 1 =? bv_unsigned wo + 20 + bv_unsigned wn) with false
        by (symmetry; apply Z.eqb_neq; lia).
      cbn [negb]. cbv iota.
      apply (IH (S i)); first [lia | assumption | f_equal; lia].
  Qed.

  Definition pinv (m' : word -> option byte) (P : list byte) : Prop :=
    frp m' /\ wr_at rsegs m' (bv_unsigned wo) 32 /\ bytes_at rsegs m' (bv_unsigned wo) P /\
    bytes_at rsegs m' (bv_unsigned wo + 20) J20 /\ bytes_at rsegs m' (bv_unsigned wo + 22 + bv_unsigned wn) P5 /\
    bytes_at rsegs m' (bv_unsigned wd) D /\
    munch Wp m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.

  Lemma pinv_ok : forall m' P k, pinv m' P -> k = Z.of_nat (length P) -> (length P < 20)%nat ->
    store_ok rsegs m' (wa (bv_unsigned wo + k)) 1 = true.
  Proof. intros m' P k (_ & WO & _) Hk Hl. apply (wr_at_store_ok rsegs m' (bv_unsigned wo) 32); [exact WO | lia | lia]. Qed.

  Lemma pinv_ok0 : forall m', pinv m' [] -> store_ok rsegs m' wo 1 = true.
  Proof.
    intros m' D0. pose proof (pinv_ok m' [] 0 D0 eq_refl ltac:(cbn; lia)) as H.
    rewrite Z.add_0_r in H. rewrite (wa_of_var wo (bv_unsigned wo) eq_refl) in H. exact H.
  Qed.

  Lemma pinv_store : forall m' P (A v : word), pinv m' P -> (length P < 20)%nat ->
    A = wa (bv_unsigned wo + Z.of_nat (length P)) ->
    pinv (write_to_mem m' A (le1 v)) (P ++ [Z_to_bv 8 (bv_unsigned v)]).
  Proof.
    intros m' P A v ((jk & FR) & WO & BP & B20 & B5 & BD & MU & WM & MI) Hl ->.
    assert (LP5 : length P5 = (9 - nn)%nat) by (rewrite EP5, length_firstn, length_skipn; lia).
    pose proof (wr_at_store_ok rsegs m' (bv_unsigned wo) 32 (Z.of_nat (length P)) 1 WO ltac:(lia) ltac:(lia)) as HS.
    change (le1 v) with [Z_to_bv 8 (bv_unsigned v)].
    split; [exists jk; apply rw_cells_frame; [exact FR | lia | cbn [length]; lia | cbn [cells_size csize Nat.add length]; lia]|].
    split; [apply wr_at_write; exact WO|].
    split.
    { apply (bytes_at_cat _ _ _ (bv_unsigned wo + Z.of_nat (length P))); [| | reflexivity].
      - apply bytes_at_write_other; [exact BP | lia | cbn [length]; lia | left; lia].
      - apply bytes_at_write_same; cbn [length]; lia. }
    split; [apply bytes_at_write_other; [exact B20 | lia | cbn [length]; lia | rewrite LJ20; cbn [length]; lia]|].
    split; [apply bytes_at_write_other; [exact B5 | lia | cbn [length]; lia | rewrite LP5; cbn [length]; lia]|].
    split; [apply bytes_at_write_other; [exact BD | lia | cbn [length]; lia | rewrite HLD; cbn [length]; lia]|].
    split; [apply munch_write; [exact MU | lia | cbn [length]; lia | cbn [inside Wp length]; right; left; split; lia]|].
    split; [apply wmono_write; exact WM|].
    apply mem_inv_store; [exact MI | exact HS].
  Qed.

  Ltac pst k :=
    lazymatch goal with
    | PI : pinv ?mc ?P |- _ =>
        let HS := fresh "HS" in
        first [ pose proof (pinv_ok0 mc PI) as HS
              | pose proof (pinv_ok mc P k PI eq_refl ltac:(apply Nat.ltb_lt; reflexivity)) as HS ];
        step;
        clear HS;
        lazymatch goal with
        | |- evt _ _ (MS _ _ _ _ _ (write_to_mem mc ?A (le1 ?v)) _) =>
            let PI' := fresh "PI" in
            pose proof (pinv_store mc P A v PI ltac:(apply Nat.ltb_lt; reflexivity)
                          ltac:(first [reflexivity | apply rc_wa_add0])) as PI';
            clear PI;
            let mc' := fresh "mc" in
            set (mc' := write_to_mem mc A (le1 v)) in *; clearbody mc'
        end
    end.

  Lemma mid : forall u0 u1 u2 x14 x15 x16 x17 u3 u4 u5 u6 m',
    pinv m' [] ->
    evt rsegs Qp
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0 u1 u2 s0 s1 wo wv wd wn x14 x15 x16 x17
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x153e4) fc None m' (seg_rom rsegs)).
  Proof.
    intros u0 u1 u2 x14 x15 x16 x17 u3 u4 u5 u6 m' PI.
    pose proof (zr_word wv) as Rv. unfold inr64 in Rv.
    step. step. step. step. step. step. step. step. step. step. step.
    pst 0. pst 1. pst 2. pst 3.
    step.
    pst 4. pst 5. pst 6. pst 7.
    step.
    pst 8. pst 9. pst 10. pst 11.
    step.
    pst 12. pst 13. pst 14. pst 15.
    step. step.
    pst 16. pst 17. pst 18. pst 19.
    step.
    rewrite (rc_zext32 wn) by lia.
    match goal with H : pinv _ ?P |- _ =>
      assert (EH : P = dt1_hdr nn (bv_unsigned wv)); [|rewrite EH in H]
    end.
    { cbn [app]. unfold dt1_hdr, dt1_bytes. cbn [map].
      repeat apply rc_cons_eq;
        first [ reflexivity
              | apply Z_to_bv8_mod; rewrite unsigned_lit_wrap; rewrite mod_mod8_of_modw by lia;
                first [reflexivity | f_equal; lia] ]. }
    clear EH.
    match goal with H : pinv ?mc _ |- _ => rename H into PI20; rename mc into m20 end.
    destruct PI20 as ((jk & FR) & WO & BH & B20 & B5 & BD & MU & WM & MI).
    pose proof (dt1_hdr_length nn (bv_unsigned wv)) as LH.
    assert (LP5 : length P5 = (9 - nn)%nat) by (rewrite EP5, length_firstn, length_skipn; lia).
    step. step. step. step.
    eapply evt_cut.
    { eapply HMC with (junk := J20); [exact BD | lia | | | exact MI].
      - rewrite unsigned_lit by lia. split; [split|].
        + cbn [cells_wf cell_wf]. split; [lia | exact I].
        + cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B20.
        + cbn [cells_size csize]. rewrite Nat.add_0_r.
          replace (Z.of_nat (Z.to_nat (bv_unsigned wn))) with (bv_unsigned wn) by lia.
          apply (wr_at_sub _ _ _ 32 20 (bv_unsigned wn) WO); lia.
      - rewrite unsigned_lit by lia. lia. }
    intros ms' PO.
    destruct PO as (t0' & t1' & t2' & a1'' & a2'' & a3' & a4'' & a5'' & a6' & a7' & t3' & t4' & t5' & t6' & m3 & E & MU3 & WM3 & MI3 & RW3 & BD3).
    subst ms'.
    rewrite unsigned_lit in MU3, RW3 by lia.
    clear BD3.
    unfold Wp in MU.
    transport_after_call rsegs m20 m3 MU3 WM3.
    clear MU3 WM3 MI.
    destruct RW3 as [[_ BD3] _]. cbn [cells_bytes cbytes] in BD3. rewrite app_nil_r in BD3.
    replace (ret_pc (Z_to_bv 64 87176)) with (Z_to_bv 64 87176) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    step. step.
    eapply innerp with (k := (nn + 4)%nat) (i := 0%nat); [lia | lia | | | eexists; exact FR | exact WO | | exact B5 | exact MU | exact WM | exact MI3].
    - f_equal. lia.
    - rewrite unsigned_lit by lia. reflexivity.
    - apply (bytes_at_cat _ _ _ (bv_unsigned wo + 20)); [exact BH | exact BD3 | rewrite LH; lia].
  Qed.
End BDP.

Theorem build_dt1_single_holds : memcpy_contract -> build_dt1_single_contract.
Proof.
  intros HMC. unfold build_dt1_single_contract, BUILD_DT1_SINGLE.
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
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp);
                   (bv_unsigned a0, bv_unsigned a0 + 22 + bv_unsigned a3);
                   (bv_unsigned a0 + 31, bv_unsigned a0 + 32)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step.
  carve_frame 48%nat ST.
  clear ST.
  step. step. step. step. step.
  pose proof (bytes_at_sub rsegs _ _ ob 20 nn HOB ltac:(lia)) as B20.
  pose proof (bytes_at_sub rsegs _ _ ob (22 + nn) (9 - nn) HOB ltac:(lia)) as B5.
  remember (firstn nn (skipn 20 ob)) as J20 eqn:EJ20.
  assert (LJ20 : length J20 = nn) by (subst J20; rewrite length_firstn, length_skipn; lia).
  clear EJ20.
  remember (firstn (9 - nn) (skipn (22 + nn) ob)) as P5 eqn:EP5.
  change (Z.of_nat 20) with 20 in B20.
  apply (bytes_at_addr _ _ _ (bv_unsigned a0 + 22 + bv_unsigned a3)) in B5; [|lia].
  clear HOB.
  eapply mid; try eassumption; try lia.
  split; [eexists; eassumption|]. split; [assumption|]. split; [apply bytes_at_nil; lia|].
  split; [assumption|]. split; [assumption|]. split; [assumption|].
  split; [assumption|]. split; assumption.
Qed.
