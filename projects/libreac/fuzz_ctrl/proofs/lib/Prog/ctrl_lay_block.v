From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcPorts RcPortsLib RcBox RcSynth
  RcLay RcLayLib memset_c memcpy_c reac_box_model_block_c ctrl_lay_block_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcSynthLib.
Import ListNotations.
Open Scope Z_scope.


Section L.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (p f md g : Z) (fr tb mb nb gb : list byte).
  Hypothesis SPlo : 240 <= bv_unsigned sp < 2^64.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis P0 : 0 < p.
  Hypothesis P50 : p + 50 <= 2^64.
  Hypothesis Rf : 0 <= f < 2^64.
  Hypothesis F24 : f + 24 <= 2^64.
  Hypothesis FL : length fr = 24%nat.
  Hypothesis Rg : 0 <= g < 2^64.
  Hypothesis Rmd : 0 <= md < 2^64.
  Hypothesis AOL : ly_ao fr + ly_al fr <= 32.
  Hypothesis DJ1 : bv_unsigned sp <= p + 18 \/ p + 50 <= bv_unsigned sp - 240.
  Hypothesis DJ2 : bv_unsigned sp <= f \/ f + 24 <= bv_unsigned sp - 240.
  Hypothesis DB1 : p + 50 <= f \/ f + 24 <= p + 18.

  Definition LAY : list byte :=
    ly_lay (ly_k fr) tb (ly_Z md mb nb (ly_bb (ly_k fr))) g (ly_ao fr) (ly_al fr) gb.

  Definition BASE : list byte := ly_base (ly_k fr) tb (ly_Z md mb nb (ly_bb (ly_k fr))).

  Definition Q : machine_state -> Prop :=
    fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                      (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom rsegs) /\
      munch [(p + 18, p + 50); (bv_unsigned sp - 240, bv_unsigned sp)] m m' /\
      wmono rsegs m m' /\ mem_inv rsegs m' /\
      stk rsegs m' (bv_unsigned sp - 240) (bv_unsigned sp) /\
      rw_cells rsegs m' (p + 18) [CB 32 LAY].

  Definition LC (mc : word -> option byte) (gj X : list byte) : Prop :=
    rw_cells rsegs mc (bv_unsigned sp + -80) [CB 32 gj; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
    stk rsegs mc (bv_unsigned sp - 240) (bv_unsigned sp + -80) /\
    munch [(p + 18, p + 50); (bv_unsigned sp - 240, bv_unsigned sp)] m mc /\
    wmono rsegs m mc /\ mem_inv rsegs mc /\
    rw_cells rsegs mc (p + 18) [CB 32 X] /\ bytes_at rsegs mc f fr.

  Lemma ly_epi : forall mc gj x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31,
    LC mc gj LAY ->
    evt rsegs Q
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x14da4) fc None mc (seg_rom rsegs)).
  Proof.
    intros mc gj x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31
      (FR & ST & MU & WM & MI & BK & FB).
    do 8 step.
    release_frame FR ST (bv_unsigned sp).
    finish.
  Qed.

  Lemma LC_intro : forall mc gj X,
    rw_cells rsegs mc (bv_unsigned sp + -80) [CB 32 gj; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mc (bv_unsigned sp - 240) (bv_unsigned sp + -80) ->
    munch [(p + 18, p + 50); (bv_unsigned sp - 240, bv_unsigned sp)] m mc ->
    wmono rsegs m mc -> mem_inv rsegs mc -> rw_cells rsegs mc (p + 18) [CB 32 X] -> bytes_at rsegs mc f fr ->
    LC mc gj X.
  Proof. intros. unfold LC. tauto. Qed.

  Lemma LC_sok : forall mc gj X i, LC mc gj X -> 0 <= i < 32 ->
    store_ok rsegs mc (wa (p + 18 + i)) 1 = true.
  Proof.
    intros mc gj X i (FR & ST & MU & WM & MI & BK & FB) Hi.
    destruct (ly_rw_cb _ _ _ _ _ BK) as (_ & _ & HW).
    apply (wr_at_store_ok rsegs mc (p + 18) (Z.of_nat 32) i 1 HW); lia.
  Qed.

  Lemma LC_store : forall mc gj X a bs, LC mc gj X -> length bs = 1%nat -> p + 18 <= a < p + 50 ->
    LC (write_to_mem mc (Z_to_bv 64 a) bs) gj (upd_bytes X (Z.to_nat (a - (p + 18))) bs).
  Proof.
    intros mc gj X a bs (FR & ST & MU & WM & MI & BK & FB) Hl Ha.
    destruct (ly_rw_cb _ _ _ _ _ BK) as (XL & XB & XW).
    change (Z_to_bv 64 a) with (wa a).
    split; [|split; [|split; [|split; [|split; [|split]]]]].
    - apply rw_cells_frame; [exact FR | lia | rewrite Hl; lia |]. cbn [cells_size csize]. rewrite Hl. lia.
    - apply stk_write; [exact ST | lia | rewrite Hl; lia].
    - apply munch_write; [exact MU | lia | rewrite Hl; lia | cbn [inside]; rewrite Hl; left; lia].
    - apply wmono_write. exact WM.
    - apply mem_inv_store; [exact MI|]. rewrite Hl.
      replace a with (p + 18 + (a - (p + 18))) by lia.
      apply (wr_at_store_ok rsegs mc (p + 18) (Z.of_nat 32) (a - (p + 18)) 1 XW); lia.
    - apply ly_rw_cb_eq; [rewrite upd_bytes_length; lia | |].
      + replace (wa a) with (wa (p + 18 + (a - (p + 18)))) by (f_equal; lia).
        apply bytes_at_write_inside; [exact XB | lia | rewrite Hl, XL; lia].
      + apply wr_at_write. exact XW.
    - apply (bytes_at_write_other rsegs mc a bs f fr FB); [lia | rewrite Hl; lia | rewrite FL, Hl; lia].
  Qed.

  Lemma ly_args : forall mc gj x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    LC mc gj BASE ->
    ly_hide (g <> 0 -> ly_al fr <> 0 ->
      Z.of_nat (length gb) = ly_al fr /\ bytes_at rsegs m g gb /\ ly_dj (p + 18) (p + 50) g (g + ly_al fr)) ->
    ly_hide (g <> 0 -> ly_al fr <> 0 -> ly_dj (bv_unsigned sp - 240) (bv_unsigned sp) g (g + ly_al fr)) ->
    memcpy_contract ->
    evt rsegs Q
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp x5 x6 x7 (Z_to_bv 64 g) (Z_to_bv 64 f)
               x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (p + 18)) (Z_to_bv 64 md) (Z_to_bv 64 p)
               s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x14d88) fc None mc (seg_rom rsegs)).
  Proof.
    intros mc gj x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 LCH GP DJ4 MEMC.
    pose proof LCH as (FR & ST & MU & WM & MI & BK & FB).
    pose proof (rd_byte rsegs mc f fr 16 FB ltac:(lia)) as R16.
    pose proof (rd_byte rsegs mc f fr 17 FB ltac:(lia)) as R17.
    step. rewrite (rc_eqb g 0) by lia.
    destruct (Z.eqb_spec g 0) as [G0|G0]; cbv iota.
    - eapply ly_epi. replace LAY with BASE; [exact LCH|].
      unfold LAY, BASE, ly_lay. rewrite (proj2 (Z.eqb_eq g 0) G0). reflexivity.
    - step. step. rewrite (rc_u8_eqb fr 17 0) by lia.
      destruct (Z.eqb_spec (rc_u8 fr 17) 0) as [A0|A0]; cbv iota.
      + eapply ly_epi. replace LAY with BASE; [exact LCH|].
        unfold LAY, BASE, ly_lay, ly_al. rewrite (proj2 (Z.eqb_eq _ 0) A0), orb_true_r. reflexivity.
      + destruct (GP G0 A0) as (GL & GBm & GD). specialize (DJ4 G0 A0). unfold ly_dj in GD, DJ4.
        pose proof (rc_u8_range fr 16) as RAO. pose proof (rc_u8_range fr 17) as RAL.
        unfold ly_ao, ly_al in *.
        assert (GBc : bytes_at rsegs mc g gb).
        { apply (bytes_at_transport rsegs _ m mc g gb GBm MU). cbn [disjoint_from]. lia. }
        clear GBm GP.
        destruct (ly_rw_split3 rsegs mc (p + 18) BASE (Z.to_nat (rc_u8 fr 16)) (Z.to_nat (rc_u8 fr 17)) BK
                    ltac:(lia)) as (B1 & B2 & B3).
        clear BK.
        rewrite Z2Nat.id in B2, B3 by lia. rewrite Z2Nat.id in B3 by lia.
        step. step. step. step.
        assert (UAO : bv_unsigned (zxb (nth 16 fr (Z_to_bv 8 0))) = rc_u8 fr 16) by (apply rc_zxb_u).
        assert (UAL : bv_unsigned (zxb (nth 17 fr (Z_to_bv 8 0))) = rc_u8 fr 17) by (apply rc_zxb_u).
        rewrite UAO.
        assert (UA0 : bv_unsigned (Z_to_bv 64 (p + 18 + rc_u8 fr 16)) = p + 18 + rc_u8 fr 16)
          by (apply unsigned_lit; lia).
        assert (UG : bv_unsigned (Z_to_bv 64 g) = g) by (apply unsigned_lit; lia).
        call MEMC.
        { rewrite UG. exact GBc. }
        { rewrite UAL. lia. }
        { rewrite UA0, UAL. exact B2. }
        { rewrite UA0, UAL, UG. lia. }
        { exact MI. }
        match goal with H : rw_cells rsegs ?mm (bv_unsigned (Z_to_bv 64 (p + 18 + rc_u8 fr 16))) _ |- _ =>
          rewrite UA0, UAL in H; rename H into BM end.
        assert (GLn : length gb = Z.to_nat (rc_u8 fr 17)) by lia.
        pose proof (ly_rw_join3 rsegs _ _ _ _ _ _ _ _ _ B1 BM B3 ltac:(lia) ltac:(lia) ltac:(lia)) as BJ.
        assert (EL : LAY = firstn (Z.to_nat (rc_u8 fr 16)) BASE ++ gb ++
                           skipn (Z.to_nat (rc_u8 fr 16) + Z.to_nat (rc_u8 fr 17)) BASE).
        { unfold LAY, ly_lay, ly_put, ly_ao, ly_al.
          rewrite (proj2 (Z.eqb_neq g 0) G0), (proj2 (Z.eqb_neq _ 0) A0). cbn [orb]. fold BASE.
          rewrite GLn. reflexivity. }
        eapply ly_epi. apply LC_intro; [ | | | | | rewrite EL; exact BJ | ]; eassumption.
  Qed.

  Lemma ly_cpy : forall mc gj X src sb x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    LC mc gj X -> bytes_at rsegs mc src sb -> length sb = 32%nat -> sb = BASE -> 0 <= src < 2^64 ->
    (src + 32 <= p + 18 \/ p + 50 <= src) ->
    ly_hide (g <> 0 -> ly_al fr <> 0 ->
      Z.of_nat (length gb) = ly_al fr /\ bytes_at rsegs m g gb /\ ly_dj (p + 18) (p + 50) g (g + ly_al fr)) ->
    ly_hide (g <> 0 -> ly_al fr <> 0 -> ly_dj (bv_unsigned sp - 240) (bv_unsigned sp) g (g + ly_al fr)) ->
    memcpy_contract ->
    evt rsegs Q
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp x5 x6 x7 (Z_to_bv 64 g) (Z_to_bv 64 f)
               x10 (Z_to_bv 64 src) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (p + 18)) (Z_to_bv 64 md) (Z_to_bv 64 p)
               s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x14d7c) fc None mc (seg_rom rsegs)).
  Proof.
    intros mc gj X src sb x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 LCH SB SL ESB RS DS GP DJ4 MEMC.
    pose proof LCH as (FR & ST & MU & WM & MI & BK & FB). clear LCH.
    step. step. step.
    assert (U18 : bv_unsigned (Z_to_bv 64 (p + 18)) = p + 18) by (apply unsigned_lit; lia).
    assert (U32 : bv_unsigned (Z_to_bv 64 32) = 32) by reflexivity.
    assert (US : bv_unsigned (Z_to_bv 64 src) = src) by (apply unsigned_lit; lia).
    call MEMC.
    { rewrite US. exact SB. }
    { rewrite U32. exact SL. }
    { rewrite U18, U32. exact BK. }
    { rewrite U18, U32, US. lia. }
    { exact MI. }
    match goal with H : rw_cells rsegs ?mm (bv_unsigned (Z_to_bv 64 (p + 18))) _ |- _ =>
      rewrite U18, U32 in H; change (Z.to_nat 32) with 32%nat in H; rename H into BM end.
    eapply ly_args; [ | exact GP | exact DJ4 | exact MEMC ].
    apply LC_intro; [ | | | | | rewrite <- ESB; exact BM | ]; eassumption.
  Qed.

  Lemma ly_loop : forall n j mc gj x1 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    (j + n = 16)%nat -> (0 < n)%nat -> ly_k fr = 1 -> LC mc gj (ly_dp j) ->
    ly_hide (g <> 0 -> ly_al fr <> 0 ->
      Z.of_nat (length gb) = ly_al fr /\ bytes_at rsegs m g gb /\ ly_dj (p + 18) (p + 50) g (g + ly_al fr)) ->
    ly_hide (g <> 0 -> ly_al fr <> 0 -> ly_dj (bv_unsigned sp - 240) (bv_unsigned sp) g (g + ly_al fr)) ->
    memcpy_contract ->
    evt rsegs Q
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp x5 x6 x7 (Z_to_bv 64 g) (Z_to_bv 64 f)
               (Z_to_bv 64 (p + 19 + 2 * Z.of_nat j)) (Z_to_bv 64 (p + 51)) (Z_to_bv 64 122) x13 x14 x15 x16 x17
               (Z_to_bv 64 (p + 18)) (Z_to_bv 64 md) (Z_to_bv 64 p)
               s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x14d14) fc None mc (seg_rom rsegs)).
  Proof.
    induction n as [|n IH]; intros j mc gj x1 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 Hjn Hn K1 LCH GP DJ4 MEMC;
      [lia|].
    pose proof (LC_sok mc gj (ly_dp j) (2 * Z.of_nat j) LCH ltac:(lia)) as HS1.
    step.
    pose proof (LC_store mc gj (ly_dp j) (p + 18 + 2 * Z.of_nat j) (le1 (Z_to_bv 64 0)) LCH (length_le1 _)
                  ltac:(lia)) as LC1.
    replace (Z.to_nat (p + 18 + 2 * Z.of_nat j - (p + 18))) with (2 * j)%nat in LC1 by lia.
    change (Z_to_bv 64 (p + 18 + 2 * Z.of_nat j)) with (wa (p + 18 + 2 * Z.of_nat j)) in LC1.
    remember (write_to_mem mc (wa (p + 18 + 2 * Z.of_nat j)) (le1 (Z_to_bv 64 0))) as mc1 eqn:E1.
    clear E1 HS1 LCH.
    pose proof (LC_sok mc1 gj _ (2 * Z.of_nat j + 1) LC1 ltac:(lia)) as HS2.
    step.
    pose proof (LC_store mc1 gj _ (p + 18 + (2 * Z.of_nat j + 1)) (le1 (Z_to_bv 64 122)) LC1 (length_le1 _)
                  ltac:(lia)) as LC2.
    replace (Z.to_nat (p + 18 + (2 * Z.of_nat j + 1) - (p + 18))) with (2 * j + 1)%nat in LC2 by lia.
    change (Z_to_bv 64 (p + 18 + (2 * Z.of_nat j + 1))) with (wa (p + 18 + (2 * Z.of_nat j + 1))) in LC2.
    remember (write_to_mem mc1 (wa (p + 18 + (2 * Z.of_nat j + 1))) (le1 (Z_to_bv 64 122))) as mc2 eqn:E2.
    clear E2 HS2 LC1.
    change (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0] in LC2.
    change (le1 (Z_to_bv 64 122)) with [Z_to_bv 8 122] in LC2.
    rewrite (ly_dp_step j ltac:(lia)) in LC2.
    step. step.
    rewrite (ly_eqb_near (p + 19 + 2 * Z.of_nat j + 2) (p + 51)) by lia.
    destruct (Nat.eq_dec j 15) as [J|J].
    - subst j. replace (p + 19 + 2 * Z.of_nat 15 + 2 =? p + 51) with true by (symmetry; apply Z.eqb_eq; lia).
      cbn [negb]. step.
      assert (EB : BASE = ly_desc) by (unfold BASE, ly_base; rewrite K1; reflexivity).
      rewrite ly_dp_16, <- EB in LC2.
      eapply ly_args; [exact LC2 | exact GP | exact DJ4 | exact MEMC].
    - replace (p + 19 + 2 * Z.of_nat j + 2 =? p + 51) with false by (symmetry; apply Z.eqb_neq; lia).
      cbn [negb]. replace (p + 19 + 2 * Z.of_nat j + 2) with (p + 19 + 2 * Z.of_nat (S j)) by lia.
      eapply (IH (S j)); [lia | lia | exact K1 | exact LC2 | exact GP | exact DJ4 | exact MEMC].
  Qed.
  Lemma LC_after_box : forall mc m' gj gj' X, LC mc gj X ->
    munch [(bv_unsigned sp - 240, bv_unsigned sp + -80); (bv_unsigned sp + -80, bv_unsigned sp + -80 + 32)] mc m' ->
    wmono rsegs mc m' -> mem_inv rsegs m' -> stk rsegs m' (bv_unsigned sp - 240) (bv_unsigned sp + -80) ->
    rw_cells rsegs m' (bv_unsigned sp + -80) [CB 32 gj'] -> LC m' gj' X.
  Proof.
    intros mc m' gj gj' X (FR & ST & MU & WM & MI & BK & FB) MUc WMc MIc STc GEN.
    destruct (ly_rw_split2 rsegs mc (bv_unsigned sp + -80) (bv_unsigned sp + -80 + 32) [CB 32 gj]
                [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] FR ltac:(cbn; lia)) as [_ FR2].
    apply LC_intro.
    - apply (ly_rw_join2 rsegs m' _ (bv_unsigned sp + -80 + 32) [CB 32 gj'] [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]);
        [exact GEN | cbn; lia |].
      apply (rw_cells_transport rsegs _ mc m' _ _ FR2 MUc WMc). cbn [disjoint_from cells_size csize]. lia.
    - exact STc.
    - apply (munch_trans _ m mc m' MU). eapply munch_weaken; [| exact MUc].
      unfold sub_fp. cbn [outside]. intros. lia.
    - apply (wmono_trans rsegs m mc m' WM WMc).
    - exact MIc.
    - apply (rw_cells_transport rsegs _ mc m' _ _ BK MUc WMc). cbn [disjoint_from cells_size csize]. lia.
    - apply (bytes_at_transport rsegs _ mc m' _ _ FB MUc). cbn [disjoint_from]. rewrite FL. lia.
  Qed.

  Lemma BASE_box : 3 <= ly_k fr <= 9 -> BASE = ly_Z md mb nb (ly_bb (ly_k fr)).
  Proof.
    intros KB. unfold BASE, ly_base.
    rewrite (proj2 (Z.eqb_neq (ly_k fr) 0) ltac:(lia)), (proj2 (Z.eqb_neq (ly_k fr) 1) ltac:(lia)),
      (proj2 (Z.eqb_neq (ly_k fr) 2) ltac:(lia)).
    reflexivity.
  Qed.

  Lemma ly_box : forall b mc gj x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    b = ly_bb (ly_k fr) -> 3 <= ly_k fr <= 9 -> LC mc gj ly_zero ->
    ly_hide (3 <= ly_k fr <= 9 -> md <> 0 ->
       md mod 8 = 0 /\ length mb = 296%nat /\ bytes_at rsegs m md mb /\
       ((ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
          name_ok nb /\ bytes_at rsegs m (rname mb) nb)) ->
    ly_hide (3 <= ly_k fr <= 9 -> md <> 0 ->
       ly_dj (bv_unsigned sp - 240) (bv_unsigned sp) md (md + 296) /\
       ((ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
          ly_dj (bv_unsigned sp - 240) (bv_unsigned sp) (rname mb) (rname mb + Z.of_nat (length nb)))) ->
    ly_hide (3 <= ly_k fr <= 9 -> md <> 0 -> ly_dj (p + 18) (p + 50) md (md + 296)) ->
    ly_hide (3 <= ly_k fr <= 9 -> md <> 0 -> (ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 ->
       rname mb <> 0 -> ly_dj (p + 18) (p + 50) (rname mb) (rname mb + Z.of_nat (length nb))) ->
    ly_hide (g <> 0 -> ly_al fr <> 0 ->
      Z.of_nat (length gb) = ly_al fr /\ bytes_at rsegs m g gb /\ ly_dj (p + 18) (p + 50) g (g + ly_al fr)) ->
    ly_hide (g <> 0 -> ly_al fr <> 0 -> ly_dj (bv_unsigned sp - 240) (bv_unsigned sp) g (g + ly_al fr)) ->
    reac_box_model_block_contract -> memcpy_contract ->
    evt rsegs Q
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp x5 x6 x7 (Z_to_bv 64 g) (Z_to_bv 64 f)
               x10 (Z_to_bv 64 b) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (p + 18)) (Z_to_bv 64 md)
               (Z_to_bv 64 p) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x14d64) fc None mc (seg_rom rsegs)).
  Proof.
    intros b mc gj x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 -> KB LCH MDP DJ5 DB3 DBN GP DJ4 BOX MEMC.
    pose proof LCH as (FR & ST & MU & WM & MI & BK & FB).
    destruct (ly_rw_split2 rsegs mc (bv_unsigned sp + -80) (bv_unsigned sp + -80 + 32) [CB 32 gj]
                [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] FR ltac:(cbn; lia)) as [GEN _].
    assert (BBR : 0 <= ly_bb (ly_k fr) <= 6) by (unfold ly_bb; repeat match goal with |- context [if ?c then _ else _] => destruct c end; lia).
    step. step. step.
    assert (US : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) = bv_unsigned sp + -80) by (apply unsigned_lit; lia).
    eapply evt_cut.
    { eapply (BOX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                md (ly_bb (ly_k fr)) (bv_unsigned sp + -80) mb nb gj).
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - lia.
      - lia.
      - lia.
      - rewrite US. Z.div_mod_to_equations. lia.
      - rewrite US. replace (bv_unsigned sp + -80 - 160) with (bv_unsigned sp - 240) by lia. exact ST.
      - intros M0. destruct (MDP KB M0) as (M8 & ML & MB & _). destruct (DJ5 KB M0) as (DS & _).
        specialize (DB3 KB M0). unfold ly_dj in DS, DB3. rewrite US.
        split; [exact M8|]. split; [exact ML|]. split; [|split; lia].
        apply (bytes_at_transport rsegs _ m mc _ _ MB MU). cbn [disjoint_from]. rewrite ML. lia.
      - intros M0 HB5 HH HR. destruct (MDP KB M0) as (_ & _ & _ & NM). destruct (NM HB5 HH HR) as (NO & NB).
        destruct (DJ5 KB M0) as (_ & DN). specialize (DN HB5 HH HR). specialize (DBN KB M0 HB5 HH HR).
        unfold ly_dj in DN, DBN. rewrite US.
        split; [exact NO|]. split; [|split; lia].
        apply (bytes_at_transport rsegs _ m mc _ _ NB MU). cbn [disjoint_from]. lia.
      - intros _. split; [exact GEN|]. rewrite US. split; [lia|].
        destruct (ly_rw_cb _ _ _ _ _ GEN) as (_ & _ & GW).
        apply (ly_wr_not_ro rsegs mc _ 32 JOIN_0013 64 GW MI ltac:(lia) ltac:(lia)); [| unfold JOIN_0013; lia ..].
        apply (ly_ro_range rsegs JOIN_0013 64). vm_compute. reflexivity.
      - exact MI. }
    intros ms' POST. unfold reac_box_model_block_post in POST.
    destruct POST as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                      -> & MW & WMc & MIc & STc).
    rewrite US in MW, STc. replace (bv_unsigned sp + -80 - 160) with (bv_unsigned sp - 240) in MW, STc by lia.
    replace (ret_pc (Z_to_bv 64 0x14d70)) with (Z_to_bv 64 0x14d70) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    assert (O0 : (bv_unsigned sp + -80 =? 0) = false) by (apply Z.eqb_neq; lia).
    rewrite O0, orb_false_r in MW. rewrite O0, orb_false_r.
    destruct (Z.eqb_spec md 0) as [M0|M0]; cbn [orb] in MW |- *.
    - assert (LC2 : LC m' gj ly_zero).
      { eapply LC_after_box; [exact LCH | | exact WMc | exact MIc | exact STc |].
        - eapply munch_weaken; [| exact MW]. unfold sub_fp. cbn [outside]. intros. lia.
        - apply (rw_cells_transport rsegs _ mc m' _ _ GEN MW WMc). cbn [disjoint_from cells_size csize]. lia. }
      step. step. change (bv_eqb (Z_to_bv 64 (-1)) (Z_to_bv 64 1)) with false. cbn [negb].
      assert (EB : BASE = ly_zero).
      { rewrite (BASE_box KB). unfold ly_Z. rewrite (proj2 (Z.eqb_eq md 0) M0). reflexivity. }
      rewrite <- EB in LC2. eapply ly_args; [exact LC2 | exact GP | exact DJ4 | exact MEMC].
    - destruct MW as (SB & MW).
      destruct (MDP KB M0) as (_ & ML & _ & _).
      pose proof (RcSynthLib.rs_synth_len mb (ly_bb (ly_k fr)) nb ML) as SL.
      destruct (ly_rw_cb _ _ _ _ _ GEN) as (_ & _ & GW).
      assert (GEN2 : rw_cells rsegs m' (bv_unsigned sp + -80) [CB 32 (synth mb (ly_bb (ly_k fr)) nb)]).
      { apply ly_rw_cb_eq; [exact SL | exact SB | exact (wr_at_transport rsegs mc m' _ _ GW WMc)]. }
      assert (LC2 : LC m' (synth mb (ly_bb (ly_k fr)) nb) ly_zero).
      { eapply LC_after_box; [exact LCH | exact MW | exact WMc | exact MIc | exact STc | exact GEN2]. }
      assert (RC : -1 <= rc mb (ly_bb (ly_k fr)) <= 1).
      { unfold rc. repeat match goal with |- context [if ?c then _ else _] => destruct c end; lia. }
      step. step. rewrite (ly_eqb_close (rc mb (ly_bb (ly_k fr))) 1) by lia.
      destruct (Z.eqb_spec (rc mb (ly_bb (ly_k fr))) 1) as [R1|R1]; cbn [negb].
      + step.
        eapply ly_cpy; [exact LC2 | exact SB | exact SL | | lia | lia | exact GP | exact DJ4 | exact MEMC].
        rewrite (BASE_box KB). unfold ly_Z. rewrite (proj2 (Z.eqb_neq md 0) M0), (proj2 (Z.eqb_eq _ 1) R1).
        reflexivity.
      + assert (EB : BASE = ly_zero).
        { rewrite (BASE_box KB). unfold ly_Z. rewrite (proj2 (Z.eqb_neq md 0) M0), (proj2 (Z.eqb_neq _ 1) R1).
          reflexivity. }
        assert (LC3 : LC m' (synth mb (ly_bb (ly_k fr)) nb) BASE) by (rewrite EB; exact LC2).
        eapply ly_args; [exact LC3 | exact GP | exact DJ4 | exact MEMC].
  Qed.
  Lemma ly_dispatch : forall mc gj x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    LC mc gj ly_zero -> ly_k fr <= 9 ->
    ly_hide (ly_k fr = 2 -> ly_tm fr + 32 <= 2^64 /\ length tb = 32%nat /\ ro_bytes rsegs (ly_tm fr) tb) ->
    ly_hide (ly_k fr = 2 -> ly_dj (p + 18) (p + 50) (ly_tm fr) (ly_tm fr + 32)) ->
    ly_hide (3 <= ly_k fr <= 9 -> md <> 0 ->
       md mod 8 = 0 /\ length mb = 296%nat /\ bytes_at rsegs m md mb /\
       ((ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
          name_ok nb /\ bytes_at rsegs m (rname mb) nb)) ->
    ly_hide (3 <= ly_k fr <= 9 -> md <> 0 ->
       ly_dj (bv_unsigned sp - 240) (bv_unsigned sp) md (md + 296) /\
       ((ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
          ly_dj (bv_unsigned sp - 240) (bv_unsigned sp) (rname mb) (rname mb + Z.of_nat (length nb)))) ->
    ly_hide (3 <= ly_k fr <= 9 -> md <> 0 -> ly_dj (p + 18) (p + 50) md (md + 296)) ->
    ly_hide (3 <= ly_k fr <= 9 -> md <> 0 -> (ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 ->
       rname mb <> 0 -> ly_dj (p + 18) (p + 50) (rname mb) (rname mb + Z.of_nat (length nb))) ->
    ly_hide (g <> 0 -> ly_al fr <> 0 ->
      Z.of_nat (length gb) = ly_al fr /\ bytes_at rsegs m g gb /\ ly_dj (p + 18) (p + 50) g (g + ly_al fr)) ->
    ly_hide (g <> 0 -> ly_al fr <> 0 -> ly_dj (bv_unsigned sp - 240) (bv_unsigned sp) g (g + ly_al fr)) ->
    reac_box_model_block_contract -> memcpy_contract ->
    evt rsegs Q
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp x5 x6 x7 (Z_to_bv 64 g) (Z_to_bv 64 f)
               x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (p + 18)) (Z_to_bv 64 md) (Z_to_bv 64 p)
               s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x14cdc) fc None mc (seg_rom rsegs)).
  Proof.
    intros mc gj x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 LCH K9 TM DB2 MDP DJ5 DB3 DBN GP DJ4
      BOX MEMC.
    pose proof LCH as (FR & ST & MU & WM & MI & BK & FB).
    pose proof (rd_byte rsegs mc f fr 2 FB ltac:(lia)) as R2.
    step. step. step. rewrite (rc_u8_gtu fr 2 9) by lia.
    replace (9 <? rc_u8 fr 2) with false by (symmetry; apply Z.ltb_ge; unfold ly_k in K9; lia). cbv iota.
    assert (KR : 0 <= ly_k fr) by (unfold ly_k; pose proof (rc_u8_range fr 2); lia).
    assert (KC : ly_k fr = 0 \/ ly_k fr = 1 \/ ly_k fr = 2 \/ 3 <= ly_k fr <= 9) by lia.
    destruct KC as [K|[K|[K|KB]]].
    - rewrite (rc_zxb_lit fr 2 _ K). do 8 step.
      eapply ly_args; [ | exact GP | exact DJ4 | exact MEMC].
      replace BASE with ly_zero; [exact LCH|]. unfold BASE, ly_base. rewrite K. reflexivity.
    - rewrite (rc_zxb_lit fr 2 _ K). do 8 step. step. step. step.
      replace (Z_to_bv 64 (p + 19)) with (Z_to_bv 64 (p + 19 + 2 * Z.of_nat 0)) by (f_equal; lia).
      eapply (ly_loop 16 0); [lia | lia | exact K | exact LCH | exact GP | exact DJ4 | exact MEMC].
    - rewrite (rc_zxb_lit fr 2 _ K). do 8 step.
      destruct (TM K) as (T32 & TL & RO). specialize (DB2 K). unfold ly_dj in DB2.
      destruct (ly_rd8 rsegs mc f fr FB FL) as (L & EL & HR).
      step. rewrite (ly_ld8 fr L FL EL). step.
      pose proof (ly_le_range (firstn 8 (skipn 8 fr))) as TR.
      assert (TR0 : 0 <= ly_tm fr) by (unfold ly_tm; lia).
      eapply ly_cpy; [exact LCH | | exact TL | | lia | lia | exact GP | exact DJ4 | exact MEMC].
      + apply ro_bytes_at; [exact MI | lia | rewrite TL; lia | exact RO].
      + unfold BASE, ly_base. rewrite K. reflexivity.
    - assert (KC : ly_k fr = 3 \/ ly_k fr = 4 \/ ly_k fr = 5 \/ ly_k fr = 6 \/ ly_k fr = 7 \/ ly_k fr = 8 \/
                   ly_k fr = 9) by lia.
      destruct KC as [K|[K|[K|[K|[K|[K|K]]]]]]; rewrite (rc_zxb_lit fr 2 _ K); do 8 step;
        repeat lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x14d64) _ _ _ _) => fail | _ => step end;
        (eapply ly_box; [unfold ly_bb; rewrite K; reflexivity | exact KB | exact LCH | exact MDP | exact DJ5
                        | exact DB3 | exact DBN | exact GP | exact DJ4 | exact BOX | exact MEMC]).
  Qed.
End L.

Theorem ctrl_lay_block_holds : memset_contract -> memcpy_contract -> reac_box_model_block_contract ->
  ctrl_lay_block_contract.
Proof.
  intros MEMS MEMC BOX. unfold ctrl_lay_block_contract, CTRL_LAY_BLOCK, CTRL_LAY_BLOCK_K.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    p f md g fr ob tb mb nb gb -> -> -> -> Rp Rf Rmd Rg SP16 ST DJ1 DJ2 DJ3 DJ4 DJ5 F8 F24 FL FB K9 AOL TM P0 P50 BLK
    DB1 DB2 DB3 DBN MDP GP MI.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof ST as (STlo & _ & _).
  assert (DJ1u : bv_unsigned sp <= p + 18 \/ p + 50 <= bv_unsigned sp - 240) by (unfold ly_dj in DJ1; lia).
  assert (DJ2u : bv_unsigned sp <= f \/ f + 24 <= bv_unsigned sp - 240) by (unfold ly_dj in DJ2; lia).
  assert (DB1u : p + 50 <= f \/ f + 24 <= p + 18) by (unfold ly_dj in DB1; lia).
  clear DJ1 DJ2 DB1.
  apply ly_hide_in in DJ3, DJ4, DJ5, TM, DB2, DB3, DBN, MDP, GP.
  pose proof (munch_refl [(p + 18, p + 50); (bv_unsigned sp - 240, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 80%nat ST.
  do 16 step.
  assert (U18 : bv_unsigned (Z_to_bv 64 (p + 18)) = p + 18) by (apply unsigned_lit; lia).
  assert (U32 : bv_unsigned (Z_to_bv 64 32) = 32) by reflexivity.
  assert (U0 : bv_unsigned (Z_to_bv 64 0) = 0) by reflexivity.
  call MEMS.
  { rewrite U18, U32. exact BLK. }
  { exact MI. }
  rewrite U18, U32, U0 in POST. change (Z.to_nat 32) with 32%nat in POST. change (0 mod 256) with 0 in POST.
  eapply ly_dispatch; try eassumption; try lia.
  unfold LC; refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))); eassumption.
Qed.
