From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcPorts RcPortsLib reac_ports_unknown_c.
Import ListNotations.
Open Scope Z_scope.

Section P.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p c : Z) (bs : list byte).

  Definition Qp : machine_state -> Prop :=
    fun ms' => exists (a2' a3' a4' a5' : word) (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (if pu_ok p bs then 4 * pu_nunk bs 12 else -1))
                    (Z_to_bv 64 c) a2' a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ munch (if c =? 0 then [] else [(c, c + 1)]) m m'
      /\ wmono rsegs m m'
      /\ (forall lo, stk rsegs m lo (bv_unsigned sp) -> stk rsegs m' lo (bv_unsigned sp))
      /\ (mem_inv rsegs m -> mem_inv rsegs m')
      /\ (c <> 0 -> bytes_at rsegs m' c [Z_to_bv 8 (if pu_ok p bs then pu_first bs 12 else 0)]).

  Lemma p_fin : forall mc v r a2' a3' a4' a5',
    rc_inv rsegs c m mc v ->
    r = Z_to_bv 64 (if pu_ok p bs then 4 * pu_nunk bs 12 else -1) ->
    v = (if pu_ok p bs then pu_first bs 12 else 0) ->
    Qp (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 r (Z_to_bv 64 c) a2' a3' a4' a5' a6 a7
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (ret_pc ra) fc None mc (seg_rom rsegs)).
  Proof.
    intros mc v r a2' a3' a4' a5' HI Hr Hv. subst r v.
    destruct (rc_inv_post rsegs c m mc _ HI) as (MU & WM & ST & MI & HB).
    exists a2', a3', a4', a5', mc. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    split; [intros lo; apply ST|]. split; [exact MI | exact HB].
  Qed.

  Ltac p_bad HI :=
    let Hok := fresh "Hok" in
    assert (Hok : pu_ok p bs = false) by (unfold pu_ok, pu_decl; decide_tests; reflexivity);
    apply evt_done; eapply p_fin; [exact HI | rewrite Hok; reflexivity | rewrite Hok; reflexivity].

  Lemma p_tail : forall j mc x5,
    (j < 12)%nat -> 0 <= p -> p + 20 <= 2^64 -> pu_ok p bs = true ->
    rc_inv rsegs c m mc (pu_first bs (S j)) ->
    ((S j < 12)%nat ->
      evt rsegs Qp
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (pu_nunk bs (S j))) (Z_to_bv 64 c) (Z_to_bv 64 (p + 20))
                 (Z_to_bv 64 (p + 8 + Z.of_nat (S j))) (Z_to_bv 64 4) x5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x158c8) fc None mc (seg_rom rsegs))) ->
    evt rsegs Qp
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (pu_nunk bs (S j))) (Z_to_bv 64 c) (Z_to_bv 64 (p + 20))
               (Z_to_bv 64 (p + 8 + Z.of_nat j)) (Z_to_bv 64 4) x5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x158e0) fc None mc (seg_rom rsegs)).
  Proof.
    intros j mc x5 Hj Hp H20 Hok HI K. pose proof (pu_nunk_range bs (S j)) as NR.
    step. step.
    rewrite (eqb_le64 (p + 8 + Z.of_nat j + 1) (p + 20)) by lia.
    destruct (Nat.eq_dec j 11) as [J|J].
    - subst j. replace (p + 8 + Z.of_nat 11 + 1 =? p + 20) with true by (symmetry; apply Z.eqb_eq; lia).
      cbn [negb]. step. rewrite (rc_slliw2 (pu_nunk bs 12)) by lia. step.
      apply evt_done. eapply p_fin; [exact HI | rewrite Hok; reflexivity | rewrite Hok; reflexivity].
    - replace (p + 8 + Z.of_nat j + 1 =? p + 20) with false by (symmetry; apply Z.eqb_neq; lia).
      cbn [negb]. replace (p + 8 + Z.of_nat j + 1) with (p + 8 + Z.of_nat (S j)) by lia.
      apply K. lia.
  Qed.

  Lemma p_loop : forall n j mc x5,
    (j + n = 12)%nat -> (0 < n)%nat ->
    0 <= p -> p + 20 <= 2^64 -> length bs = 20%nat -> 0 <= c < 2^64 ->
    (c <> 0 -> c + 1 <= p \/ p + 20 <= c) ->
    pu_ok p bs = true ->
    bytes_at rsegs mc p bs -> rc_inv rsegs c m mc (pu_first bs j) ->
    evt rsegs Qp
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (pu_nunk bs j)) (Z_to_bv 64 c) (Z_to_bv 64 (p + 20))
               (Z_to_bv 64 (p + 8 + Z.of_nat j)) (Z_to_bv 64 4) x5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x158c8) fc None mc (seg_rom rsegs)).
  Proof.
    induction n as [|n IH]; intros j mc x5 Hjn Hn Hp H20 Hlen Hc Hdis Hok HB HI; [lia|].
    pose proof (rd_byte rsegs mc p bs (8 + j) HB ltac:(lia)) as RD.
    pose proof (pu_nunk_range bs j) as NR. pose proof (rc_u8_range bs (8 + j)) as UR.
    step. step. rewrite (rc_u8_ltu bs (8 + j) 4) by lia.
    destruct (Z.ltb_spec (rc_u8 bs (8 + j)) 4) as [K|K]; cbv iota.
    - assert (HI' : rc_inv rsegs c m mc (pu_first bs (S j))).
      { apply (rc_inv_same rsegs c m mc (pu_first bs j)); [right; symmetry; apply pu_first_keep; lia | exact HI]. }
      rewrite <- (pu_nunk_known bs j K).
      apply (p_tail j); [lia | lia | lia | exact Hok | exact HI' |].
      intros HS. apply (IH (S j)); try assumption; lia.
    - step. rewrite (rc_eqb c 0) by lia.
      destruct (Z.eqb_spec c 0) as [C0|C0]; cbv iota.
      + assert (HI' : rc_inv rsegs c m mc (pu_first bs (S j))).
        { apply (rc_inv_same rsegs c m mc (pu_first bs j)); [left; exact C0 | exact HI]. }
        step. rewrite (rc_addiw (pu_nunk bs j) 1) by lia. rewrite <- (pu_nunk_unk bs j K).
        apply (p_tail j); [lia | lia | lia | exact Hok | exact HI' |].
        intros HS. apply (IH (S j)); try assumption; lia.
      + step. rewrite (rc_eqb (pu_nunk bs j) 0) by lia.
        destruct (Z.eqb_spec (pu_nunk bs j) 0) as [N0|N0]; cbn [negb].
        * pose proof (rc_inv_store_ok rsegs c m mc _ C0 HI) as SO.
          step.
          rewrite le1_zxb.
          assert (HI' : rc_inv rsegs c m (write_to_mem mc (Z_to_bv 64 c) [nth (8 + j) bs (Z_to_bv 8 0)])
                          (pu_first bs (S j))).
          { rewrite (pu_first_new bs j N0 K). exact (rc_inv_store rsegs c m mc _ _ C0 Hc HI). }
          assert (HB' : bytes_at rsegs (write_to_mem mc (Z_to_bv 64 c) [nth (8 + j) bs (Z_to_bv 8 0)]) p bs).
          { apply (bytes_at_write_other rsegs mc c); [exact HB | lia | cbn [length]; lia |].
            rewrite Hlen. cbn [length]. destruct (Hdis C0); lia. }
          set (mc' := write_to_mem mc (Z_to_bv 64 c) [nth (8 + j) bs (Z_to_bv 8 0)]) in *. clearbody mc'.
          step. rewrite (rc_addiw (pu_nunk bs j) 1) by lia. rewrite <- (pu_nunk_unk bs j K).
          apply (p_tail j); [lia | lia | lia | exact Hok | exact HI' |].
          intros HS. apply (IH (S j)); try assumption; lia.
        * assert (HI' : rc_inv rsegs c m mc (pu_first bs (S j))).
          { apply (rc_inv_same rsegs c m mc (pu_first bs j)); [right; symmetry; apply pu_first_keep; lia | exact HI]. }
          step. rewrite (rc_addiw (pu_nunk bs j) 1) by lia. rewrite <- (pu_nunk_unk bs j K).
          apply (p_tail j); [lia | lia | lia | exact Hok | exact HI' |].
          intros HS. apply (IH (S j)); try assumption; lia.
  Qed.

  Lemma p_body : forall mc x0 x3 x4 x5,
    0 <= p < 2^64 -> 0 <= c < 2^64 ->
    (p <> 0 -> p + 20 <= 2^64 /\ length bs = 20%nat /\ bytes_at rsegs mc p bs) ->
    (c <> 0 -> p <> 0 -> c + 1 <= p \/ p + 20 <= c) ->
    rc_inv rsegs c m mc 0 ->
    evt rsegs Qp
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x0 (Z_to_bv 64 c) (Z_to_bv 64 p) x3 x4 x5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x15878) fc None mc (seg_rom rsegs)).
  Proof.
    intros mc x0 x3 x4 x5 Rp Rc HP HD HI.
    step. step. rewrite (rc_eqb p 0) by lia.
    destruct (Z.eqb_spec p 0) as [P0|P0]; cbv iota.
    - step. p_bad HI.
    - destruct (HP P0) as (H20 & Hlen & HB).
      pose proof (rd_byte rsegs mc p bs 0 HB ltac:(lia)) as RD0.
      pose proof (rd_byte rsegs mc p bs 1 HB ltac:(lia)) as RD1.
      pose proof (rd_byte rsegs mc p bs 4 HB ltac:(lia)) as RD4.
      step. step. step. rewrite (rc_u8_eqb bs 0 1) by lia.
      destruct (Z.eqb_spec (rc_u8 bs 0) 1) as [B0|B0]; cbn [negb]; [|step; p_bad HI].
      step. step. step. rewrite (rc_u8_eqb bs 1 3) by lia.
      destruct (Z.eqb_spec (rc_u8 bs 1) 3) as [B1|B1]; cbn [negb]; [|step; p_bad HI].
      step. step. step. step.
      rewrite rc_zxb_u. change (bv_unsigned (nth 4 bs (Z_to_bv 8 0))) with (rc_u8 bs 4).
      rewrite (rc_decl_ltu (rc_u8 bs 4)) by (apply rc_u8_range).
      destruct (Z.leb_spec 128 (rc_u8 bs 4)) as [D1|D1]; destruct (Z.leb_spec (rc_u8 bs 4) 132) as [D2|D2];
        cbn [andb negb]; [|step; p_bad HI | step; p_bad HI | step; p_bad HI].
      assert (U4 : rc_u8 bs 4 = 128 \/ rc_u8 bs 4 = 129 \/ rc_u8 bs 4 = 130 \/ rc_u8 bs 4 = 131 \/ rc_u8 bs 4 = 132)
        by lia.
      assert (Hdis : c <> 0 -> c + 1 <= p \/ p + 20 <= c) by (intros Hc0; exact (HD Hc0 P0)).
      destruct U4 as [U4|[U4|[U4|[U4|U4]]]]; rewrite U4; step; step; step; step;
        [ if_false | if_true; step; p_bad HI | if_false | if_true; step; p_bad HI | if_false ].
      all: assert (Hok : pu_ok p bs = true) by (unfold pu_ok, pu_decl; decide_tests; reflexivity);
        step; step; step; step; replace (p + 8) with (p + 8 + Z.of_nat 0) by lia;
        apply (p_loop 12 0 mc x5); [lia | lia | lia | exact H20 | exact Hlen | exact Rc | exact Hdis | exact Hok
                                   | exact HB | exact HI].
  Qed.
End P.

Theorem reac_ports_unknown_holds : reac_ports_unknown_contract.
Proof.
  unfold reac_ports_unknown_contract, REAC_PORTS_UNKNOWN.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p c bs
    Ha0 Ha1 HP HC.
  pose proof (rc_word_range a0 p Ha0) as Rp. pose proof (rc_word_range a1 c Ha1) as Rc.
  apply rc_word in Ha0. apply rc_word in Ha1. subst a0 a1.
  step. step.
  destruct (Z.eq_dec c 0) as [C0|C0].
  - assert (B : bv_eqb (Z_to_bv 64 c) (Z_to_bv 64 0) = true) by (rewrite rc_eqb by lia; apply Z.eqb_eq; exact C0).
    rewrite B. cbv iota.
    apply (p_body ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p c bs
             m (Z_to_bv 64 p) a3 a4 a5); [exact Rp | exact Rc | exact HP | |].
    + intros Hc0. contradiction.
    + left. split; [exact C0 | reflexivity].
  - assert (B : bv_eqb (Z_to_bv 64 c) (Z_to_bv 64 0) = false) by (rewrite rc_eqb by lia; apply Z.eqb_neq; exact C0).
    rewrite B. cbv iota.
    destruct (HC C0) as [HW HD]. pose proof (rc_store_ok rsegs m c HW) as SO.
    step.
    match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m (Z_to_bv 64 c) ?l) _) =>
      replace l with [Z_to_bv 8 0] by reflexivity end.
    apply (p_body ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p c bs
             (write_to_mem m (Z_to_bv 64 c) [Z_to_bv 8 0]) (Z_to_bv 64 p) a3 a4 a5);
      [exact Rp | exact Rc | | |].
    + intros P0. destruct (HP P0) as (H20 & Hlen & HB). split; [exact H20|]. split; [exact Hlen|].
      apply (bytes_at_write_other rsegs m c); [exact HB | lia | cbn [length]; lia |].
      rewrite Hlen. cbn [length]. destruct (HD P0); lia.
    + intros _ P0. exact (HD P0).
    + exact (rc_inv_first rsegs c m (Z_to_bv 8 0) C0 Rc HW).
Qed.
