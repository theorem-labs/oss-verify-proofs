From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import RcModel RcLib RcLeaf RcLeafLib reac_ports_parse_c.
Import ListNotations.
Open Scope Z_scope.

Section Body.
  Variables (ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p q : Z) (bs : list byte).
  Hypothesis Hp : 0 < p < 2^64.
  Hypothesis Hq : 0 < q < 2^64.
  Hypothesis Hlen : length bs = 20%nat.
  Hypothesis HB : bytes_at rsegs m p bs.
  Hypothesis HW : wr_at rsegs m q 12.
  Hypothesis Hd : q + 12 <= p \/ p + 20 <= q.
  Hypothesis Hok : ports_ok p q bs = true.

  Definition Qp := reac_ports_parse_post ra sp gp tp t1 t2 s0 s1 (Z_to_bv 64 q) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 F fc m p q bs.

  Lemma tail : forall x2 x5 x6 x7 y0,
    evt rsegs Qp
      (MS (mkR ra sp gp tp y0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 q) x2 (Z_to_bv 64 (n_out bs))
               (Z_to_bv 64 (n_in bs)) x5 x6 x7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1675c) fc None m (seg_rom rsegs)).
  Proof.
    intros x2 x5 x6 x7 y0.
    pose proof (rcl_cnt_range is_in bs 12) as RI. pose proof (rcl_cnt_range is_out bs 12) as RO.
    change (cnt is_in bs 12) with (n_in bs) in RI. change (cnt is_out bs 12) with (n_out bs) in RO.
    change (Z.of_nat 12) with 12 in RI, RO.
    pose proof (rcl_store_ok rsegs m q 12 4 HW ltac:(lia)) as ST0.
    pose proof HW as (HWl & HWh & _). pose proof HB as (HBl & HBh & _). rewrite Hlen in HBh.
    step. step. step.
    rewrite (unsigned_lit (n_in bs)), (unsigned_lit (n_out bs)) by lia.
    rewrite !Z.shiftl_mul_pow2 by lia.
    replace (n_in bs * 2^2) with (4 * n_in bs) by lia. replace (n_out bs * 2^2) with (4 * n_out bs) by lia.
    step.
    assert (ST1 : store_ok rsegs (write_to_mem m (Z_to_bv 64 q) (le4 (Z_to_bv 64 (4 * n_in bs)))) (wa (q + 4)) 4 = true).
    { apply (wr_at_store_ok rsegs _ q 12 4 4); [apply wr_at_write; exact HW | lia | lia]. }
    step.
    assert (HB2 : bytes_at rsegs (write_to_mem (write_to_mem m (Z_to_bv 64 q) (le4 (Z_to_bv 64 (4 * n_in bs))))
                    (Z_to_bv 64 (q + 4)) (le4 (Z_to_bv 64 (4 * n_out bs)))) p bs).
    { change (Z_to_bv 64 (q + 4)) with (wa (q + 4)). change (Z_to_bv 64 q) with (wa q).
      apply bytes_at_write_other; [ | lia | rewrite ?length_le4; lia | rewrite ?length_le4, Hlen; lia].
      apply bytes_at_write_other; [exact HB | lia | rewrite ?length_le4; lia | rewrite ?length_le4, Hlen; lia]. }
    pose proof (rd_byte rsegs _ p bs 7 HB2 ltac:(lia)) as R7.
    step. step.
    pose proof (byte_range (nth 7 bs (Z_to_bv 8 0))) as B7.
    unfold zxb. rewrite (unsigned_lit (bv_unsigned (nth 7 bs (Z_to_bv 8 0)))) by lia.
    rewrite Z.shiftl_mul_pow2 by lia.
    change (bv_unsigned (nth 7 bs (Z_to_bv 8 0))) with (bt bs 7) in *.
    replace (bt bs 7 * 2^4) with (16 * bt bs 7) by lia.
    assert (ST2 : store_ok rsegs (write_to_mem (write_to_mem m (Z_to_bv 64 q) (le4 (Z_to_bv 64 (4 * n_in bs))))
                    (Z_to_bv 64 (q + 4)) (le4 (Z_to_bv 64 (4 * n_out bs)))) (wa (q + 8)) 4 = true).
    { apply (wr_at_store_ok rsegs _ q 12 8 4%nat); [apply wr_at_write, wr_at_write; exact HW | lia | lia]. }
    step. step. step.
    apply evt_done. unfold Qp, reac_ports_parse_post. rewrite Hok.
    do 8 eexists. split; [reflexivity|].
    change (Z_to_bv 64 (q + 8)) with (wa (q + 8)). change (Z_to_bv 64 (q + 4)) with (wa (q + 4)).
    change (Z_to_bv 64 q) with (wa q).
    split.
    { apply bytes_at_write_other; [ | lia | rewrite ?length_le4; lia | rewrite ?length_le4; lia].
      apply bytes_at_write_other; [ | lia | rewrite ?length_le4; lia | rewrite ?length_le4; lia].
      apply bytes_at_write_same; rewrite ?length_le4; lia. }
    split.
    { apply bytes_at_write_other; [ | lia | rewrite ?length_le4; lia | rewrite ?length_le4; lia].
      apply bytes_at_write_same; rewrite ?length_le4; lia. }
    split; [apply bytes_at_write_same; rewrite ?length_le4; lia|].
    split.
    { apply munch_write; [ | lia | rewrite ?length_le4; lia | cbn [inside]; rewrite ?length_le4; lia].
      apply munch_write; [ | lia | rewrite ?length_le4; lia | cbn [inside]; rewrite ?length_le4; lia].
      apply munch_write; [apply munch_refl | lia | rewrite ?length_le4; lia | cbn [inside]; rewrite ?length_le4; lia]. }
    split; [apply wmono_write, wmono_write, wmono_write, wmono_refl|].
    intros HMI. apply mem_inv_store; [ | rewrite length_le4; exact ST2].
    apply mem_inv_store; [ | rewrite length_le4; exact ST1].
    apply mem_inv_store; [exact HMI | rewrite length_le4; exact ST0].
  Qed.

  Lemma loop : forall n i y0,
    (i + n = 12)%nat -> (0 < n)%nat ->
    evt rsegs Qp
      (MS (mkR ra sp gp tp y0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 q) (Z_to_bv 64 (p + 8 + Z.of_nat i))
               (Z_to_bv 64 (cnt is_out bs i)) (Z_to_bv 64 (cnt is_in bs i)) (Z_to_bv 64 (p + 20))
               (Z_to_bv 64 2) (Z_to_bv 64 1) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x16738) fc None m (seg_rom rsegs)).
  Proof.
    pose proof HB as (HBl & HBh & _). rewrite Hlen in HBh.
    induction n as [|n IH]; intros i y0 Hin Hn; [lia|].
    assert (K : forall y, evt rsegs Qp
      (MS (mkR ra sp gp tp y t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 q) (Z_to_bv 64 (p + 8 + Z.of_nat i))
               (Z_to_bv 64 (cnt is_out bs (S i))) (Z_to_bv 64 (cnt is_in bs (S i))) (Z_to_bv 64 (p + 20))
               (Z_to_bv 64 2) (Z_to_bv 64 1) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x16754) fc None m (seg_rom rsegs))).
    { intros y. step. step.
      rewrite (eqb_le64 (p + 8 + Z.of_nat i + 1) (p + 20)) by lia.
      destruct n as [|n].
      - replace (p + 8 + Z.of_nat i + 1 =? p + 20) with true by (symmetry; apply Z.eqb_eq; lia).
        cbn [negb]. replace i with 11%nat in * by lia.
        exact (tail _ _ _ _ _).
      - replace (p + 8 + Z.of_nat i + 1 =? p + 20) with false by (symmetry; apply Z.eqb_neq; lia).
        cbn [negb].
        replace (p + 8 + Z.of_nat i + 1) with (p + 8 + Z.of_nat (S i)) by lia.
        apply (IH (S i)); lia. }
    pose proof (rd_byte rsegs m p bs (8 + i) HB ltac:(lia)) as RD.
    pose proof (byte_range (nth (8 + i) bs (Z_to_bv 8 0))) as BC.
    step. step.
    rewrite (rcl_zxb_eqb _ 2) by lia.
    change (bv_unsigned (nth (8 + i) bs (Z_to_bv 8 0))) with (bt bs (8 + i)) in *.
    destruct (Z.eqb_spec (bt bs (8 + i)) 2) as [C2|C2]; cbn [negb].
    - assert (IN : is_in (bt bs (8 + i)) = true) by (unfold is_in; rewrite C2; reflexivity).
      assert (OUT : is_out (bt bs (8 + i)) = false) by (unfold is_out; rewrite C2; reflexivity).
      step. step.
      replace (cnt is_in bs i + 1) with (cnt is_in bs (S i)) by (rewrite rcl_cnt_S, IN; reflexivity).
      replace (cnt is_out bs i) with (cnt is_out bs (S i)) by (rewrite rcl_cnt_S, OUT; lia).
      apply K.
    - step.
      rewrite (rcl_zxb_eqb _ 1) by lia.
      change (bv_unsigned (nth (8 + i) bs (Z_to_bv 8 0))) with (bt bs (8 + i)).
      destruct (Z.eqb_spec (bt bs (8 + i)) 1) as [C1|C1]; cbn [negb].
      + assert (IN : is_in (bt bs (8 + i)) = false) by (unfold is_in; rewrite C1; reflexivity).
        assert (OUT : is_out (bt bs (8 + i)) = true) by (unfold is_out; rewrite C1; reflexivity).
        step.
        replace (cnt is_out bs i + 1) with (cnt is_out bs (S i)) by (rewrite rcl_cnt_S, OUT; reflexivity).
        replace (cnt is_in bs i) with (cnt is_in bs (S i)) by (rewrite rcl_cnt_S, IN; lia).
        apply K.
      + step.
        rewrite (rcl_zxb_eqb _ 0) by lia.
        change (bv_unsigned (nth (8 + i) bs (Z_to_bv 8 0))) with (bt bs (8 + i)).
        destruct (Z.eqb_spec (bt bs (8 + i)) 0) as [C0|C0]; cbn [negb].
        * assert (IN : is_in (bt bs (8 + i)) = true) by (unfold is_in; rewrite C0; reflexivity).
          assert (OUT : is_out (bt bs (8 + i)) = false) by (unfold is_out; rewrite C0; reflexivity).
          step. step.
          replace (cnt is_in bs i + 1) with (cnt is_in bs (S i)) by (rewrite rcl_cnt_S, IN; reflexivity).
          replace (cnt is_out bs i) with (cnt is_out bs (S i)) by (rewrite rcl_cnt_S, OUT; lia).
          apply K.
        * assert (IN : is_in (bt bs (8 + i)) = false)
            by (unfold is_in; rewrite (proj2 (Z.eqb_neq _ _) C0), (proj2 (Z.eqb_neq _ _) C2); reflexivity).
          assert (OUT : is_out (bt bs (8 + i)) = false) by (unfold is_out; apply Z.eqb_neq; exact C1).
          replace (cnt is_in bs i) with (cnt is_in bs (S i)) by (rewrite rcl_cnt_S, IN; lia).
          replace (cnt is_out bs i) with (cnt is_out bs (S i)) by (rewrite rcl_cnt_S, OUT; lia).
          apply K.
  Qed.
End Body.

Theorem reac_ports_parse_holds : reac_ports_parse_contract.
Proof.
  unfold reac_ports_parse_contract, REAC_PORTS_PARSE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    p q bs -> -> Hp Hq HR HW.
  destruct (Z.eqb_spec p 0) as [P0|P0].
  - subst p. step. step. rewrite (rcl_eqb 0 0) by lia. cbn [Z.eqb]. step. step.
    apply evt_done. unfold reac_ports_parse_post.
    replace (ports_ok 0 q bs) with false by reflexivity.
    do 8 eexists. split; reflexivity.
  - destruct (Z.eqb_spec q 0) as [Q0|Q0].
    + subst q. step. step. rewrite (rcl_eqb p 0) by lia.
      replace (p =? 0) with false by (symmetry; apply Z.eqb_neq; exact P0). cbn [negb].
      step. rewrite (rcl_eqb 0 0) by lia. cbn [Z.eqb]. step. step.
      apply evt_done. unfold reac_ports_parse_post.
      replace (ports_ok p 0 bs) with false by (unfold ports_ok; rewrite (proj2 (Z.eqb_neq _ _) P0); reflexivity).
      do 8 eexists. split; reflexivity.
    + destruct (HR P0 Q0) as [Hlen HB]. destruct (HW P0 Q0) as (Hq4 & HWq & Hd).
      pose proof HB as (HBl & HBh & _). rewrite Hlen in HBh.
      pose proof (rd_byte rsegs m p bs 0 HB ltac:(lia)) as R0.
      pose proof (rd_byte rsegs m p bs 1 HB ltac:(lia)) as R1.
      pose proof (rd_byte rsegs m p bs 4 HB ltac:(lia)) as R4.
      pose proof (byte_range (nth 0 bs (Z_to_bv 8 0))) as B0.
      pose proof (byte_range (nth 1 bs (Z_to_bv 8 0))) as B1.
      pose proof (byte_range (nth 4 bs (Z_to_bv 8 0))) as B4.
      change (bv_unsigned (nth 0 bs (Z_to_bv 8 0))) with (bt bs 0) in B0.
      change (bv_unsigned (nth 1 bs (Z_to_bv 8 0))) with (bt bs 1) in B1.
      change (bv_unsigned (nth 4 bs (Z_to_bv 8 0))) with (bt bs 4) in B4.
      step. step. rewrite (rcl_eqb p 0) by lia.
      replace (p =? 0) with false by (symmetry; apply Z.eqb_neq; exact P0). cbn [negb].
      step. rewrite (rcl_eqb q 0) by lia.
      replace (q =? 0) with false by (symmetry; apply Z.eqb_neq; exact Q0). cbn [negb].
      step. step. step.
      rewrite (rcl_zxb_eqb _ 1) by lia.
      change (bv_unsigned (nth 0 bs (Z_to_bv 8 0))) with (bt bs 0).
      destruct (Z.eqb_spec (bt bs 0) 1) as [E0|E0]; cbn [negb].
      * step. step. step.
        rewrite (rcl_zxb_eqb _ 3) by lia.
        change (bv_unsigned (nth 1 bs (Z_to_bv 8 0))) with (bt bs 1).
        destruct (Z.eqb_spec (bt bs 1) 3) as [E1|E1]; cbn [negb].
        -- step. step. step. step.
           unfold zxb. rewrite (unsigned_lit (bv_unsigned (nth 4 bs (Z_to_bv 8 0))))
             by (pose proof (byte_range (nth 4 bs (Z_to_bv 8 0))); lia).
           change (bv_unsigned (nth 4 bs (Z_to_bv 8 0))) with (bt bs 4).
           assert (Pf : (p =? 0) = false) by (apply Z.eqb_neq; exact P0).
           assert (Qf : (q =? 0) = false) by (apply Z.eqb_neq; exact Q0).
           destruct (Z_le_gt_dec 128 (bt bs 4)) as [L1|L1]; [destruct (Z_le_gt_dec (bt bs 4) 132) as [L2|L2]|].
           ++ assert (X : bt bs 4 = 128 \/ bt bs 4 = 129 \/ bt bs 4 = 130 \/ bt bs 4 = 131 \/ bt bs 4 = 132) by lia.
              destruct X as [X|[X|[X|[X|X]]]]; rewrite X; rc_vm; step; step; step; step; rc_vm.
              ** step. step. step. step. step. step.
                 assert (Hok : ports_ok p q bs = true) by (unfold ports_ok, decl; rewrite Pf, Qf, E0, E1, X; reflexivity).
                 replace (p + 8) with (p + 8 + Z.of_nat 0) by lia.
                 eapply (loop ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p q bs) with (n := 12%nat) (i := 0%nat);
                   first [ lia | exact Hlen | exact HB | exact HWq | exact Hd | exact Hok | exact MI | reflexivity ].
              ** step. step.
                 apply evt_done. unfold reac_ports_parse_post.
                 replace (ports_ok p q bs) with false by (unfold ports_ok, decl; rewrite Pf, Qf, E0, E1, X; reflexivity).
                 do 8 eexists. split; reflexivity.
              ** step. step. step. step. step. step.
                 assert (Hok : ports_ok p q bs = true) by (unfold ports_ok, decl; rewrite Pf, Qf, E0, E1, X; reflexivity).
                 replace (p + 8) with (p + 8 + Z.of_nat 0) by lia.
                 eapply (loop ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p q bs) with (n := 12%nat) (i := 0%nat);
                   first [ lia | exact Hlen | exact HB | exact HWq | exact Hd | exact Hok | exact MI | reflexivity ].
              ** step. step.
                 apply evt_done. unfold reac_ports_parse_post.
                 replace (ports_ok p q bs) with false by (unfold ports_ok, decl; rewrite Pf, Qf, E0, E1, X; reflexivity).
                 do 8 eexists. split; reflexivity.
              ** step. step. step. step. step. step.
                 assert (Hok : ports_ok p q bs = true) by (unfold ports_ok, decl; rewrite Pf, Qf, E0, E1, X; reflexivity).
                 replace (p + 8) with (p + 8 + Z.of_nat 0) by lia.
                 eapply (loop ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p q bs) with (n := 12%nat) (i := 0%nat);
                   first [ lia | exact Hlen | exact HB | exact HWq | exact Hd | exact Hok | exact MI | reflexivity ].
           ++ rewrite (rcl_out128 (bt bs 4)) by lia. cbn [negb].
              step. step.
              apply evt_done. unfold reac_ports_parse_post.
              replace (ports_ok p q bs) with false by (unfold ports_ok, decl; rewrite Pf, Qf, E0, E1;
                rewrite (proj2 (Z.eqb_neq (bt bs 4) 128) ltac:(lia)), (proj2 (Z.eqb_neq (bt bs 4) 130) ltac:(lia)),
                  (proj2 (Z.eqb_neq (bt bs 4) 132) ltac:(lia)); reflexivity).
              do 8 eexists. split; reflexivity.
           ++ rewrite (rcl_out128 (bt bs 4)) by lia. cbn [negb].
              step. step.
              apply evt_done. unfold reac_ports_parse_post.
              replace (ports_ok p q bs) with false by (unfold ports_ok, decl; rewrite Pf, Qf, E0, E1;
                rewrite (proj2 (Z.eqb_neq (bt bs 4) 128) ltac:(lia)), (proj2 (Z.eqb_neq (bt bs 4) 130) ltac:(lia)),
                  (proj2 (Z.eqb_neq (bt bs 4) 132) ltac:(lia)); reflexivity).
              do 8 eexists. split; reflexivity.
        -- step. step.
           apply evt_done. unfold reac_ports_parse_post.
           replace (ports_ok p q bs) with false by (unfold ports_ok, decl;
             rewrite (proj2 (Z.eqb_neq _ _) P0), (proj2 (Z.eqb_neq _ _) Q0), E0, (proj2 (Z.eqb_neq _ _) E1); reflexivity).
           do 8 eexists. split; reflexivity.
      * step. step.
        apply evt_done. unfold reac_ports_parse_post.
        replace (ports_ok p q bs) with false by (unfold ports_ok, decl;
          rewrite (proj2 (Z.eqb_neq _ _) P0), (proj2 (Z.eqb_neq _ _) Q0), (proj2 (Z.eqb_neq _ _) E0); reflexivity).
        do 8 eexists. split; reflexivity.
Qed.
