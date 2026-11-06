From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_grant.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import RcModel RcLib RcFin RcFinLib ctrl_finish_c.
Import ListNotations.
Open Scope Z_scope.

Section Fin.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (p : Z).
  Hypothesis Hp : 0 < p.
  Hypothesis Hp50 : p + 50 <= 2^64.

  Definition Qb (mm : word -> option byte) (bs : list byte) (y5 y6 : word) : machine_state -> Prop :=
    fun ms' => exists a1' a2' a3' a4' : word,
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1' a2' a3' a4' y5 y6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None
               (write_to_mem mm (wa (p + 18 + Z.of_nat 31)) [Z_to_bv 8 ((- psum bs 31) mod 256)]) (seg_rom rsegs).

  Lemma blk_loop : forall mm bs y5 y6,
    length bs = 32%nat -> bytes_at rsegs mm (p + 18) bs -> wr_at rsegs mm (p + 18) 32 ->
    forall k i x4, (i + k = 31)%nat -> (0 < k)%nat ->
    evt rsegs (Qb mm bs y5 y6)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 (psum bs i)) (Z_to_bv 64 (p + 18 + Z.of_nat i))
               (Z_to_bv 64 (p + 49)) x4 y5 y6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14300) fc None mm (seg_rom rsegs)).
  Proof.
    intros mm bs y5 y6 Hl HB HW. induction k as [|k IH]; intros i x4 Hik Hk; [lia|].
    pose proof (rd_byte rsegs mm (p + 18) bs i HB ltac:(lia)) as RD.
    step. step. step. step.
    rewrite psum_S_zxb.
    rewrite (rcf_eqb (p + 18 + Z.of_nat i + 1) (p + 49)) by lia.
    destruct k as [|k].
    - replace (p + 18 + Z.of_nat i + 1 =? p + 49) with true by (symmetry; apply Z.eqb_eq; lia).
      cbn [negb]. cbv iota.
      replace i with 30%nat in * by lia.
      assert (HS : store_ok rsegs mm (wa (p + 49)) 1 = true).
      { replace (p + 49) with (p + 18 + 31) by lia. apply (wr_at_store_ok rsegs mm (p + 18) 32 31 1 HW); lia. }
      step. step. step.
      pose proof (psum_range bs 31) as R31. change (Z.of_nat 31) with 31 in R31.
      rewrite (rcf_neg_byte (psum bs 31)) by lia.
      replace (Z_to_bv 64 (p + 49)) with (wa (p + 18 + Z.of_nat 31)) by (unfold wa; f_equal; lia).
      apply evt_done. unfold Qb. do 4 eexists. reflexivity.
    - replace (p + 18 + Z.of_nat i + 1 =? p + 49) with false by (symmetry; apply Z.eqb_neq; lia).
      cbn [negb]. cbv iota.
      replace (p + 18 + Z.of_nat i + 1) with (p + 18 + Z.of_nat (S i)) by lia.
      apply (IH (S i)); lia.
  Qed.

  Lemma blk : forall mm bs y1 y2 y3 y4 y5 y6,
    length bs = 32%nat -> bytes_at rsegs mm (p + 18) bs -> wr_at rsegs mm (p + 18) 32 ->
    evt rsegs (Qb mm bs y5 y6)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) y1 y2 y3 y4 y5 y6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x142f4) fc None mm (seg_rom rsegs)).
  Proof.
    intros mm bs y1 y2 y3 y4 y5 y6 Hl HB HW.
    step. step. step.
    pose proof (blk_loop mm bs y5 y6 Hl HB HW 31 0 y4 eq_refl ltac:(lia)) as L.
    replace (p + 18 + Z.of_nat 0) with (p + 18) in L by lia. exact L.
  Qed.

  Lemma rec_loop : forall mm o n Bo (Q : machine_state -> Prop),
    0 <= o -> 2 <= n -> o + n <= 31 -> (Z.to_nat (n - 1) <= length Bo)%nat -> bytes_at rsegs mm (p + o + 18) Bo ->
    forall k i x6, (i + k = Z.to_nat (n - 1))%nat -> (0 < k)%nat ->
    (forall y5 y6, evt rsegs Q
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 n) (Z_to_bv 64 (p + o + 18))
                (Z_to_bv 64 (psum Bo (Z.to_nat (n - 1)))) (Z_to_bv 64 (n + o + p + 17)) y5 y6 a7
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x142e4) fc None mm (seg_rom rsegs))) ->
    evt rsegs Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 n) (Z_to_bv 64 (p + o + 18))
               (Z_to_bv 64 (psum Bo i)) (Z_to_bv 64 (n + o + p + 17)) (Z_to_bv 64 (p + o + 18 + Z.of_nat i)) x6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x142cc) fc None mm (seg_rom rsegs)).
  Proof.
    intros mm o n Bo Q Ho Hn Hon HL HB. induction k as [|k IH]; intros i x6 Hik Hk K; [lia|].
    pose proof (rd_byte rsegs mm (p + o + 18) Bo i HB ltac:(lia)) as RD.
    step. step. step. step.
    rewrite psum_S_zxb.
    rewrite (rcf_eqb (p + o + 18 + Z.of_nat i + 1) (n + o + p + 17)) by lia.
    destruct k as [|k].
    - replace (p + o + 18 + Z.of_nat i + 1 =? n + o + p + 17) with true by (symmetry; apply Z.eqb_eq; lia).
      cbn [negb]. cbv iota.
      step. replace (S i) with (Z.to_nat (n - 1)) by lia. apply K.
    - replace (p + o + 18 + Z.of_nat i + 1 =? n + o + p + 17) with false by (symmetry; apply Z.eqb_neq; lia).
      cbn [negb]. cbv iota.
      replace (p + o + 18 + Z.of_nat i + 1) with (p + o + 18 + Z.of_nat (S i)) by lia.
      apply (IH (S i)); [lia | lia | exact K].
  Qed.

  Lemma rec_loop0 : forall mm o n Bo (Q : machine_state -> Prop) x6,
    0 <= o -> 2 <= n -> o + n <= 31 -> (Z.to_nat (n - 1) <= length Bo)%nat -> bytes_at rsegs mm (p + o + 18) Bo ->
    (forall y5 y6, evt rsegs Q
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 n) (Z_to_bv 64 (p + o + 18))
                (Z_to_bv 64 (psum Bo (Z.to_nat (n - 1)))) (Z_to_bv 64 (n + o + p + 17)) y5 y6 a7
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x142e4) fc None mm (seg_rom rsegs))) ->
    evt rsegs Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 n) (Z_to_bv 64 (p + o + 18))
               (Z_to_bv 64 0) (Z_to_bv 64 (n + o + p + 17)) (Z_to_bv 64 (p + o + 18)) x6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x142cc) fc None mm (seg_rom rsegs)).
  Proof.
    intros mm o n Bo Q x6 Ho Hn Hon HL HB K.
    pose proof (rec_loop mm o n Bo Q Ho Hn Hon HL HB (Z.to_nat (n - 1)) 0 x6 ltac:(lia) ltac:(lia) K) as L.
    replace (p + o + 18 + Z.of_nat 0) with (p + o + 18) in L by lia. exact L.
  Qed.
End Fin.

Theorem ctrl_finish_holds : ctrl_finish_contract.
Proof.
  unfold ctrl_finish_contract, CTRL_FINISH.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    p f c o n row B -> -> Hf8 Hf24 Hrl HR Hc Ho Hn Hc2 Hrec Hp Hp50 HRW.
  pose proof (rd_byte rsegs m f row 20 HR ltac:(lia)) as RD20. change (Z.of_nat 20) with 20 in RD20.
  pose proof (rd_byte rsegs m f row 18 HR ltac:(lia)) as RD18. change (Z.of_nat 18) with 18 in RD18.
  pose proof (rd_byte rsegs m f row 19 HR ltac:(lia)) as RD19. change (Z.of_nat 19) with 19 in RD19.
  assert (Z20 : zxb (nth 20 row (Z_to_bv 8 0)) = Z_to_bv 64 c) by (unfold zxb; rewrite <- Hc; reflexivity).
  assert (Z18 : zxb (nth 18 row (Z_to_bv 8 0)) = Z_to_bv 64 o) by (unfold zxb; rewrite <- Ho; reflexivity).
  assert (Z19 : zxb (nth 19 row (Z_to_bv 8 0)) = Z_to_bv 64 n) by (unfold zxb; rewrite <- Hn; reflexivity).
  pose proof (byte_range (nth 20 row (Z_to_bv 8 0))) as BRc.
  pose proof (byte_range (nth 18 row (Z_to_bv 8 0))) as BRo.
  pose proof (byte_range (nth 19 row (Z_to_bv 8 0))) as BRn.
  unfold ubat in Hc, Ho, Hn.
  assert (Hcases : c = 0 \/ c = 1 \/ c = 2) by lia.
  step. rewrite Z20. step. step.
  rewrite (rcf_eqb c 1) by lia.
  destruct Hcases as [C | [C | C]].
  - replace (c =? 1) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
    step. step.
    rewrite (rcf_eqb c 2) by lia. replace (c =? 2) with false by (symmetry; apply Z.eqb_neq; lia).
    cbn [negb]. cbv iota.
    step.
    apply evt_done. cbv beta. do 8 eexists. split; [reflexivity|].
    rewrite C. change (fin_w 0 o n p) with (@nil (Z * Z)).
    split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact (fun H => H)|].
    intros [H | H]; discriminate H.
  - replace (c =? 1) with true by (symmetry; apply Z.eqb_eq; lia). cbv iota.
    destruct (rcf_rw32_inv rsegs m (p + 18) B (HRW ltac:(lia))) as (Hl & HB & HW).
    eapply evt_mono; [apply (blk ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc p
                               Hp Hp50 m B _ _ _ _ a5 a6 Hl HB HW)|].
    intros ms' (a1' & a2' & a3' & a4' & ->). cbv beta.
    assert (HW2 : wr_at rsegs m (p + 18) (Z.of_nat (length B))) by (rewrite Hl; exact HW).
    rewrite C. change (fin_w 1 o n p) with [(p + 49, p + 50)].
    destruct (rcf_store1 rsegs [(p + 49, p + 50)] m m (p + 18) B 31 (Z_to_bv 8 ((- psum B 31) mod 256))
                (munch_refl _ _) (wmono_refl _ _) (fun H => H) HB HW2 ltac:(lia) ltac:(cbn [inside]; left; lia))
      as (MU & WM & MI & HB' & HW').
    rewrite Hl in HW'.
    do 8 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    intros _.
    split; [rewrite rcf_fin1; apply rcf_rw32; [apply rcf_stamp32_len; exact Hl | exact HB' | exact HW']|].
    split; [apply rcf_closes_fin; [exact Hl | left; reflexivity | intros H; discriminate H]|].
    intros HC. apply rcf_fin_same; [exact Hl | left; reflexivity | intros H; discriminate H | exact HC].
  - replace (c =? 1) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
    step. step.
    rewrite (rcf_eqb c 2) by lia. replace (c =? 2) with true by (symmetry; apply Z.eqb_eq; lia).
    cbn [negb]. cbv iota.
    destruct (Hrec C) as [Hn2 Hon].
    destruct (rcf_rw32_inv rsegs m (p + 18) B (HRW ltac:(lia))) as (Hl & HB & HW).
    step. rewrite Z18. step. rewrite Z19. step. step. step.
    rewrite (rcf_ltu n 2) by lia. replace (n <? 2) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
    step. step. step. step. step.
    rewrite C. change (fin_w 2 o n p) with [(p + 18 + o + n - 1, p + 18 + o + n); (p + 49, p + 50)].
    assert (Hlo : (Z.to_nat (n - 1) <= length (skipn (Z.to_nat o) B))%nat) by (rewrite length_skipn; lia).
    pose proof (rcf_bytes_skipn rsegs m (p + 18) B (Z.to_nat o) ltac:(lia) HB) as HBo.
    replace (p + 18 + Z.of_nat (Z.to_nat o)) with (p + o + 18) in HBo by lia.
    apply (rec_loop0 ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc p Hp Hp50
             m o n (skipn (Z.to_nat o) B) _ a6 ltac:(lia) Hn2 Hon Hlo HBo).
    intros y5 y6.
    pose proof (psum_range (skipn (Z.to_nat o) B) (Z.to_nat (n - 1))) as PRo.
    assert (HS : store_ok rsegs m (wa (p + o + 18 + n + -1)) 1 = true).
    { replace (p + o + 18 + n + -1) with (p + 18 + (o + n - 1)) by lia.
      apply (wr_at_store_ok rsegs m (p + 18) 32 (o + n - 1) 1 HW); lia. }
    step. step. step. step.
    rewrite (rcf_rec_byte (psum (skipn (Z.to_nat o) B) (Z.to_nat (n - 1)))) by lia.
    replace (Z_to_bv 64 (p + o + 18 + n + -1)) with (wa (p + 18 + Z.of_nat (Z.to_nat (o + n - 1))))
      by (unfold wa; f_equal; lia).
    assert (HW2 : wr_at rsegs m (p + 18) (Z.of_nat (length B))) by (rewrite Hl; exact HW).
    destruct (rcf_store1 rsegs [(p + 18 + o + n - 1, p + 18 + o + n); (p + 49, p + 50)] m m (p + 18) B
                (Z.to_nat (o + n - 1)) (Z_to_bv 8 ((- psum (skipn (Z.to_nat o) B) (Z.to_nat (n - 1))) mod 128))
                (munch_refl _ _) (wmono_refl _ _) (fun H => H) HB HW2 ltac:(lia) ltac:(cbn [inside]; left; lia))
      as (MU1 & WM1 & MI1 & HB1 & HW1).
    assert (HlR : length (rstamp B o n) = 32%nat) by (apply rcf_rstamp_len; lia).
    rewrite Hl in HW1.
    eapply evt_mono; [apply (blk ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc p
                               Hp Hp50 _ (rstamp B o n) _ _ _ _ y5 y6 HlR HB1 HW1)|].
    intros ms' (a1' & a2' & a3' & a4' & ->). cbv beta.
    assert (HW1' : wr_at rsegs (write_to_mem m (wa (p + 18 + Z.of_nat (Z.to_nat (o + n - 1))))
                     [Z_to_bv 8 ((- psum (skipn (Z.to_nat o) B) (Z.to_nat (n - 1))) mod 128)])
                     (p + 18) (Z.of_nat (length (rstamp B o n)))) by (rewrite HlR; exact HW1).
    destruct (rcf_store1 rsegs [(p + 18 + o + n - 1, p + 18 + o + n); (p + 49, p + 50)] m _ (p + 18)
                (rstamp B o n) 31 (Z_to_bv 8 ((- psum (rstamp B o n) 31) mod 256))
                MU1 WM1 MI1 HB1 HW1' ltac:(lia) ltac:(cbn [inside]; right; left; lia))
      as (MU & WM & MI & HB2 & HW2').
    rewrite HlR in HW2'.
    do 8 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    intros _.
    split; [rewrite rcf_fin2; apply rcf_rw32; [apply rcf_stamp32_len; exact HlR | exact HB2 | exact HW2']|].
    split; [apply rcf_closes_fin; [exact Hl | right; reflexivity | intros _; split; [lia | split; lia]]|].
    intros HC. apply rcf_fin_same; [exact Hl | right; reflexivity | intros _; split; [lia | split; lia] | exact HC].
Qed.