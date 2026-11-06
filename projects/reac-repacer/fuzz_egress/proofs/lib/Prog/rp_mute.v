From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Prog Require Import memset_c rp_mute_c.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib Require Import EgressFrame.
Import ListNotations.
Open Scope Z_scope.

Lemma firstn1_skipn : forall (bs : list byte) k d, (k < length bs)%nat -> firstn 1 (skipn k bs) = [nth k bs d].
Proof. induction bs as [|b bs IH]; intros [|k] d H; cbn in *; try lia; auto. apply IH; lia. Qed.

Lemma zxb_unsigned : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b.
Proof.
  intros b. unfold zxb. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R.
  apply unsigned_lit. cbn in R |- *. lia.
Qed.

Ltac fold_zxb H :=
  repeat match type of H with
  | context [Z_to_bv 64 (bv_unsigned ?b)] =>
      lazymatch type of b with bv 8 => change (Z_to_bv 64 (bv_unsigned b)) with (zxb b) in H end
  end;
  rewrite ?zxb_unsigned in H.

Lemma wr_at_skip : forall segs m a n k, wr_at segs m a n -> 0 <= k <= n -> wr_at segs m (a + k) (n - k).
Proof.
  intros segs m a n k (H0 & H1 & H) Hk. split; [lia|]. split; [lia|].
  intros i Hi. replace (a + k + i) with (a + (k + i)) by lia. apply H. lia.
Qed.

Section Mute.
Variable MS_OK : memset_contract.

Lemma rp_mute_ret : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m bs (a0v a1v : word),
  mem_inv rsegs m -> rp_mute_mutes (bv_unsigned a1v) bs = false -> bytes_at rsegs m (bv_unsigned a0v) bs ->
  exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
       F (ret_pc ra) fc None m (seg_rom rsegs) =
    MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
       F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned a0v + 18, bv_unsigned a0v + bv_unsigned a1v)] m m' /\
    wmono rsegs m m' /\ mem_inv rsegs m' /\ bytes_at rsegs m' (bv_unsigned a0v) (rp_mute_bytes (bv_unsigned a1v) bs).
Proof.
  intros. do 16 eexists. split; [reflexivity|].
  split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [assumption|].
  unfold rp_mute_bytes. rewrite H0. assumption.
Qed.

Theorem rp_mute_holds : rp_mute_contract.
Proof.
  unfold rp_mute_contract, RP_MUTE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs
    Ha0 HB HL HW HI.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0. change (bv_modulus 64) with (2^64) in Ra0.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1. change (bv_modulus 64) with (2^64) in Ra1.
  pose proof (bytes_at_bound rsegs m _ _ HB) as HBb. rewrite HL in HBb. rewrite Z2Nat.id in HBb by lia.
  step. step.
  if_cases HC; zify_cond HC.
  - (* n < 19: return at once *)
    step. apply evt_done. eapply (rp_mute_ret) with (bs := bs) (a0v := a0) (a1v := a1); [exact HI | |];
      [| exact HB]. unfold rp_mute_mutes. rewrite (proj2 (Z.ltb_ge 18 (bv_unsigned a1))) by lia. reflexivity.
  - set (b16 := nth 16 bs (Z_to_bv 8 1)). set (b17 := nth 17 bs (Z_to_bv 8 1)).
    assert (RB16 : ov_read_bytes rsegs m (wa (bv_unsigned a0 + 16)) 1 = Some [b16]).
    { rewrite (bytes_at_read rsegs m _ bs 16 1 HB) by lia. f_equal. apply firstn1_skipn. lia. }
    assert (RB17 : ov_read_bytes rsegs m (wa (bv_unsigned a0 + 17)) 1 = Some [b17]).
    { rewrite (bytes_at_read rsegs m _ bs 17 1 HB) by lia. f_equal. apply firstn1_skipn. lia. }
    step. step.
    if_cases H16; zify_cond H16; fold_zxb H16.
    + (* f[16] != 0 *)
      step. apply evt_done. eapply (rp_mute_ret) with (bs := bs) (a0v := a0) (a1v := a1); [exact HI | |];
        [| exact HB]. unfold rp_mute_mutes, frame_is_audio. fold b16.
      rewrite (proj2 (Z.eqb_neq (bv_unsigned b16) 0)) by lia. rewrite andb_false_r. reflexivity.
    + step. step.
      if_cases H17; zify_cond H17; fold_zxb H17.
      * (* audio: memset (f + 18, 0, n - 18) *)
        do 4 step.
        set (junk := skipn 18 bs).
        pose proof HB as HB'. rewrite <- (firstn_skipn 18 bs) in HB'. apply bytes_at_app in HB'.
        destruct HB' as [HB18 HBJ]. rewrite firstn_length_le in HBJ by lia. fold junk in HBJ.
        assert (HJ : rw_cells rsegs m (bv_unsigned a0 + 18) [CB (Z.to_nat (bv_unsigned a1 - 18)) junk]).
        { split; [split|].
          - cbn. split; [|exact I]. unfold junk. rewrite skipn_length. lia.
          - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HBJ.
          - cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. apply wr_at_skip; [exact HW | lia]. }
        eapply evt_cut; [eapply (MS_OK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ junk) |].
        { rewrite !unsigned_lit by lia. replace (bv_unsigned a1 + -18) with (bv_unsigned a1 - 18) by lia. exact HJ. }
        { exact HI. }
        intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1
          & -> & MU1 & WM1 & MI1 & HO1).
        apply evt_done. do 15 eexists. exists m1. split; [reflexivity|].
        rewrite !unsigned_lit in MU1, HO1 by lia.
        split; [replace (bv_unsigned a0 + bv_unsigned a1) with (bv_unsigned a0 + 18 + (bv_unsigned a1 + -18)) by lia;
                exact MU1|].
        split; [exact WM1|]. split; [exact MI1|].
        unfold rp_mute_bytes, rp_mute_mutes, frame_is_audio. fold b16 b17.
        rewrite (proj2 (Z.ltb_lt 18 (bv_unsigned a1))) by lia.
        rewrite (proj2 (Z.eqb_eq (bv_unsigned b16) 0)) by lia. rewrite (proj2 (Z.eqb_eq (bv_unsigned b17) 0)) by lia.
        cbn [andb]. apply bytes_at_app. rewrite firstn_length_le by lia. split.
        -- eapply bytes_at_transport; [exact HB18 | exact MU1 |]. cbn [disjoint_from].
           rewrite firstn_length_le by lia. split; [lia | exact I].
        -- destruct HO1 as [(_ & HB1) _]. cbn [cells_bytes cbytes] in HB1. rewrite app_nil_r in HB1.
           replace (Z.to_nat (bv_unsigned a1 - 18)) with (Z.to_nat (bv_unsigned a1 + -18)) by (f_equal; lia).
           exact HB1.
      * step. apply evt_done. eapply (rp_mute_ret) with (bs := bs) (a0v := a0) (a1v := a1); [exact HI | |];
          [| exact HB]. unfold rp_mute_mutes, frame_is_audio. fold b16 b17.
        rewrite (proj2 (Z.eqb_neq (bv_unsigned b17) 0)) by lia. rewrite !andb_false_r. reflexivity.
Qed.

End Mute.
