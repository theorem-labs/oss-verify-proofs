From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcFin RcFinLib RcRec RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import
  RcAsanRT reac_ctrl_record_cksum_stamp_c reac_ctrl_block_cksum_stamp_c ctrl_finish_c.
Import ListNotations.
Open Scope Z_scope.

Lemma cfb_stampck : forall B o n, 0 <= o -> 1 <= n -> o + n <= 32 -> length B = 32%nat ->
  stampck (firstn (Z.to_nat (n - 1)) (skipn (Z.to_nat o) B)) = (- rsum B o (n - 1)) mod 128.
Proof.
  intros B o n Ho Hn Hon Hl. unfold stampck, rsum.
  rewrite length_firstn, length_skipn.
  replace (Nat.min (Z.to_nat (n - 1)) (length B - Z.to_nat o)) with (Z.to_nat (n - 1)) by lia.
  rewrite rcf_psum_firstn by lia. reflexivity.
Qed.

(* The bytes at A after a run that changes, of them, only the byte A + k. *)
Lemma cfb_bytes_munch1 : forall segs W m m1 A bs (k : nat) b,
  bytes_at segs m A bs -> (k < length bs)%nat -> munch W m m1 ->
  (forall x, A <= x < A + Z.of_nat (length bs) -> x <> A + Z.of_nat k -> outside W x) ->
  bytes_at segs m1 (A + Z.of_nat k) [b] -> bytes_at segs m1 A (upd_bytes bs k [b]).
Proof.
  intros segs W m m1 A bs k b HB Hk MU HO H1.
  pose proof HB as (HA & HL & HR). pose proof H1 as (_ & _ & HR1).
  split; [lia|]. split; [rewrite rcf_upd_len by lia; lia|].
  intros i Hi. rewrite rcf_upd_len in Hi by lia.
  rewrite upd_bytes_nth by (cbn [length]; lia). cbn [length].
  destruct (Nat.eq_dec i k) as [->|Hne].
  - rewrite Nat.leb_refl. replace (Nat.ltb k (k + 1)) with true by (symmetry; apply Nat.ltb_lt; lia).
    cbn [andb]. rewrite Nat.sub_diag. specialize (HR1 0%nat ltac:(cbn; lia)).
    change (Z.of_nat 0) with 0 in HR1. rewrite Z.add_0_r in HR1. exact HR1.
  - replace (Nat.leb k i && Nat.ltb i (k + 1))%bool with false
      by (destruct (Nat.leb_spec k i); destruct (Nat.ltb_spec i (k + 1)); cbn; first [reflexivity | lia]).
    rewrite <- (HR i Hi). unfold mrd. rewrite (MU (wa (A + Z.of_nat i))); [reflexivity|].
    rewrite wa_unsigned by lia. apply HO; lia.
Qed.

(* The runtime cells, the shadow and the addressability of a range stay as they are across a run whose writes
   miss them. *)
Lemma cfb_cells : forall W m m', asan_cells m -> munch W m m' ->
  (forall x, RT_LO <= x < RT_HI -> outside W x) -> asan_cells m'.
Proof.
  intros W m m' AC MU HO. unfold asan_cells in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat match goal with |- _ /\ _ => split end;
    (eapply rc_bytes_at_munch; [eassumption | exact MU | ]);
    intros x Hx; apply HO; rewrite ?length_le8, ?length_le4 in Hx; cbn [length] in Hx;
    unfold RT_LO, RT_HI, CELL_K, GOT_CELL_K, INITED, REPLACE, GOT_REPLACE, UAR, GOT_UAR, CANPOISON, HIEND,
      GOT_HIEND, MIDBEG, GOT_MIDBEG, MIDEND, GOT_MIDEND, REAL_MEMCPY, REAL_MEMSET, GOT_REAL_MEMSET in *; lia.
Qed.

Lemma cfb_shadow_rw : forall W m m', shadow_rw m -> munch W m m' -> wmono rsegs m m' ->
  (forall x, in_shadow x -> outside W x) -> shadow_rw m'.
Proof.
  intros W m m' HS MU WM HO a Ha. destruct (HS a Ha) as [Hw (b & Hb)]. split; [apply WM, Hw|].
  exists b. unfold mrd in *. rewrite MU; [exact Hb|].
  pose proof (rt_shadow_bound a Ha) as R. rewrite wa_unsigned by lia. apply HO, Ha.
Qed.

Lemma cfb_addressable : forall W m m' p n, addressable m p n -> munch W m m' ->
  (forall x, in_shadow x -> outside W x) -> addressable m' p n.
Proof.
  intros W m m' p n (H1 & H2 & H3 & H) MU HO. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hk). split; [exact Ha|]. exists b. split; [|exact Hk].
  unfold mrd in *. rewrite MU; [exact Hb|].
  pose proof (rt_app_shadow (p + i) Ha) as HSh. pose proof (rt_shadow_bound _ HSh) as R.
  rewrite wa_unsigned by lia. apply HO, HSh.
Qed.

Lemma cfb_addr_sub : forall m p n k n', addressable m p n -> 0 <= k -> 0 <= n' -> k + n' <= n ->
  addressable m (p + k) n'.
Proof.
  intros m p n k n' (H1 & H2 & H3 & H) Hk Hn' Hkn. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. replace (p + k + i) with (p + (k + i)) by lia. apply H. lia.
Qed.

(* sub_fp of two lists of intervals given as literals. *)
Ltac cfb_sub :=
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; cbn [outside] in Hx |- *;
  repeat match type of Hx with _ /\ _ => let H := fresh "Ho" in destruct Hx as [H Hx] end;
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia].

(* The goal [outside W x] from a hypothesis [outside W' x] whose intervals cover those of W. *)
Ltac cfb_out H :=
  repeat match type of H with _ /\ _ => let Ho := fresh "Ho" in destruct H as [Ho H] end;
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia].

(* +0x9c .. +0xb8: the checks before the tail jump, the epilogue and the block stamp. *)
Section T.
  Variables (ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (p lo : Z).
  Hypothesis HBS : reac_ctrl_block_cksum_stamp_contract.
  Hypothesis Hp : 0 < p.
  Hypothesis Hp50 : p + 50 <= 2^64.

  Definition Qt (mm : word -> option byte) (bs : list byte) : machine_state -> Prop :=
    fun ms' => exists (t0' t1' a0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0' t1' t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (p + 18 + 31, p + 18 + 32)] mm m'
      /\ wmono rsegs mm m' /\ (mem_inv rsegs mm -> mem_inv rsegs m')
      /\ rw_cells rsegs m' (p + 18) [CB 32 (stamp32 bs)] /\ stk rsegs m' lo (bv_unsigned sp).

  Lemma tail : forall mm bs yra yt0 yt1 y0 y1 y2 y3 y4 y5 y6 y7,
    length bs = 32%nat -> bytes_at rsegs mm (p + 18) bs -> wr_at rsegs mm (p + 18) 32 ->
    bytes_at rsegs mm (bv_unsigned sp + -8) (le8 ra) -> bytes_at rsegs mm (bv_unsigned sp + -16) (le8 s0) ->
    stk rsegs mm lo (bv_unsigned sp) -> lo + 16 <= bv_unsigned sp ->
    (p + 18 + 32 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= p + 18) ->
    asan_cells mm -> shadow_rw mm -> addressable mm (p + 18) 32 ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(bv_unsigned sp - 16, bv_unsigned sp); (p + 18 + 31, p + 18 + 32)] x) ->
    evt rsegs (Qt mm bs)
      (MS (mkR yra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp yt0 yt1 t2 (Z_to_bv 64 p) s1 y0 y1 y2 y3 y4 y5 y6 y7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x86580) fc None mm (seg_rom rsegs)).
  Proof.
    intros mm bs yra yt0 yt1 y0 y1 y2 y3 y4 y5 y6 y7 Hl HB HW Ha Hs STm HLO HD HC HSW HAD HO.
    assert (RDa : ov_read_bytes rsegs mm (wa (bv_unsigned sp + -8)) 8 = Some (le8 ra)).
    { replace (bv_unsigned sp + -8) with (bv_unsigned sp + -8 + 0) by lia.
      rewrite (bytes_at_read rsegs mm _ (le8 ra) 0 8 Ha) by (try rewrite length_le8; lia). reflexivity. }
    assert (RDs : ov_read_bytes rsegs mm (wa (bv_unsigned sp + -16)) 8 = Some (le8 s0)).
    { replace (bv_unsigned sp + -16) with (bv_unsigned sp + -16 + 0) by lia.
      rewrite (bytes_at_read rsegs mm _ (le8 s0) 0 8 Hs) by (try rewrite length_le8; lia). reflexivity. }
    step.
    rewrite (rcf_eqb p 0) by lia. replace (p =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
    step. step.
    rewrite (rcf_ltu_neg_l p (-19)) by lia.
    replace (2^64 + -19 <? p) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
    step. step. step. step.
    step.
    eapply evt_mono; [eapply HBS with (q := p + 18) (B := bs) (lo := lo);
                      try unfold REAC_CTRL_BLOCK_CKSUM_STAMP_FRAME;
                      [lia | lia | reflexivity | apply rcf_rw32; assumption | lia | exact STm | lia
                      | exact HC | exact HSW | exact HAD | exact HO] |].
    intros ms' (t0' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m' & -> & MU & WM & MI & RW & _ & STf).
    unfold Qt. do 11 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact RW | exact STf].
  Qed.
End T.

Theorem ctrl_finish_holds : reac_ctrl_record_cksum_stamp_contract -> reac_ctrl_block_cksum_stamp_contract ->
  ctrl_finish_contract.
Proof.
  intros HRS HBS. unfold ctrl_finish_contract, CTRL_FINISH, CTRL_FINISH_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    p f c o n lo row B -> -> Hf8 Hf24 Hrl HR Hc Ho Hn Hc2 Hrec Hp Hp50 HRW ST HLO HDf HDp HCE HSW HADf HADp HWO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
  pose proof ST as (ST0 & _ & _).
  destruct (stk_split rsegs m lo (bv_unsigned sp - 16) (bv_unsigned sp) ST ltac:(lia)) as [STlo STtop].
  (* +0x0 .. +0x8: the frame [S - 16, S) with ra and s0 *)
  assert (HS1 : store_ok rsegs m (wa (bv_unsigned sp + -8)) 8 = true)
    by (apply (rcf_stk_store_ok rsegs m (bv_unsigned sp - 16) (bv_unsigned sp)); [exact STtop | lia | cbn; lia]).
  pose proof (stk_write rsegs m (bv_unsigned sp - 16) (bv_unsigned sp) (bv_unsigned sp + -8) (le8 ra) STtop
                ltac:(lia) ltac:(rewrite length_le8; lia)) as ST'.
  assert (HS2 : store_ok rsegs (write_to_mem m (Z_to_bv 64 (bv_unsigned sp + -8)) (le8 ra))
                  (wa (bv_unsigned sp + -16)) 8 = true)
    by (apply (rcf_stk_store_ok rsegs _ (bv_unsigned sp - 16) (bv_unsigned sp)); [exact ST' | lia | cbn; lia]).
  step. step. step. clear HS1 HS2 ST'.
  destruct (rcf_frame16 rsegs m (bv_unsigned sp) [] ra s0 STtop)
    as (MU1 & WM1 & MI1 & STm1 & FRa & FRs & TB1 & TW1).
  pose proof (TB1 f row HR ltac:(rewrite Hrl; lia)) as HR1.
  pose proof (stk_transport_disjoint rsegs _ m _ lo (bv_unsigned sp - 16) STlo MU1 WM1
                ltac:(cbn [disjoint_from]; split; [lia | exact I])) as STlo1.
  remember (write_to_mem (write_to_mem m (Z_to_bv 64 (bv_unsigned sp + -8)) (le8 ra))
              (Z_to_bv 64 (bv_unsigned sp + -16)) (le8 s0)) as m1 eqn:Em1.
  pose proof (bytes_at_bound rsegs m f row HR) as HRB.
  pose proof (rd_byte rsegs m1 f row 20 HR1 ltac:(lia)) as RD20. change (Z.of_nat 20) with 20 in RD20.
  pose proof (rd_byte rsegs m1 f row 18 HR1 ltac:(lia)) as RD18. change (Z.of_nat 18) with 18 in RD18.
  pose proof (rd_byte rsegs m1 f row 19 HR1 ltac:(lia)) as RD19. change (Z.of_nat 19) with 19 in RD19.
  assert (Z20 : zxb (nth 20 row (Z_to_bv 8 0)) = Z_to_bv 64 c) by (unfold zxb; rewrite <- Hc; reflexivity).
  assert (Z18 : zxb (nth 18 row (Z_to_bv 8 0)) = Z_to_bv 64 o) by (unfold zxb; rewrite <- Ho; reflexivity).
  assert (Z19 : zxb (nth 19 row (Z_to_bv 8 0)) = Z_to_bv 64 n) by (unfold zxb; rewrite <- Hn; reflexivity).
  pose proof (byte_range (nth 20 row (Z_to_bv 8 0))) as BRc.
  pose proof (byte_range (nth 18 row (Z_to_bv 8 0))) as BRo.
  pose proof (byte_range (nth 19 row (Z_to_bv 8 0))) as BRn.
  unfold ubat in Hc, Ho, Hn.
  assert (Hcases : c = 0 \/ c = 1 \/ c = 2) by lia.
  assert (L7 : Z.land f 7 = 0) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; exact Hf8).
  (* the runtime after the frame stores *)
  assert (HOf : forall x, RT_LO <= x < RT_HI \/ in_shadow x -> outside [(bv_unsigned sp - 16, bv_unsigned sp)] x).
  { intros x Hx. pose proof (HWO x Hx) as H. cbn [outside] in H |- *. destruct H as [H _]. split; [lia | exact I]. }
  pose proof (cfb_cells _ m m1 HCE MU1 (fun x Hx => HOf x (or_introl Hx))) as AC1.
  pose proof (cfb_shadow_rw _ m m1 HSW MU1 WM1 (fun x Hx => HOf x (or_intror Hx))) as SW1.
  pose proof (cfb_addressable _ m m1 _ _ HADf MU1 (fun x Hx => HOf x (or_intror Hx))) as HADf1.
  pose proof (rt_asan_rt m1 [] AC1 (fun _ _ => I)) as HRT1.
  pose proof (rt_shadow_rd m1 (f + 18) 3 [] HADf1 (fun _ _ => I)) as HSRf1.
  pose proof (rt_addressable m1 (f + 18) 3 HADf1) as HAf1.
  set (off := ASAN_K) in HRT1, HSRf1, HAf1. clearbody off.
  pose proof (asan_rt_got_read rsegs m1 _ _ off _ HRT1) as RG.
  pose proof (asan_rt_cell_read rsegs m1 _ _ off _ HRT1) as RC.
  unfold GOT_CELL_K, CELL_K in RG, RC.
  match goal with |- evt _ ?Q _ => set (QQ := Q) end.
  (* +0xc .. +0x10: the alignment check of f *)
  step. step.
  rewrite (unsigned_lit f) by lia. rewrite L7. rewrite bv_eqb_refl. cbn [negb]. cbv iota.
  step. step. step. step.
  clear RG RC.
  step.
  (* +0x28 .. +0x34: the shadow check of f + 20 *)
  destruct (asan_shadow_read_at rsegs m1 off (f + 18) 3 _ 2 ((f + 20) / 8 + off) HSRf1 ltac:(lia)
              ltac:(unfold asan_shadow; replace (f + 18 + 2) with (f + 20) by lia; reflexivity)) as (k20 & RK & BK).
  pose proof (HAf1 2 k20 ltac:(lia) BK) as OK. unfold asan_ok in OK. replace (f + 18 + 2) with (f + 20) in OK by lia.
  pose proof (rc_byte_signed k20) as KR. clear BK.
  assert (PRO : forall y13 y14,
    evt rsegs QQ
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 (Z_to_bv 64 p) s1 (Z_to_bv 64 (f + 20))
               (Z_to_bv 64 f) (Z_to_bv 64 off) y13 y14 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8651c) fc None m1 (seg_rom rsegs))).
  { intros y13 y14. clear RK.
    step. rewrite Z20. step. step.
    rewrite (rcf_eqb c 1) by lia.
    destruct Hcases as [C | [C | C]].
    - (* c = 0: return *)
      replace (c =? 1) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
      step. step.
      rewrite (rcf_eqb c 2) by lia. replace (c =? 2) with false by (symmetry; apply Z.eqb_neq; lia).
      cbn [negb]. cbv iota.
      assert (RDa : ov_read_bytes rsegs m1 (wa (bv_unsigned sp + -8)) 8 = Some (le8 ra)).
      { replace (bv_unsigned sp + -8) with (bv_unsigned sp + -8 + 0) by lia.
        rewrite (bytes_at_read rsegs m1 _ (le8 ra) 0 8 FRa) by (try rewrite length_le8; lia). reflexivity. }
      assert (RDs : ov_read_bytes rsegs m1 (wa (bv_unsigned sp + -16)) 8 = Some (le8 s0)).
      { replace (bv_unsigned sp + -16) with (bv_unsigned sp + -16 + 0) by lia.
        rewrite (bytes_at_read rsegs m1 _ (le8 s0) 0 8 FRs) by (try rewrite length_le8; lia). reflexivity. }
      step. step. step. step.
      apply evt_done. unfold QQ. cbv beta. rewrite C in Hc. subst c.
      do 11 eexists. split; [reflexivity|].
      split; [eapply munch_weaken; [| exact MU1]; cfb_sub|].
      split; [exact WM1|]. split; [exact MI1|].
      split; [exact (stk_merge rsegs m1 lo (bv_unsigned sp - 16) (bv_unsigned sp) STlo1 STm1 ltac:(lia))|].
      intros [H | H]; discriminate H.
    - (* c = 1: the block stamp *)
      replace (c =? 1) with true by (symmetry; apply Z.eqb_eq; lia). cbv iota.
      assert (CC : c = 1 \/ c = 2) by lia.
      destruct (rcf_rw32_inv rsegs m (p + 18) B (HRW CC)) as (Hl & HB & HW).
      pose proof (HDp CC) as HDp'.
      pose proof (TB1 (p + 18) B HB ltac:(rewrite Hl; lia)) as HB1.
      pose proof (TW1 (p + 18) 32 HW) as HW1.
      pose proof (cfb_addressable _ m m1 _ _ (HADp CC) MU1 (fun x Hx => HOf x (or_intror Hx))) as HADp1.
      rewrite C in Hc. subst c.
      change (fin_w 1 o n p) with [(p + 49, p + 50)] in HWO.
      assert (HOb : forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
                outside [(bv_unsigned sp - 16, bv_unsigned sp); (p + 18 + 31, p + 18 + 32)] x).
      { intros x Hx.
        assert (Hx' : RT_LO <= x < RT_HI \/ in_shadow x)
          by (unfold GOT_CELL_K, CELL_K, RT_LO, RT_HI in *;
              destruct Hx as [Hx | [Hx | Hx]]; [left; lia | left; lia | right; exact Hx]).
        pose proof (HWO x Hx') as H. cbn [outside] in H |- *. cfb_out H. }
      eapply evt_mono; [apply (tail ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc p lo HBS Hp Hp50
                                 m1 B _ _ _ _ _ _ _ _ _ _ _ Hl HB1 HW1 FRa FRs
                                 (stk_merge rsegs m1 lo (bv_unsigned sp - 16) (bv_unsigned sp) STlo1 STm1 ltac:(lia))
                                 ltac:(lia) ltac:(lia) AC1 SW1 HADp1 HOb)|].
      intros ms' (x0 & x1 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & m' & -> & MU & WM & MI & RW & STf).
      unfold QQ. cbv beta.
      change (fin_w 1 o n p) with [(p + 49, p + 50)].
      do 11 eexists. split; [reflexivity|].
      split.
      { apply (munch_trans _ m m1 m').
        - eapply munch_weaken; [| exact MU1]; cfb_sub.
        - eapply munch_weaken; [| exact MU]; cfb_sub. }
      split; [exact (wmono_trans rsegs m m1 m' WM1 WM)|].
      split; [intros HI; exact (MI (MI1 HI))|].
      split; [exact STf|].
      intros _.
      split; [rewrite rcf_fin1; exact RW|].
      split; [apply rcf_closes_fin; [exact Hl | left; reflexivity | intros H; discriminate H]|].
      intros HC. apply rcf_fin_same; [exact Hl | left; reflexivity | intros H; discriminate H | exact HC].
    - (* c = 2: the record stamp, then the block stamp *)
      replace (c =? 1) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
      step. step.
      rewrite (rcf_eqb c 2) by lia. replace (c =? 2) with true by (symmetry; apply Z.eqb_eq; lia).
      cbn [negb]. cbv iota.
      assert (CC : c = 1 \/ c = 2) by lia.
      destruct (Hrec C) as [Hn2 Hon].
      destruct (rcf_rw32_inv rsegs m (p + 18) B (HRW CC)) as (Hl & HB & HW).
      pose proof (HDp CC) as HDp'.
      pose proof (TB1 (p + 18) B HB ltac:(rewrite Hl; lia)) as HB1.
      pose proof (TW1 (p + 18) 32 HW) as HW1.
      pose proof (cfb_addressable _ m m1 _ _ (HADp CC) MU1 (fun x Hx => HOf x (or_intror Hx))) as HADp1.
      rewrite C in Hc. subst c.
      change (fin_w 2 o n p) with [(p + 18 + o + n - 1, p + 18 + o + n); (p + 49, p + 50)] in HWO.
      assert (Ho0 : 0 <= o) by lia.
      assert (HOb : forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
                outside [(bv_unsigned sp - 16, bv_unsigned sp); (p + 18 + 31, p + 18 + 32)] x).
      { intros x Hx.
        assert (Hx' : RT_LO <= x < RT_HI \/ in_shadow x)
          by (unfold GOT_CELL_K, CELL_K, RT_LO, RT_HI in *;
              destruct Hx as [Hx | [Hx | Hx]]; [left; lia | left; lia | right; exact Hx]).
        pose proof (HWO x Hx') as H. cbn [outside] in H |- *. cfb_out H. }
      (* +0x4c .. +0x54: the pointer checks of p *)
      step.
      rewrite (rcf_eqb p 0) by lia. replace (p =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
      step. step.
      rewrite (rcf_ltu_neg p (-18)) by lia.
      replace (p <? 2^64 + -18) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb]. cbv iota.
      step.
      (* +0x5c .. +0x68: the shadow check of f + 18 *)
      destruct (asan_shadow_read_at rsegs m1 off (f + 18) 3 _ 0 ((f + 18) / 8 + off) HSRf1 ltac:(lia)
                  ltac:(unfold asan_shadow; rewrite Z.add_0_r; reflexivity)) as (k18 & RK18 & BK18).
      pose proof (HAf1 0 k18 ltac:(lia) BK18) as OK18. unfold asan_ok in OK18. rewrite Z.add_0_r in OK18.
      pose proof (rc_byte_signed k18) as KR18. clear BK18.
      assert (R1 : forall y13 y14,
        evt rsegs QQ
          (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 (Z_to_bv 64 p) s1 (Z_to_bv 64 (f + 18))
                   (Z_to_bv 64 f) (Z_to_bv 64 off) y13 y14 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x86550) fc None m1 (seg_rom rsegs))).
      { intros z13 z14. clear RK18.
        (* +0x6c .. +0x78: the load of o and the check p + 18 + o < 2^64 *)
        step. rewrite Z18.
        step. step. step.
        rewrite (unsigned_lit (p + 18)) by lia. rewrite (zb_lxor_ones (p + 18)) by lia.
        rewrite (rcf_ltu (18446744073709551615 - (p + 18)) o) by lia.
        replace (18446744073709551615 - (p + 18) <? o) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
        step.
        (* +0x80 .. +0x8c: the shadow check of f + 19 *)
        destruct (asan_shadow_read_at rsegs m1 off (f + 18) 3 _ 1 ((f + 19) / 8 + off) HSRf1 ltac:(lia)
                    ltac:(unfold asan_shadow; replace (f + 18 + 1) with (f + 19) by lia; reflexivity))
          as (k19 & RK19 & BK19).
        pose proof (HAf1 1 k19 ltac:(lia) BK19) as OK19. unfold asan_ok in OK19.
        replace (f + 18 + 1) with (f + 19) in OK19 by lia.
        pose proof (rc_byte_signed k19) as KR19. clear BK19.
        assert (R2 : forall y11 y12,
          evt rsegs QQ
            (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 (Z_to_bv 64 p) s1 (Z_to_bv 64 (f + 19))
                     y11 y12 (Z_to_bv 64 o) (Z_to_bv 64 (p + 18)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x86574) fc None m1 (seg_rom rsegs))).
        { intros w11 w12. clear RK19.
          (* +0x90 .. +0x98: the load of n and the call of the record stamp *)
          step. rewrite Z19. step. step.
          assert (Hbsr : bytes_at rsegs m1 (p + 18 + o) (firstn (Z.to_nat (n - 1)) (skipn (Z.to_nat o) B))).
          { pose proof (rcf_bytes_sub rsegs m1 (p + 18) B (Z.to_nat o) (Z.to_nat (n - 1)) ltac:(lia) HB1) as H.
            replace (p + 18 + Z.of_nat (Z.to_nat o)) with (p + 18 + o) in H by lia. exact H. }
          assert (Hwr : wr_at rsegs m1 (p + 18 + o + n - 1) 1).
          { replace (p + 18 + o + n - 1) with (p + 18 + (o + n - 1)) by lia.
            apply (rcf_wr_sub rsegs m1 (p + 18) 32 1 HW1); lia. }
          pose proof (cfb_addr_sub m1 (p + 18) 32 o n HADp1 ltac:(lia) ltac:(lia) ltac:(lia)) as HADr.
          assert (HOr : forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
                    outside [(bv_unsigned sp + -16 - 16, bv_unsigned sp + -16);
                             (p + 18 + o + n - 1, p + 18 + o + n)] x).
          { intros x Hx.
            assert (Hx' : RT_LO <= x < RT_HI \/ in_shadow x)
              by (unfold GOT_CELL_K, CELL_K, RT_LO, RT_HI in *;
                  destruct Hx as [Hx | [Hx | Hx]]; [left; lia | left; lia | right; exact Hx]).
            pose proof (HWO x Hx') as H. cbn [outside] in H |- *. cfb_out H. }
          eapply evt_cut;
            [eapply HRS with (bs := firstn (Z.to_nat (n - 1)) (skipn (Z.to_nat o) B)) (lo := lo);
             try unfold REAC_CTRL_RECORD_CKSUM_STAMP_FRAME;
             rewrite ?(unsigned_lit (p + 18 + o)) by lia; rewrite ?(unsigned_lit n) by lia;
             rewrite ?(unsigned_lit (bv_unsigned sp + -16)) by lia;
             [lia | lia | lia | rewrite length_firstn, length_skipn; lia | exact Hbsr | exact Hwr | lia
             | exact STlo1 | lia | exact AC1 | exact SW1 | exact HADr | exact HOr] |].
          intros ms' (x5 & x6 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & m2 & -> & HBr & _ & _ & MU2 & WM2 & MI2 & STlo2).
          unfold REAC_CTRL_RECORD_CKSUM_STAMP_FRAME in MU2.
          rewrite (unsigned_lit (p + 18 + o)), (unsigned_lit n) in HBr, MU2 by lia.
          rewrite (unsigned_lit (bv_unsigned sp + -16)) in MU2, STlo2 by lia.
          replace (ret_pc (Z_to_bv 64 0x86580)) with (Z_to_bv 64 0x86580)
            by (symmetry; apply ret_pc_even; [lia | reflexivity]).
          replace (p + 18 + o + n - 1) with (p + 18 + Z.of_nat (Z.to_nat (o + n - 1))) in HBr by lia.
          pose proof (cfb_bytes_munch1 rsegs _ m1 m2 (p + 18) B (Z.to_nat (o + n - 1)) _ HB1 ltac:(lia) MU2
                        ltac:(intros x Hx1 Hx2; cbn [outside]; split; [lia | split; [lia | exact I]]) HBr) as HB2.
          rewrite (cfb_stampck B o n) in HB2 by lia.
          assert (HlR : length (rstamp B o n) = 32%nat) by (apply rcf_rstamp_len; lia).
          pose proof (wr_at_transport rsegs m1 m2 (p + 18) 32 HW1 WM2) as HW2.
          pose proof (bytes_at_transport rsegs _ m1 m2 _ _ FRa MU2
                        ltac:(cbn [disjoint_from]; rewrite length_le8; split; [lia | split; [lia | exact I]])) as FRa2.
          pose proof (bytes_at_transport rsegs _ m1 m2 _ _ FRs MU2
                        ltac:(cbn [disjoint_from]; rewrite length_le8; split; [lia | split; [lia | exact I]])) as FRs2.
          pose proof (stk_transport_disjoint rsegs _ m1 m2 _ _ STm1 MU2 WM2
                        ltac:(cbn [disjoint_from]; split; [lia | split; [lia | exact I]])) as STm2.
          pose proof (stk_merge rsegs m2 lo (bv_unsigned sp - 16) (bv_unsigned sp) STlo2 STm2 ltac:(lia)) as STf2.
          assert (HO2 : forall x, RT_LO <= x < RT_HI \/ in_shadow x ->
                    outside [(bv_unsigned sp + -16 - 16, bv_unsigned sp + -16);
                             (p + 18 + o + n - 1, p + 18 + o + n)] x).
          { intros x Hx. pose proof (HWO x Hx) as H. cbn [outside] in H |- *. cfb_out H. }
          pose proof (cfb_cells _ m1 m2 AC1 MU2 (fun x Hx => HO2 x (or_introl Hx))) as AC2.
          pose proof (cfb_shadow_rw _ m1 m2 SW1 MU2 WM2 (fun x Hx => HO2 x (or_intror Hx))) as SW2.
          pose proof (cfb_addressable _ m1 m2 _ _ HADp1 MU2 (fun x Hx => HO2 x (or_intror Hx))) as HADp2.
          (* +0x9c .. +0xb8 *)
          eapply evt_mono; [apply (tail ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc p lo
                                     HBS Hp Hp50 m2 (rstamp B o n) _ _ _ _ _ _ _ _ _ _ _ HlR HB2 HW2 FRa2 FRs2 STf2
                                     ltac:(lia) ltac:(lia) AC2 SW2 HADp2 HOb)|].
          intros ms' (x0 & x1 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & m3 & -> & MU3 & WM3 & MI3 & RW3 & STf3).
          unfold QQ. cbv beta.
          change (fin_w 2 o n p) with [(p + 18 + o + n - 1, p + 18 + o + n); (p + 49, p + 50)].
          do 11 eexists. split; [reflexivity|].
          split.
          { apply (munch_trans _ m m2 m3); [apply (munch_trans _ m m1 m2)|].
            - eapply munch_weaken; [| exact MU1]; cfb_sub.
            - eapply munch_weaken; [| exact MU2]; cfb_sub.
            - eapply munch_weaken; [| exact MU3]; cfb_sub. }
          split; [exact (wmono_trans rsegs m m2 m3 (wmono_trans rsegs m m1 m2 WM1 WM2) WM3)|].
          split; [intros HI; exact (MI3 (MI2 (MI1 HI)))|].
          split; [exact STf3|].
          intros _.
          split; [rewrite rcf_fin2; exact RW3|].
          split; [apply rcf_closes_fin; [exact Hl | right; reflexivity | intros _; split; [lia | split; lia]]|].
          intros HC. apply rcf_fin_same; [exact Hl | right; reflexivity | intros _; split; [lia | split; lia]
                                         | exact HC]. }
        step.
        rewrite (unsigned_lit (f + 19)) by lia. rewrite rc_shr3.
        step. step. clear RK19.
        step.
        unfold sxb. rewrite (rc_eqb0_signed (bv_signed k19)) by lia.
        destruct (Z.eqb_spec (bv_signed k19) 0) as [K0|K0]; cbn [negb].
        - apply R2.
        - step.
          rewrite (unsigned_lit (f + 19)) by lia. rewrite rc_land7.
          step.
          rewrite (rc_lts_signed ((f + 19) mod 8) (bv_signed k19))
            by (pose proof (Z.mod_pos_bound (f + 19) 8 ltac:(lia)); lia).
          replace ((f + 19) mod 8 <? bv_signed k19) with true by (symmetry; apply Z.ltb_lt; destruct OK19; lia).
          apply R2. }
      step.
      rewrite (unsigned_lit (f + 18)) by lia. rewrite rc_shr3.
      step. step. clear RK18.
      step.
      unfold sxb. rewrite (rc_eqb0_signed (bv_signed k18)) by lia.
      destruct (Z.eqb_spec (bv_signed k18) 0) as [K0|K0]; cbn [negb].
      + apply R1.
      + step.
        rewrite (unsigned_lit (f + 18)) by lia. rewrite rc_land7.
        step.
        rewrite (rc_lts_signed ((f + 18) mod 8) (bv_signed k18))
          by (pose proof (Z.mod_pos_bound (f + 18) 8 ltac:(lia)); lia).
        replace ((f + 18) mod 8 <? bv_signed k18) with true by (symmetry; apply Z.ltb_lt; destruct OK18; lia).
        apply R1. }
  step.
  rewrite (unsigned_lit (f + 20)) by lia. rewrite rc_shr3.
  step. step. clear RK.
  step.
  unfold sxb. rewrite (rc_eqb0_signed (bv_signed k20)) by lia.
  destruct (Z.eqb_spec (bv_signed k20) 0) as [K0|K0]; cbn [negb].
  - apply PRO.
  - step.
    rewrite (unsigned_lit (f + 20)) by lia. rewrite rc_land7.
    step.
    rewrite (rc_lts_signed ((f + 20) mod 8) (bv_signed k20))
      by (pose proof (Z.mod_pos_bound (f + 20) 8 ltac:(lia)); lia).
    replace ((f + 20) mod 8 <? bv_signed k20) with true by (symmetry; apply Z.ltb_lt; destruct OK; lia).
    apply PRO.
Qed.
