(* proves check_announce_holds, the walk of check_announce in fuzz_frame.ubsan against U/Prog/check_announce_c.v, with the memset, diginet_announce_parse and bcmp UBSan contracts as hypotheses. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Lib Require ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Prog Require Import diginet_frame_parse_c check_parse_fields_c
  CheckStackU memset_c bcmp_c diginet_announce_parse_c check_announce_c.
Import ListNotations.
Open Scope Z_scope.

(** * Cells: split, join and slices *)

Lemma cau_split1 : forall m A B c rest, rw_cells rsegs m A (c :: rest) -> B = A + Z.of_nat (csize c) ->
  rw_cells rsegs m A [c] /\ rw_cells rsegs m B rest.
Proof.
  intros m A B c rest [[Hwf Hb] (W0 & W1 & W2)] ->.
  cbn [cells_wf] in Hwf. destruct Hwf as [Hc Hr].
  cbn [cells_bytes] in Hb. apply (proj1 (bytes_at_app rsegs _ _ _ _)) in Hb. destruct Hb as [B1 B2].
  rewrite cbytes_length in B2 by exact Hc.
  cbn [cells_size] in W1, W2.
  split.
  - split; [split; [cbn; tauto | cbn [cells_bytes]; rewrite app_nil_r; exact B1] |].
    cbn [cells_size]. split; [lia|]. split; [lia|]. intros i Hi. apply W2. lia.
  - split; [split; assumption|]. split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (csize c) + i) with (A + (Z.of_nat (csize c) + i)) by lia. apply W2. lia.
Qed.

Lemma cau_join : forall m A B cs1 cs2, rw_cells rsegs m A cs1 -> rw_cells rsegs m B cs2 ->
  B = A + Z.of_nat (cells_size cs1) -> rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros m A B cs1 cs2 [[Hw1 Hb1] (V0 & V1 & V2)] [[Hw2 Hb2] (U0 & U1 & U2)] ->.
  split; [split|].
  - apply cells_wf_app. tauto.
  - rewrite cells_bytes_app. apply (proj2 (bytes_at_app rsegs _ _ _ _)). split; [exact Hb1|].
    rewrite cells_bytes_length by exact Hw1. exact Hb2.
  - rewrite cells_size_app. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z_lt_le_dec i (Z.of_nat (cells_size cs1))) as [L|L].
    + apply V2. lia.
    + replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia.
      apply U2. lia.
Qed.

Lemma cau_cells_mid : forall m A pre cs post, cells_at rsegs m A (pre ++ cs ++ post) ->
  cells_at rsegs m (A + Z.of_nat (cells_size pre)) cs.
Proof.
  intros m A pre cs post [Hwf Hb].
  apply cells_wf_app in Hwf. destruct Hwf as [H1 H23]. apply cells_wf_app in H23. destruct H23 as [H2 H3].
  rewrite !cells_bytes_app in Hb. apply (proj1 (bytes_at_app rsegs _ _ _ _)) in Hb. destruct Hb as [_ Hb].
  apply (proj1 (bytes_at_app rsegs _ _ _ _)) in Hb. destruct Hb as [Hb _].
  rewrite cells_bytes_length in Hb by exact H1. split; assumption.
Qed.

Lemma cau_sub : forall m A B cs i j, cells_at rsegs m A cs -> B = A + Z.of_nat (cells_size (firstn i cs)) ->
  bytes_at rsegs m B (cells_bytes (firstn j (skipn i cs))).
Proof.
  intros m A B cs i j H ->.
  apply (cau_cells_mid m A (firstn i cs) (firstn j (skipn i cs)) (skipn j (skipn i cs))).
  rewrite !firstn_skipn. exact H.
Qed.

(** * Bytes *)

Lemma cau_skipn_nth : forall (bs : list byte) i, (i < length bs)%nat ->
  skipn i bs = nth i bs (b8 0) :: skipn (S i) bs.
Proof.
  induction bs as [|x bs IH]; intros [|i] Hi; cbn [length] in Hi; try lia; [reflexivity|].
  cbn [skipn nth]. apply IH. lia.
Qed.

Lemma cau_rd1 : forall m a bs i, bytes_at rsegs m a bs -> (i < length bs)%nat ->
  ov_read_bytes rsegs m (wa (a + Z.of_nat i)) 1 = Some [nth i bs (b8 0)].
Proof.
  intros m a bs i H Hi. rewrite (bytes_at_ov_read rsegs m a bs i 1 H) by lia.
  rewrite (cau_skipn_nth bs i Hi). reflexivity.
Qed.

(* The body of the frame: the bytes of b from 30, inside b. *)
Lemma cau_body_at : forall m buf b, fr_code b = 0 -> bytes_at rsegs m buf b ->
  bytes_at rsegs m (buf + 30) (fr_body b).
Proof.
  intros m buf b HC HB.
  destruct (fr_body_len_ok b HC) as (L1 & L2 & L3).
  rewrite <- (firstn_skipn 30 b) in HB. apply (proj1 (bytes_at_app rsegs _ _ _ _)) in HB.
  destruct HB as [_ HB]. rewrite length_firstn in HB. replace (Nat.min 30 (length b)) with 30%nat in HB by lia.
  unfold fr_body. rewrite <- (firstn_skipn (Z.to_nat (fr_body_len b)) (skipn 30 b)) in HB.
  apply (proj1 (bytes_at_app rsegs _ _ _ _)) in HB. destruct HB as [HB _]. exact HB.
Qed.

Lemma cau_body_len : forall b, fr_code b = 0 -> Z.of_nat (length (fr_body b)) = fr_body_len b.
Proof.
  intros b HC. rewrite (length_fr_body b HC). destruct (fr_body_len_ok b HC) as (L1 & _ & _). lia.
Qed.

Lemma cau_window : forall m a c bs k n, bytes_at rsegs m a bs -> (k + n <= length bs)%nat ->
  c = a + Z.of_nat k -> bytes_at rsegs m c (firstn n (skipn k bs)).
Proof.
  intros m a c bs k n H Hk ->.
  rewrite <- (firstn_skipn k bs) in H. apply (proj1 (bytes_at_app rsegs _ _ _ _)) in H. destruct H as [_ H].
  rewrite length_firstn in H. replace (Nat.min k (length bs)) with k in H by lia.
  rewrite <- (firstn_skipn n (skipn k bs)) in H. apply (proj1 (bytes_at_app rsegs _ _ _ _)) in H.
  destruct H as [H _]. exact H.
Qed.

Lemma cau_cells_hd : forall m A c cs, cells_at rsegs m A (c :: cs) -> bytes_at rsegs m A (cbytes c).
Proof.
  intros m A c cs [Hwf Hb]. cbn [cells_bytes] in Hb.
  apply (proj1 (bytes_at_app rsegs _ _ _ _)) in Hb. tauto.
Qed.

Lemma cau_cells_2nd : forall m A B c1 c2 cs, cells_at rsegs m A (c1 :: c2 :: cs) ->
  B = A + Z.of_nat (csize c1) -> bytes_at rsegs m B (cbytes c2).
Proof.
  intros m A B c1 c2 cs [Hwf Hb] ->. cbn [cells_wf] in Hwf. destruct Hwf as [Hc1 _].
  cbn [cells_bytes] in Hb.
  apply (proj1 (bytes_at_app rsegs _ _ _ _)) in Hb. destruct Hb as [_ Hb].
  rewrite (cbytes_length c1 Hc1) in Hb.
  apply (proj1 (bytes_at_app rsegs _ _ _ _)) in Hb. tauto.
Qed.

Lemma cau_rd1z : forall m a bs (i : Z) c, bytes_at rsegs m a bs -> (0 <= i)%Z -> (Z.to_nat i < length bs)%nat ->
  c = a + i -> ov_read_bytes rsegs m (wa c) 1 = Some [nth (Z.to_nat i) bs (b8 0)].
Proof.
  intros m a bs i c H Hi Hl ->.
  replace (a + i) with (a + Z.of_nat (Z.to_nat i)) by lia.
  apply cau_rd1; assumption.
Qed.

Lemma cau_uz : forall (x : byte), bv_unsigned (zxb x) = bz x.
Proof. intros x. unfold zxb, bz. apply unsigned_lit. pose proof (bz_range x) as H. unfold bz in H. lia. Qed.

(** * Strings and bytes *)

Lemma cau_zxb_b8 : forall c, 0 <= c < 2^8 -> zxb (b8 c) = Z_to_bv 64 c.
Proof. intros c Hc. unfold zxb. f_equal. exact (bz_b8 c Hc). Qed.

Lemma cau_land_fe_range : forall c, 0 <= c < 2^8 -> 0 <= Z.land c 0xfe < 2^8.
Proof.
  assert (G : forall c, 0 <= c < 2^8 -> ((0 <=? Z.land c 0xfe) && (Z.land c 0xfe <? 2^8))%bool = true).
  { apply (byte_forall (fun c => ((0 <=? Z.land c 0xfe) && (Z.land c 0xfe <? 2^8))%bool)).
    vm_compute. reflexivity. }
  intros c Hc. pose proof (G c Hc) as H. apply andb_true_iff in H. destruct H as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

Lemma cau_memcmp_eq : forall n l r, (n <= length l)%nat -> (n <= length r)%nat ->
  firstn n l = firstn n r -> memcmp_model l r n = Some 0.
Proof.
  induction n as [|n IH]; intros [|x l] [|y r] Hl Hr HF; cbn in *; try lia; try reflexivity.
  injection HF as Hxy HF'. subst y. rewrite Z.eqb_refl. apply IH; [lia|lia|exact HF'].
Qed.

(* The alignment test at 0x13518: w & 7 for an 8-aligned w. *)
Lemma cau_land7 : forall w, w mod 8 = 0 -> Z.land w 7 = 0.
Proof. intros w H. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. exact H. Qed.

Theorem check_announce_holds :
  memset_contract -> diginet_announce_parse_contract -> bcmp_contract -> check_announce_contract.
Proof.
  intros MEMSET ANN BCMP. unfold check_announce_contract, CHECK_ANNOUNCE, U_CA_STACK.
  intros ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    buf f w lo b fj HC HBL Hf Hf8 Hw8 HB HP HW Hsp8 ST LO DB DF DW MI.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  unfold parse_cells in HP. unfold spec_cells in HW.
  pose proof (fr_body_len_ok b HC) as (BL1 & BL2 & BL3).
  pose proof (bytes_at_bound rsegs m buf b HB) as BB.
  pose proof (ro_cells_bound rsegs m f _ HP) as BF. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in BF.
  pose proof (ro_cells_bound rsegs m w _ HW) as BW. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in BW.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2^64) in Rsp.
  pose proof ST as (LO0 & _ & _).
  pose proof (cau_land7 w Hw8) as W7.
  carve_frame 80%nat ST.
  do 7 step.
  (* 0x1351c: the UBSan alignment check of w (w & 7), not taken *)
  step.
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false;
      [ cbv iota
      | symmetry; unfold_cond; rewrite (unsigned_lit w) by lia; rewrite W7; fold_lit_ux; solve_cond_rec ]
  end.
  do 5 step.
  lazymatch type of FR with rw_cells _ ?mm ?A ?cs => split_for_access FR rsegs mm A cs 8%nat 40%nat end.
  destruct (cau_split1 _ _ (bv_unsigned sp + -72) _ _ FR ltac:(cbn; lia)) as [FR0 FRx]. clear FR.
  destruct (cau_split1 _ _ (bv_unsigned sp + -32) _ _ FRx ltac:(cbn; lia)) as [FA FR]. clear FRx.
  (* memset (&a, 0xa5, 40) *)
  step.
  eapply evt_cut.
  { eapply MEMSET; [ | exact MI ].
    rewrite (unsigned_lit (bv_unsigned sp + -72)) by lia. exact FA. }
  intros ms' PO. unfold memset_post in PO.
  destruct PO as (c5 & c6 & c7 & c11 & c12 & c13 & c14 & c15 & c16 & c17 & c28 & c29 & c30 & c31 & m2
    & -> & MU2 & WM2 & MI2 & HZ).
  rewrite (unsigned_lit (bv_unsigned sp + -72)) in MU2, HZ by lia.
  change (bv_unsigned (Z_to_bv 64 40)) with 40 in MU2, HZ.
  change (Z.to_nat 40) with 40%nat in HZ.
  lazymatch type of HZ with rw_cells _ _ _ [CB _ ?l] => set (aj := l) in HZ end.
  assert (Laj : length aj = 40%nat) by (unfold aj; apply repeat_length).
  clear FA.
  transport_after_call rsegs m1 m2 MU2 WM2.
  clear MU2 WM2 MI.
  replace (ret_pc (Z_to_bv 64 0x13538)) with (Z_to_bv 64 0x13538) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  (* diginet_announce_parse (f, &a) *)
  do 3 step.
  eapply evt_cut.
  { eapply ANN with (f := f) (ap := bv_unsigned sp + -72) (cmd := fr_cmd b) (body := buf + 30) (lo := lo)
                    (bb := fr_body b) (aj := aj).
    - exact Hf.
    - lia.
    - exact Hf8.
    - replace (bv_unsigned sp + -72) with (bv_unsigned sp + (-9) * 8) by lia. rewrite Z_mod_plus_full. exact Hsp8.
    - apply at8_range.
    - lia.
    - eapply (cau_sub _ _ _ _ 9 1 HP). cbn. lia.
    - rewrite (cau_body_len b HC).
      pose proof (cau_sub _ _ (f + 32) _ 11 2 HP ltac:(cbn; lia)) as H32.
      cbn [firstn skipn cells_bytes cbytes] in H32. rewrite app_nil_r in H32. exact H32.
    - exact (cau_body_at m2 buf b HC HB).
    - exact HZ.
    - lia.
    - rewrite (cau_body_len b HC). lia.
    - rewrite (unsigned_lit (bv_unsigned sp + -80)) by lia. exact ST.
    - unfold ANN_STACK. rewrite (unsigned_lit (bv_unsigned sp + -80)) by lia. lia.
    - unfold ANN_STACK. rewrite (unsigned_lit (bv_unsigned sp + -80)) by lia. lia.
    - unfold ANN_STACK. rewrite (cau_body_len b HC). rewrite (unsigned_lit (bv_unsigned sp + -80)) by lia. lia.
    - unfold ANN_STACK. rewrite (unsigned_lit (bv_unsigned sp + -80)) by lia. lia.
    - exact MI2. }
  intros ms' PO.
  destruct PO as (d1 & d2 & d3 & d4 & d5 & d6 & d7 & m3 & -> & MU3 & WM3 & MI3 & ST3 & HA).
  rewrite (unsigned_lit (bv_unsigned sp + -80)) in MU3, ST3 by lia.
  unfold ANN_STACK in MU3.
  clear ST.
  transport_after_call rsegs m2 m3 MU3 WM3.
  clear MU3 WM3 MI2.
  rename ST3 into ST.
  replace (ret_pc (Z_to_bv 64 0x13544)) with (Z_to_bv 64 0x13544) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  rewrite (cau_body_len b HC) in HA |- *.
  assert (CR : 0 <= fr_cmd b < 2^8) by (unfold fr_cmd; apply at8_range).
  rewrite (cau_zxb_b8 (fr_cmd b) CR).
  (* the epilogue, common to the three exits *)
  assert (EPI : forall (m' : word -> option byte) (j0 aa : list byte)
                  (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 : word),
    rw_cells rsegs m' (bv_unsigned sp + -80) [CB 8 j0] ->
    rw_cells rsegs m' (bv_unsigned sp + -72) [CB 40 aa] ->
    rw_cells rsegs m' (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs m' lo (bv_unsigned sp + -80) ->
    munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
    evt rsegs QQ
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16
                x17 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x13684) fc None m' (seg_rom rsegs))).
  { intros m' j0 aa x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31
      E0 EA E32 ST' MU' WM' MI'.
    pose proof (cau_join m' _ _ _ _ E0 EA ltac:(cbn [cells_size csize app Nat.add]; lia)) as J1.
    pose proof (cau_join m' _ _ _ _ J1 E32 ltac:(cbn [cells_size csize app Nat.add]; lia)) as J2.
    clear J1 E0 EA E32. cbn [app] in J2.
    do 6 step.
    release_frame J2 ST' (bv_unsigned sp).
    apply evt_done. unfold QQ. do 16 eexists.
    split; [reflexivity|]. split; [exact MU'|]. split; [exact WM'|]. split; [exact MI' | exact ST']. }
  assert (UBL : bv_unsigned (Z_to_bv 64 (fr_body_len b)) = fr_body_len b) by (apply unsigned_lit; lia).
  assert (UBC : bv_unsigned (Z_to_bv 64 (Z.land (fr_cmd b) 0xfe)) = Z.land (fr_cmd b) 0xfe)
    by (apply unsigned_lit; pose proof (cau_land_fe_range (fr_cmd b) CR); lia).
  unfold ann_code in HA |- *.
  destruct (ann_cmd (fr_cmd b)) eqn:EA; cbn [negb] in HA |- *.
  - (* an announce command *)
    assert (L224 : Z.land (fr_cmd b) 0xfe = 0xe0)
      by (apply Z.eqb_eq; rewrite (ann_cmd_land (fr_cmd b) CR); exact EA).
    destruct (Z.ltb_spec (fr_body_len b) 33) as [SHORT|LONG]; cbn [Z.eqb] in HA |- *.
    + (* DIGINET_E_LENGTH: the body is shorter than 33 bytes *)
      step. step. rewrite (unsigned_lit (fr_cmd b)) by lia. rewrite L224.
      step. if_false.
      step. step. if_false.
      step. step. if_false.
      step. step. step. if_true.
      step. if_false.
      step. step. if_false.
      step. if_true.
      eapply EPI; eassumption.
    + (* DIGINET_OK *)
      step. step. rewrite (unsigned_lit (fr_cmd b)) by lia. rewrite L224.
      step. if_false.
      step. step. if_false.
      step. step. if_false.
      step. step. step. if_false.
      step. step. if_false.
      step. if_true.
      step. if_false.
      (* the body, the two strings it holds and the two fields of the announce *)
      pose proof (cau_body_at m3 buf b HC HB) as HBD.
      assert (LBD : (33 <= length (fr_body b))%nat) by (rewrite (length_fr_body b HC); lia).
      assert (UB30 : bv_unsigned (Z_to_bv 64 (buf + 30)) = buf + 30) by (apply unsigned_lit; lia).
      assert (UA4 : bv_unsigned (Z_to_bv 64 (18446744073709551615 - (buf + 45)))
                    = 18446744073709551615 - (buf + 45)) by (apply unsigned_lit; lia).
      assert (UA3 : bv_unsigned (Z_to_bv 64 (18446744073709551615 - (buf + 54)))
                    = 18446744073709551615 - (buf + 54)) by (apply unsigned_lit; lia).
      unfold ann_cells in HA.
      pose proof (cau_window m3 (buf + 30) (buf + 45) (fr_body b) 15 9 HBD ltac:(lia) ltac:(lia)) as HV9.
      pose proof (cau_window m3 (buf + 30) (buf + 54) (fr_body b) 24 9 HBD ltac:(lia) ltac:(lia)) as HN9.
      pose proof (cau_cells_hd m3 _ _ _ (proj1 HA)) as HVB.
      pose proof (cau_cells_2nd m3 (bv_unsigned sp + -72) (bv_unsigned sp + -62) _ _ _ (proj1 HA)
        ltac:(cbn [csize]; lia)) as HNB.
      cbn [cbytes] in HVB, HNB.
      assert (LP1 : length (firstn 9 (skipn 15 (fr_body b))) = 9%nat)
        by (rewrite length_firstn, length_skipn; lia).
      assert (LP2 : length (firstn 9 (skipn 24 (fr_body b))) = 9%nat)
        by (rewrite length_firstn, length_skipn; lia).
      assert (LV : length (ann_version (fr_body b) (firstn 10 aj)) = 10%nat)
        by (unfold ann_version; apply length_copy_strz; rewrite length_firstn; lia).
      assert (LN : length (ann_name (fr_body b) (firstn 10 (skipn 10 aj))) = 10%nat)
        by (unfold ann_name; apply length_copy_strz; rewrite length_firstn, length_skipn; lia).
      assert (EV : nz_run (firstn 10 (ann_version (fr_body b) (firstn 10 aj)))
                 = nz_run (firstn 9 (skipn 15 (fr_body b))))
        by exact (field_len_copy_strz (skipn 15 (fr_body b)) (firstn 10 aj)).
      assert (EN : nz_run (firstn 10 (ann_name (fr_body b) (firstn 10 (skipn 10 aj))))
                 = nz_run (firstn 9 (skipn 24 (fr_body b))))
        by exact (field_len_copy_strz (skipn 24 (fr_body b)) (firstn 10 (skipn 10 aj))).
      assert (FV : firstn (nz_run (firstn 9 (skipn 15 (fr_body b)))) (ann_version (fr_body b) (firstn 10 aj))
                 = firstn (nz_run (firstn 9 (skipn 15 (fr_body b)))) (firstn 9 (skipn 15 (fr_body b)))).
      { unfold ann_version. rewrite firstn_firstn.
        replace (Nat.min (nz_run (firstn 9 (skipn 15 (fr_body b)))) 9)
          with (nz_run (firstn 9 (skipn 15 (fr_body b))))
          by (pose proof (nz_run_le (firstn 9 (skipn 15 (fr_body b)))) as HL; rewrite LP1 in HL; lia).
        exact (copy_strz_prefix (skipn 15 (fr_body b)) (firstn 10 aj)). }
      assert (FN : firstn (nz_run (firstn 9 (skipn 24 (fr_body b)))) (ann_name (fr_body b) (firstn 10 (skipn 10 aj)))
                 = firstn (nz_run (firstn 9 (skipn 24 (fr_body b)))) (firstn 9 (skipn 24 (fr_body b)))).
      { unfold ann_name. rewrite firstn_firstn.
        replace (Nat.min (nz_run (firstn 9 (skipn 24 (fr_body b)))) 9)
          with (nz_run (firstn 9 (skipn 24 (fr_body b))))
          by (pose proof (nz_run_le (firstn 9 (skipn 24 (fr_body b)))) as HL; rewrite LP2 in HL; lia).
        exact (copy_strz_prefix (skipn 24 (fr_body b)) (firstn 10 (skipn 10 aj))). }
      set (P1 := firstn 9 (skipn 15 (fr_body b))) in *.
      set (P2 := firstn 9 (skipn 24 (fr_body b))) in *.
      set (VS := ann_version (fr_body b) (firstn 10 aj)) in *.
      set (NS := ann_name (fr_body b) (firstn 10 (skipn 10 aj))) in *.
      assert (V9 : (nz_run P1 <= 9)%nat) by (pose proof (nz_run_le P1); lia).
      assert (N9 : (nz_run P2 <= 9)%nat) by (pose proof (nz_run_le P2); lia).
      assert (FVS : firstn 10 VS = VS) by (apply firstn_all2; lia).
      assert (FNS : firstn 10 NS = NS) by (apply firstn_all2; lia).
      rewrite FVS in EV. rewrite FNS in EN.
      assert (VC9 : (nz_run VS <= 10)%nat) by (pose proof (nz_run_le VS); lia).
      assert (NC9 : (nz_run NS <= 10)%nat) by (pose proof (nz_run_le NS); lia).
      (* a.unknown is w->body, a.unknown_len is 15 *)
      step. step. step. if_false.
      step. step. step. if_false.
      (* the UBSan checks of w->body + 15: not 0, no wrap *)
      step. if_false.
      step. step. if_false.
      step. step. step.
      rewrite (unsigned_lit (buf + 45)) by lia. rewrite (ZBridge.zb_lxor_ones (buf + 45)) by lia.
      (* loop 1: spec_strz_len (w->body + 15), with the UBSan check of w->body + 15 + i *)
      assert (LOOP1 :
        evt rsegs QQ
          (MS (mkR (Z_to_bv 64 0x13544) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp c5 c6 c7
                (Z_to_bv 64 (buf + 30)) (Z_to_bv 64 f)
                (Z_to_bv 64 (buf + 30)) (Z_to_bv 64 (buf + 45))
                (Z_to_bv 64 (Z.of_nat (nz_run P1))) (Z_to_bv 64 (Z.of_nat (nz_run P1)))
                (Z_to_bv 64 (18446744073709551615 - (buf + 45))) d5 d6 d7 (Z_to_bv 64 (fr_cmd b))
                s3 s4 s5 s6 s7 s8 s9 s10 s11 c28 c29 c30 c31)
              F (Z_to_bv 64 0x135d8) fc None m3 (seg_rom rsegs)) ->
        forall (n : nat) (i : Z) (y12 : word),
        0 <= i -> i + Z.of_nat (S n) = 9 ->
        (forall j, (j < Z.to_nat i)%nat -> at8 P1 j <> 0) ->
        evt rsegs QQ
          (MS (mkR (Z_to_bv 64 0x13544) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp c5 c6 c7
                (Z_to_bv 64 (buf + 30)) (Z_to_bv 64 f)
                (Z_to_bv 64 (buf + 30)) (Z_to_bv 64 (buf + 45))
                y12 (Z_to_bv 64 i)
                (Z_to_bv 64 (18446744073709551615 - (buf + 45))) d5 d6 d7 (Z_to_bv 64 (fr_cmd b))
                s3 s4 s5 s6 s7 s8 s9 s10 s11 c28 c29 c30 c31)
              F (Z_to_bv 64 0x135b4) fc None m3 (seg_rom rsegs))).
      { intros K n. induction n as [|n IH]; intros i y12 Hi Hn Hnz.
        all: assert (UI : bv_unsigned (Z_to_bv 64 i) = i) by (apply unsigned_lit; lia).
        all: assert (UBI : bv_unsigned (Z_to_bv 64 (i + 1)) = i + 1) by (apply unsigned_lit; lia).
        all: pose proof (cau_rd1z m3 (buf + 45) P1 i (buf + 45 + i) HV9 ltac:(lia) ltac:(lia) eq_refl) as R.
        all: assert (UZ : bv_unsigned (zxb (nth (Z.to_nat i) P1 (b8 0))) = at8 P1 (Z.to_nat i))
               by (unfold at8; apply cau_uz).
        all: step; if_false.
        all: step; step; clear R; step.
        all: destruct (Z.eq_dec (at8 P1 (Z.to_nat i)) 0) as [Z0|Zn].
        - if_true. step.
          assert (NZ : nz_run P1 = Z.to_nat i)
            by (apply nz_run_char; [lia | exact Hnz | intros _; exact Z0]).
          replace i with (Z.of_nat (nz_run P1)) by (rewrite NZ; lia). exact K.
        - if_false. step. step. step. if_false. step.
          assert (NZ : nz_run P1 = 9%nat).
          { apply nz_run_char; [lia | | intros HH; exfalso; lia].
            intros j Hj. destruct (Nat.eq_dec j (Z.to_nat i)) as [->|Hne]; [exact Zn | apply Hnz; lia]. }
          assert (E9 : (9:Z) = Z.of_nat (nz_run P1)) by (rewrite NZ; reflexivity).
          replace (i + 1) with (9:Z) by lia. rewrite E9. exact K.
        - if_true. step.
          assert (NZ : nz_run P1 = Z.to_nat i)
            by (apply nz_run_char; [lia | exact Hnz | intros _; exact Z0]).
          replace i with (Z.of_nat (nz_run P1)) by (rewrite NZ; lia). exact K.
        - if_false. step. step. step. if_true.
          apply (IH (i + 1) (Z_to_bv 64 9)); [lia | lia |].
          intros j Hj. destruct (Nat.eq_dec j (Z.to_nat i)) as [->|Hne]; [exact Zn | apply Hnz; lia]. }
      refine (LOOP1 _ 8%nat 0 _ ltac:(lia) ltac:(lia) ltac:(intros j Hj; exfalso; lia)).
      (* the UBSan checks of w->body + 24: no wrap *)
      step. step. if_false.
      step. step. step.
      rewrite (unsigned_lit (buf + 54)) by lia. rewrite (ZBridge.zb_lxor_ones (buf + 54)) by lia.
      step.
      (* loop 2: spec_strz_len (w->body + 24), with the UBSan check of w->body + 24 + i *)
      assert (LOOP2 :
        (forall y14 : word, evt rsegs QQ
          (MS (mkR (Z_to_bv 64 0x13544) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp c5 c6 c7
                (Z_to_bv 64 (buf + 54)) (Z_to_bv 64 (Z.of_nat (nz_run P2)))
                (Z_to_bv 64 (Z.of_nat (nz_run P2))) (Z_to_bv 64 (buf + 45))
                (Z_to_bv 64 (Z.of_nat (nz_run P1))) (Z_to_bv 64 (18446744073709551615 - (buf + 54)))
                y14 d5 d6 d7 (Z_to_bv 64 (fr_cmd b))
                s3 s4 s5 s6 s7 s8 s9 s10 s11 c28 c29 c30 c31)
              F (Z_to_bv 64 0x13610) fc None m3 (seg_rom rsegs))) ->
        forall (n : nat) (i : Z) (y14 : word),
        0 <= i -> i + Z.of_nat (S n) = 9 ->
        (forall j, (j < Z.to_nat i)%nat -> at8 P2 j <> 0) ->
        evt rsegs QQ
          (MS (mkR (Z_to_bv 64 0x13544) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp c5 c6 c7
                (Z_to_bv 64 (buf + 54)) (Z_to_bv 64 9)
                (Z_to_bv 64 i) (Z_to_bv 64 (buf + 45))
                (Z_to_bv 64 (Z.of_nat (nz_run P1))) (Z_to_bv 64 (18446744073709551615 - (buf + 54)))
                y14 d5 d6 d7 (Z_to_bv 64 (fr_cmd b))
                s3 s4 s5 s6 s7 s8 s9 s10 s11 c28 c29 c30 c31)
              F (Z_to_bv 64 0x135f0) fc None m3 (seg_rom rsegs))).
      { intros K n. induction n as [|n IH]; intros i y14 Hi Hn Hnz.
        all: assert (UI : bv_unsigned (Z_to_bv 64 i) = i) by (apply unsigned_lit; lia).
        all: assert (UBI : bv_unsigned (Z_to_bv 64 (i + 1)) = i + 1) by (apply unsigned_lit; lia).
        all: pose proof (cau_rd1z m3 (buf + 54) P2 i (buf + 54 + i) HN9 ltac:(lia) ltac:(lia) eq_refl) as R.
        all: assert (UZ : bv_unsigned (zxb (nth (Z.to_nat i) P2 (b8 0))) = at8 P2 (Z.to_nat i))
               by (unfold at8; apply cau_uz).
        all: step; if_false.
        all: step; step; clear R; step.
        all: destruct (Z.eq_dec (at8 P2 (Z.to_nat i)) 0) as [Z0|Zn].
        - if_true. step.
          assert (NZ : nz_run P2 = Z.to_nat i)
            by (apply nz_run_char; [lia | exact Hnz | intros _; exact Z0]).
          replace i with (Z.of_nat (nz_run P2)) by (rewrite NZ; lia). apply K.
        - if_false. step. step. if_false. step.
          assert (NZ : nz_run P2 = 9%nat).
          { apply nz_run_char; [lia | | intros HH; exfalso; lia].
            intros j Hj. destruct (Nat.eq_dec j (Z.to_nat i)) as [->|Hne]; [exact Zn | apply Hnz; lia]. }
          assert (E9 : (9:Z) = Z.of_nat (nz_run P2)) by (rewrite NZ; reflexivity).
          replace (i + 1) with (9:Z) by lia. rewrite E9. apply K.
        - if_true. step.
          assert (NZ : nz_run P2 = Z.to_nat i)
            by (apply nz_run_char; [lia | exact Hnz | intros _; exact Z0]).
          replace i with (Z.of_nat (nz_run P2)) by (rewrite NZ; lia). apply K.
        - if_false. step. step. if_true.
          apply (IH (i + 1) (zxb (nth (Z.to_nat i) P2 (b8 0)))); [lia | lia |].
          intros j Hj. destruct (Nat.eq_dec j (Z.to_nat i)) as [->|Hne]; [exact Zn | apply Hnz; lia]. }
      refine (LOOP2 _ 8%nat 0 _ ltac:(lia) ltac:(lia) ltac:(intros j Hj; exfalso; lia)).
      intros y14.
      (* loop 3: field_len (a.version, 10) *)
      step. step.
      assert (LOOP3 :
        evt rsegs QQ
          (MS (mkR (Z_to_bv 64 0x13544) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp c5 c6 c7
                (Z_to_bv 64 (buf + 54)) (Z_to_bv 64 (Z.of_nat (nz_run P2)))
                (Z_to_bv 64 (Z.of_nat (nz_run VS))) (Z_to_bv 64 (buf + 45))
                (Z_to_bv 64 (Z.of_nat (nz_run P1))) (Z_to_bv 64 (bv_unsigned sp + -72))
                (Z_to_bv 64 (Z.of_nat (nz_run VS))) d5 d6 d7 (Z_to_bv 64 (fr_cmd b))
                s3 s4 s5 s6 s7 s8 s9 s10 s11 c28 c29 c30 c31)
              F (Z_to_bv 64 0x13638) fc None m3 (seg_rom rsegs)) ->
        forall (n : nat) (i : Z) (y15 : word),
        0 <= i -> i + Z.of_nat (S n) = 10 ->
        (forall j, (j < Z.to_nat i)%nat -> at8 VS j <> 0) ->
        evt rsegs QQ
          (MS (mkR (Z_to_bv 64 0x13544) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp c5 c6 c7
                (Z_to_bv 64 (buf + 54)) (Z_to_bv 64 (Z.of_nat (nz_run P2)))
                (Z_to_bv 64 i) (Z_to_bv 64 (buf + 45))
                (Z_to_bv 64 (Z.of_nat (nz_run P1))) (Z_to_bv 64 (bv_unsigned sp + -72))
                y15 d5 d6 d7 (Z_to_bv 64 (fr_cmd b))
                s3 s4 s5 s6 s7 s8 s9 s10 s11 c28 c29 c30 c31)
              F (Z_to_bv 64 0x13618) fc None m3 (seg_rom rsegs))).
      { intros K n. induction n as [|n IH]; intros i y15 Hi Hn Hnz.
        all: assert (UBI : bv_unsigned (Z_to_bv 64 (i + 1)) = i + 1) by (apply unsigned_lit; lia).
        all: pose proof (cau_rd1z m3 (bv_unsigned sp + -72) VS i (bv_unsigned sp + -72 + i) HVB
               ltac:(lia) ltac:(lia) eq_refl) as R.
        all: assert (UZ : bv_unsigned (zxb (nth (Z.to_nat i) VS (b8 0))) = at8 VS (Z.to_nat i))
               by (unfold at8; apply cau_uz).
        all: step; step; clear R; step.
        all: destruct (Z.eq_dec (at8 VS (Z.to_nat i)) 0) as [Z0|Zn].
        - if_true. step.
          assert (NZ : nz_run VS = Z.to_nat i)
            by (apply nz_run_char; [lia | exact Hnz | intros _; exact Z0]).
          replace i with (Z.of_nat (nz_run VS)) by (rewrite NZ; lia). exact K.
        - if_false. step. step. step. if_false. step.
          assert (NZ : nz_run VS = 10%nat).
          { apply nz_run_char; [lia | | intros HH; exfalso; lia].
            intros j Hj. destruct (Nat.eq_dec j (Z.to_nat i)) as [->|Hne]; [exact Zn | apply Hnz; lia]. }
          assert (E10 : (10:Z) = Z.of_nat (nz_run VS)) by (rewrite NZ; reflexivity).
          replace (i + 1) with (10:Z) by lia. rewrite E10. exact K.
        - if_true. step.
          assert (NZ : nz_run VS = Z.to_nat i)
            by (apply nz_run_char; [lia | exact Hnz | intros _; exact Z0]).
          replace i with (Z.of_nat (nz_run VS)) by (rewrite NZ; lia). exact K.
        - if_false. step. step. step. if_true.
          apply (IH (i + 1) (Z_to_bv 64 10)); [lia | lia |].
          intros j Hj. destruct (Nat.eq_dec j (Z.to_nat i)) as [->|Hne]; [exact Zn | apply Hnz; lia]. }
      refine (LOOP3 _ 9%nat 0 _ ltac:(lia) ltac:(lia) ltac:(intros j Hj; exfalso; lia)).
      (* the version the library wrote is the string the harness read *)
      rewrite EV.
      step. if_false.
      step. step.
      eapply evt_cut.
      { eapply BCMP with (ls := VS) (rs := P1) (v := 0).
        - rewrite (unsigned_lit (bv_unsigned sp + -72)) by lia. exact HVB.
        - rewrite (unsigned_lit (buf + 45)) by lia. exact HV9.
        - rewrite (unsigned_lit (Z.of_nat (nz_run P1))) by lia. rewrite Nat2Z.id.
          apply cau_memcmp_eq; [lia | lia | exact FV].
        - exact MI3. }
      intros ms' PO. unfold memcmp_post in PO.
      destruct PO as (e5 & e6 & e7 & e11 & e12 & e13 & e14 & e15 & e16 & e17 & e28 & e29 & e30 & e31 & m4
        & -> & MU4 & WM4 & MI4 & HL4 & HR4).
      transport_after_call rsegs m3 m4 MU4 WM4.
      clear MU4 WM4 MI3 HL4 HR4.
      replace (ret_pc (Z_to_bv 64 0x13644)) with (Z_to_bv 64 0x13644)
        by (symmetry; apply ret_pc_even; [lia | reflexivity]).
      step. if_false.
      (* loop 4: field_len (a.name, 10) *)
      step. step.
      assert (LOOP4 :
        evt rsegs QQ
          (MS (mkR (Z_to_bv 64 0x13644) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp e5 e6 e7
                (Z_to_bv 64 (buf + 54)) (Z_to_bv 64 (Z.of_nat (nz_run P2)))
                (Z_to_bv 64 (bv_unsigned sp + -62)) (Z_to_bv 64 (Z.of_nat (nz_run NS)))
                (Z_to_bv 64 (Z.of_nat (nz_run NS))) e13 e14 e15 e16 e17 (Z_to_bv 64 (fr_cmd b))
                s3 s4 s5 s6 s7 s8 s9 s10 s11 e28 e29 e30 e31)
              F (Z_to_bv 64 0x13670) fc None m4 (seg_rom rsegs)) ->
        forall (n : nat) (i : Z) (y12 : word),
        0 <= i -> i + Z.of_nat (S n) = 10 ->
        (forall j, (j < Z.to_nat i)%nat -> at8 NS j <> 0) ->
        evt rsegs QQ
          (MS (mkR (Z_to_bv 64 0x13644) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp e5 e6 e7
                (Z_to_bv 64 (buf + 54)) (Z_to_bv 64 (Z.of_nat (nz_run P2)))
                (Z_to_bv 64 (bv_unsigned sp + -62)) (Z_to_bv 64 i)
                y12 e13 e14 e15 e16 e17 (Z_to_bv 64 (fr_cmd b))
                s3 s4 s5 s6 s7 s8 s9 s10 s11 e28 e29 e30 e31)
              F (Z_to_bv 64 0x13650) fc None m4 (seg_rom rsegs))).
      { intros K n. induction n as [|n IH]; intros i y12 Hi Hn Hnz.
        all: assert (UBI : bv_unsigned (Z_to_bv 64 (i + 1)) = i + 1) by (apply unsigned_lit; lia).
        all: pose proof (cau_rd1z m4 (bv_unsigned sp + -62) NS i (bv_unsigned sp + -62 + i) HNB
               ltac:(lia) ltac:(lia) eq_refl) as R.
        all: assert (UZ : bv_unsigned (zxb (nth (Z.to_nat i) NS (b8 0))) = at8 NS (Z.to_nat i))
               by (unfold at8; apply cau_uz).
        all: step; step; clear R; step.
        all: destruct (Z.eq_dec (at8 NS (Z.to_nat i)) 0) as [Z0|Zn].
        - if_true. step.
          assert (NZ : nz_run NS = Z.to_nat i)
            by (apply nz_run_char; [lia | exact Hnz | intros _; exact Z0]).
          replace i with (Z.of_nat (nz_run NS)) by (rewrite NZ; lia). exact K.
        - if_false. step. step. step. if_false. step.
          assert (NZ : nz_run NS = 10%nat).
          { apply nz_run_char; [lia | | intros HH; exfalso; lia].
            intros j Hj. destruct (Nat.eq_dec j (Z.to_nat i)) as [->|Hne]; [exact Zn | apply Hnz; lia]. }
          assert (E10 : (10:Z) = Z.of_nat (nz_run NS)) by (rewrite NZ; reflexivity).
          replace (i + 1) with (10:Z) by lia. rewrite E10. exact K.
        - if_true. step.
          assert (NZ : nz_run NS = Z.to_nat i)
            by (apply nz_run_char; [lia | exact Hnz | intros _; exact Z0]).
          replace i with (Z.of_nat (nz_run NS)) by (rewrite NZ; lia). exact K.
        - if_false. step. step. step. if_true.
          apply (IH (i + 1) (Z_to_bv 64 10)); [lia | lia |].
          intros j Hj. destruct (Nat.eq_dec j (Z.to_nat i)) as [->|Hne]; [exact Zn | apply Hnz; lia]. }
      refine (LOOP4 _ 9%nat 0 _ ltac:(lia) ltac:(lia) ltac:(intros j Hj; exfalso; lia)).
      (* the name the library wrote is the string the harness read *)
      rewrite EN.
      step. if_false.
      step. step. step.
      eapply evt_cut.
      { eapply BCMP with (ls := NS) (rs := P2) (v := 0).
        - rewrite (unsigned_lit (bv_unsigned sp + -62)) by lia. exact HNB.
        - rewrite (unsigned_lit (buf + 54)) by lia. exact HN9.
        - rewrite (unsigned_lit (Z.of_nat (nz_run P2))) by lia. rewrite Nat2Z.id.
          apply cau_memcmp_eq; [lia | lia | exact FN].
        - exact MI4. }
      intros ms' PO. unfold memcmp_post in PO.
      destruct PO as (g5 & g6 & g7 & g11 & g12 & g13 & g14 & g15 & g16 & g17 & g28 & g29 & g30 & g31 & m5
        & -> & MU5 & WM5 & MI5 & HL5 & HR5).
      transport_after_call rsegs m4 m5 MU5 WM5.
      clear MU5 WM5 MI4 HL5 HR5.
      replace (ret_pc (Z_to_bv 64 0x13680)) with (Z_to_bv 64 0x13680)
        by (symmetry; apply ret_pc_even; [lia | reflexivity]).
      step. if_false.
      destruct (rw_cells_forget rsegs m5 _ _ HA) as [aa HAA].
      cbn [cells_size csize Nat.add] in HAA.
      eapply EPI; eassumption.
  - (* not an announce command *)
    cbn [Z.eqb] in HA.
    assert (LNE : Z.land (fr_cmd b) 0xfe <> 0xe0).
    { intros E. assert (T : (Z.land (fr_cmd b) 0xfe =? 0xe0) = true) by (apply Z.eqb_eq; exact E).
      rewrite (ann_cmd_land (fr_cmd b) CR), EA in T. discriminate. }
    step. step. rewrite (unsigned_lit (fr_cmd b)) by lia.
    step. if_true.
    step. step. if_true.
    step. if_true.
    eapply EPI; eassumption.
Qed.
