From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import sb_dec_c.
Import ListNotations.
Open Scope Z_scope.

Lemma sbd_stk_wr : forall m lo hi a k, stk rsegs m lo hi -> lo <= a -> a + k <= hi -> 0 <= k -> wr_at rsegs m a k.
Proof.
  intros m lo hi a k (H1 & H2 & H) Ha Hk K0. split; [lia|]. split; [lia|].
  intros i Hi. apply (H (a + i)). lia.
Qed.

Lemma sbd_wr_sub : forall m a k a' k', wr_at rsegs m a k -> a <= a' -> a' + k' <= a + k -> 0 <= k' -> wr_at rsegs m a' k'.
Proof.
  intros m a k a' k' (H1 & H2 & H) Ha Hk K0. split; [lia|]. split; [lia|].
  intros i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply H. lia.
Qed.

Lemma sbd_le1b : forall b : byte, le1 (Z_to_bv 64 (bv_unsigned b)) = [b].
Proof. exact le1_zxb. Qed.

Lemma sbd_le1 : forall z, 0 <= z < 2^64 -> le1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof. intros z Hz. unfold le1. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma sbd_swrap : forall z, -2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof.
  intros z Hz. change (bv_swrap 32 z) with ((z + 2^31) mod 2^32 - 2^31).
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma sbd_q : forall x, 0 <= x < 2^31 ->
  bv_swrap 32 (Z.shiftr (bv_signed (Z_to_bv 64 (x * 1717986919))) 34 mod 18446744073709551616 +
               Z.shiftr (x * 1717986919) 63) = x / 10.
Proof.
  intros x Hx.
  rewrite zb_signed, unsigned_lit by lia.
  replace (x * 1717986919 <? 2^63) with true by (symmetry; apply Z.ltb_lt; lia).
  rewrite !Z.shiftr_div_pow2 by lia.
  rewrite (Z.div_small (x * 1717986919) (2^63)) by lia.
  replace (x * 1717986919 / 2^34) with (x / 10).
  2: { pose proof (Z.mod_pos_bound x 10 ltac:(lia)). pose proof (Z.div_mod x 10 ltac:(lia)).
       apply Z.div_unique_pos with (6 * (x / 10) + (x mod 10) * 1717986919); lia. }
  pose proof (Z.mod_pos_bound x 10 ltac:(lia)). pose proof (Z.div_mod x 10 ltac:(lia)).
  rewrite Z.add_0_r, Z.mod_small by lia. apply sbd_swrap. lia.
Qed.

Lemma sbd_r : forall x, 0 <= x < 2^31 ->
  bv_swrap 32 (x - (x / 10 mod 18446744073709551616 * 10) mod 18446744073709551616) = x mod 10.
Proof.
  intros x Hx. pose proof (Z.mod_pos_bound x 10 ltac:(lia)). pose proof (Z.div_mod x 10 ltac:(lia)).
  rewrite (Z.mod_small (x / 10)) by lia. rewrite (Z.mod_small (x / 10 * 10)) by lia.
  rewrite sbd_swrap by lia. lia.
Qed.

Lemma sbd_lt10 : forall x, 0 <= x < 2^31 -> bv_ltu (Z_to_bv 64 (-20)) (Z_to_bv 64 (x + -10)) = (x <? 10).
Proof.
  intros x Hx. rewrite bv_ltu_Z, !unsigned_lit_wrap.
  destruct (Z.ltb_spec x 10).
  - apply Z.ltb_lt. Z.div_mod_to_equations. lia.
  - apply Z.ltb_ge. Z.div_mod_to_equations. lia.
Qed.

Lemma sbd_bnez : forall (a : word) k, bv_unsigned a = 2^64 - k - 1 -> 0 <= k < 2^64 - 1 ->
  bv_eqb (Z_to_bv 64 (bv_unsigned a + 1)) (Z_to_bv 64 0) = (k =? 0).
Proof.
  intros a k H Hk. unfold bv_eqb. rewrite unsigned_lit_wrap, H. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  destruct (Z.eqb_spec k 0) as [->|NE]; [reflexivity|].
  apply Z.eqb_neq. rewrite Z.mod_small by lia. lia.
Qed.

Lemma sbd_room_lt : forall c n, n + 1 < c -> sb_dec_room c n = c - 1 - n /\ sb_dec_room c (n + 1) = c - 1 - (n + 1).
Proof.
  intros c n H. unfold sb_dec_room.
  destruct (Z.leb_spec (n + 1) c), (Z.leb_spec (n + 1 + 1) c); lia.
Qed.

Lemma sbd_room_ge : forall c n, c <= n + 1 -> sb_dec_room c n = 0.
Proof. intros c n H. unfold sb_dec_room. destruct (Z.leb_spec (n + 1) c); lia. Qed.

Lemma sbd_room_nn : forall c n, 0 <= sb_dec_room c n.
Proof. intros c n. unfold sb_dec_room. destruct (Z.leb_spec (n + 1) c); lia. Qed.

Lemma sbd_lsd_S : forall x j, sb_dec_lsd x (S j) = (48 + x mod 10) :: (if x <? 10 then [] else sb_dec_lsd (x / 10) j).
Proof. reflexivity. Qed.

Lemma sbd_lsd_len : forall x, 1 <= Z.of_nat (length (sb_dec_lsd x 3)) <= 3.
Proof.
  intros x. cbn [sb_dec_lsd]. destruct (x <? 10), (x / 10 <? 10), (x / 10 / 10 <? 10); cbn [length]; lia.
Qed.

Lemma sbd_D_len : forall x md, md <= 2 -> 1 <= Z.of_nat (length (sb_dec_D x md)) <= 3.
Proof.
  intros x md H. unfold sb_dec_D. pose proof (sbd_lsd_len x) as L. rewrite length_rev.
  destruct (Z.ltb_spec (Z.of_nat (length (sb_dec_lsd x 3))) md); [rewrite length_app; cbn [length]|]; lia.
Qed.

Ltac sbd_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?a ?bs) _) =>
      let E := addr_expr a in
      let H := fresh "HW" in
      assert (H : bytes_at rsegs (write_to_mem mm a bs) E bs) by (apply bytes_at_write_same; simpl_sizes; lia);
      store_done
  end.

Section Emit.
Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (b p cap : word) (lo hi : Z).

Definition sbd_at (pc : Z) (a1 a2 a4 a5 a6 a7 : word) (m : word -> option byte) : machine_state :=
  MS (mkR ra sp gp tp t0 t1 t2 s0 s1 b a1 a2 (Z_to_bv 64 1) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
     F (Z_to_bv 64 pc) fc None m (seg_rom rsegs).

Definition sbd_epost (R : list Z) (m : word -> option byte) (n : Z) (ov : word) (ms' : machine_state) : Prop :=
  exists (a1' a2' a4' a5' a6' a7' : word) (m' : word -> option byte),
    ms' = sbd_at 0x1455c a1' a2' a4' a5' a6' a7' m' /\
    munch [(bv_unsigned b + 16, bv_unsigned b + 28);
           (bv_unsigned p + n, bv_unsigned p + n + Z.min (Z.of_nat (length R)) (sb_dec_room (bv_unsigned cap) n))]
      m m' /\
    wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo hi /\
    bytes_at rsegs m' (bv_unsigned b)
      (sb_rec p cap (Z_to_bv 64 (n + Z.min (Z.of_nat (length R)) (sb_dec_room (bv_unsigned cap) n)))
         (if sb_dec_room (bv_unsigned cap) n <? Z.of_nat (length R) then Z_to_bv 64 1 else ov)) /\
    (0 < sb_dec_room (bv_unsigned cap) n ->
     bytes_at rsegs m' (bv_unsigned p + n)
       (map (Z_to_bv 8) (firstn (Z.to_nat (Z.min (Z.of_nat (length R)) (sb_dec_room (bv_unsigned cap) n))) R))).

Lemma sbd_epost_nil : forall m1 n ov a1 a2 a4 a5 a6 a7,
  0 <= n -> rw_cells rsegs m1 (bv_unsigned b) [C8 p; C8 cap; C8 (Z_to_bv 64 n); C4 ov] ->
  mem_inv rsegs m1 -> stk rsegs m1 lo hi ->
  (0 < sb_dec_room (bv_unsigned cap) n -> 0 <= bv_unsigned p + n <= 2^64) ->
  sbd_epost [] m1 n ov (sbd_at 0x1455c a1 a2 a4 a5 a6 a7 m1).
Proof.
  intros m1 n ov a1 a2 a4 a5 a6 a7 N0 FR MI ST HPN.
  pose proof (sbd_room_nn (bv_unsigned cap) n) as RN.
  exists a1, a2, a4, a5, a6, a7, m1. split; [reflexivity|].
  split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|]. split; [exact ST|]. split.
  - cbn [length]. replace (n + Z.min (Z.of_nat 0) (sb_dec_room (bv_unsigned cap) n)) with n by lia.
    replace (sb_dec_room (bv_unsigned cap) n <? Z.of_nat 0) with false by (symmetry; apply Z.ltb_ge; lia).
    destruct FR as [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. exact HB.
  - intros H. cbn [firstn map]. replace (Z.to_nat (Z.min (Z.of_nat (length (@nil Z))) (sb_dec_room (bv_unsigned cap) n))) with O by (cbn [length]; lia).
    cbn [firstn map]. apply bytes_at_nil. apply HPN. exact H.
Qed.

Lemma sbd_tr_st : forall c R m m1 n ov ms',
  0 <= n -> n + 1 < bv_unsigned cap ->
  munch [(bv_unsigned b + 16, bv_unsigned b + 28);
         (bv_unsigned p + n, bv_unsigned p + n + Z.min (Z.of_nat (length R) + 1) (sb_dec_room (bv_unsigned cap) n))] m m1 ->
  wmono rsegs m m1 ->
  bytes_at rsegs m1 (bv_unsigned p + n) [Z_to_bv 8 c] ->
  (bv_unsigned p + n + Z.min (Z.of_nat (length R) + 1) (sb_dec_room (bv_unsigned cap) n) <= bv_unsigned b \/
   bv_unsigned b + 28 <= bv_unsigned p + n) ->
  sbd_epost R m1 (n + 1) ov ms' -> sbd_epost (c :: R) m n ov ms'.
Proof.
  intros c R m m1 n ov ms' N0 HC MU WM HBY DP (a1' & a2' & a4' & a5' & a6' & a7' & m' & E & MU' & WM' & MI' & ST' & HB' & HP').
  destruct (sbd_room_lt _ _ HC) as [RM RM1].
  assert (LEN : Z.of_nat (length (c :: R)) = Z.of_nat (length R) + 1) by (cbn [length]; lia).
  pose proof (bytes_at_bound _ _ _ _ HBY) as BY. cbn [length] in BY.
  exists a1', a2', a4', a5', a6', a7', m'. split; [exact E|].
  split.
  { apply (munch_trans _ m m1 m').
    - eapply munch_weaken; [|exact MU]. intros x Hx. cbn [outside] in *. lia.
    - eapply munch_weaken; [|exact MU']. intros x Hx. cbn [outside] in *. lia. }
  split; [exact (wmono_trans _ _ _ _ WM WM')|].
  split; [exact MI'|]. split; [exact ST'|]. split.
  - replace (n + Z.min (Z.of_nat (length (c :: R))) (sb_dec_room (bv_unsigned cap) n))
      with (n + 1 + Z.min (Z.of_nat (length R)) (sb_dec_room (bv_unsigned cap) (n + 1))) by lia.
    replace (sb_dec_room (bv_unsigned cap) n <? Z.of_nat (length (c :: R)))
      with (sb_dec_room (bv_unsigned cap) (n + 1) <? Z.of_nat (length R)).
    + exact HB'.
    + rewrite RM, RM1, LEN. destruct (Z.ltb_spec (bv_unsigned cap - 1 - (n + 1)) (Z.of_nat (length R)));
        destruct (Z.ltb_spec (bv_unsigned cap - 1 - n) (Z.of_nat (length R) + 1)); try reflexivity; lia.
  - intros HR0.
    replace (Z.to_nat (Z.min (Z.of_nat (length (c :: R))) (sb_dec_room (bv_unsigned cap) n)))
      with (S (Z.to_nat (Z.min (Z.of_nat (length R)) (sb_dec_room (bv_unsigned cap) (n + 1))))) by lia.
    cbn [firstn map].
    apply (proj2 (bytes_at_app rsegs m' _ [Z_to_bv 8 c] _)). split.
    + eapply (bytes_at_transport rsegs _ m1 m'); [exact HBY | exact MU' |].
      cbn [disjoint_from length]. repeat split; lia.
    + cbn [length]. destruct (Z.ltb_spec 0 (sb_dec_room (bv_unsigned cap) (n + 1))) as [Hr|Hr].
      * replace (bv_unsigned p + n + Z.of_nat 1) with (bv_unsigned p + (n + 1)) by lia. exact (HP' Hr).
      * replace (Z.to_nat (Z.min (Z.of_nat (length R)) (sb_dec_room (bv_unsigned cap) (n + 1)))) with O by lia.
        cbn [firstn map]. apply bytes_at_nil. lia.
Qed.

Lemma sbd_tr_ov : forall c R m m1 n ov ms',
  0 <= n -> bv_unsigned cap <= n + 1 ->
  munch [(bv_unsigned b + 16, bv_unsigned b + 28);
         (bv_unsigned p + n, bv_unsigned p + n + Z.min (Z.of_nat (length R) + 1) (sb_dec_room (bv_unsigned cap) n))] m m1 ->
  wmono rsegs m m1 ->
  sbd_epost R m1 n (Z_to_bv 64 1) ms' -> sbd_epost (c :: R) m n ov ms'.
Proof.
  intros c R m m1 n ov ms' N0 HC MU WM (a1' & a2' & a4' & a5' & a6' & a7' & m' & E & MU' & WM' & MI' & ST' & HB' & HP').
  pose proof (sbd_room_ge _ _ HC) as RM.
  assert (LEN : Z.of_nat (length (c :: R)) = Z.of_nat (length R) + 1) by (cbn [length]; lia).
  exists a1', a2', a4', a5', a6', a7', m'. split; [exact E|].
  split.
  { apply (munch_trans _ m m1 m').
    - eapply munch_weaken; [|exact MU]. intros x Hx. cbn [outside] in *. lia.
    - eapply munch_weaken; [|exact MU']. intros x Hx. cbn [outside] in *. lia. }
  split; [exact (wmono_trans _ _ _ _ WM WM')|].
  split; [exact MI'|]. split; [exact ST'|]. split.
  - replace (n + Z.min (Z.of_nat (length (c :: R))) (sb_dec_room (bv_unsigned cap) n))
      with (n + Z.min (Z.of_nat (length R)) (sb_dec_room (bv_unsigned cap) n)) by lia.
    replace (if sb_dec_room (bv_unsigned cap) n <? Z.of_nat (length (c :: R)) then Z_to_bv 64 1 else ov)
      with (Z_to_bv 64 1) by (rewrite RM, LEN; replace (0 <? Z.of_nat (length R) + 1) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
    replace (if sb_dec_room (bv_unsigned cap) n <? Z.of_nat (length R) then Z_to_bv 64 1 else Z_to_bv 64 1)
      with (Z_to_bv 64 1) in HB' by (destruct (_ <? _); reflexivity).
    exact HB'.
  - intros HR0. rewrite RM in HR0. lia.
Qed.

Lemma sbd_emit : forall (R : list Z) (m : word -> option byte) (n : Z) (ov a1 a2 a4 a5 a6 a7 : word),
  R <> [] ->
  bv_unsigned a1 = 2^64 - Z.of_nat (length R) ->
  bytes_at rsegs m (bv_unsigned a2 + 1 - Z.of_nat (length R)) (map (Z_to_bv 8) (rev R)) ->
  rw_cells rsegs m (bv_unsigned b) [C8 p; C8 cap; C8 (Z_to_bv 64 n); C4 ov] ->
  0 <= n -> n + Z.of_nat (length R) < 2^64 - 1 ->
  (bv_unsigned b + 28 <= bv_unsigned a2 + 1 - Z.of_nat (length R) \/ bv_unsigned a2 + 1 <= bv_unsigned b) ->
  (0 < sb_dec_room (bv_unsigned cap) n ->
     wr_at rsegs m (bv_unsigned p + n) (Z.min (Z.of_nat (length R)) (sb_dec_room (bv_unsigned cap) n)) /\
     (bv_unsigned p + n + Z.min (Z.of_nat (length R)) (sb_dec_room (bv_unsigned cap) n) <= bv_unsigned b \/
      bv_unsigned b + 28 <= bv_unsigned p + n) /\
     (bv_unsigned p + n + Z.min (Z.of_nat (length R)) (sb_dec_room (bv_unsigned cap) n) <=
        bv_unsigned a2 + 1 - Z.of_nat (length R) \/
      bv_unsigned a2 + 1 <= bv_unsigned p + n)) ->
  mem_inv rsegs m -> stk rsegs m lo hi ->
  evt rsegs (sbd_epost R m n ov) (sbd_at 0x14524 a1 a2 a4 a5 a6 a7 m).
Proof.
  induction R as [|c R IH]; intros m n ov a1 a2 a4 a5 a6 a7 NE HA1 HD FR N0 NR DRD HP MI ST; [congruence|].
  clear NE.
  pose proof (zr_word b) as Rb. pose proof (zr_word p) as Rp. pose proof (zr_word cap) as Rc.
  pose proof (zr_word a2) as Ra2. pose proof (zr_word a1) as Ra1. unfold inr64 in *.
  assert (LEN : Z.of_nat (length (c :: R)) = Z.of_nat (length R) + 1) by (cbn [length]; lia).
  rewrite LEN in HA1, HD, NR, DRD, HP.
  assert (LHD : length (map (Z_to_bv 8) (rev R)) = length R) by (rewrite length_map, length_rev; reflexivity).
  pose proof (rw_cells_bound _ _ _ _ FR) as BR. cbn [cells_size csize Nat.add] in BR.
  cbn [rev] in HD. rewrite map_app in HD. cbn [map] in HD. apply bytes_at_app in HD. destruct HD as [HD HC].
  rewrite LHD in HC.
  pose proof (bytes_at_bound _ _ _ _ HD) as BD. rewrite LHD in BD.
  pose proof (bytes_at_bound _ _ _ _ HC) as BC. cbn [length] in BC.
  assert (HR : ov_read_bytes rsegs m a2 1 = Some [Z_to_bv 8 c]).
  { rewrite <- (wa_of_var a2 (bv_unsigned a2 + 1 - (Z.of_nat (length R) + 1) + Z.of_nat (length R) + 0)) by lia.
    rewrite (bytes_at_read rsegs m _ _ 0 1 HC) by (cbn; lia). reflexivity. }
  clear HC.
  unfold sbd_at.
  do 4 zstep.
  rewrite bv_ltu_Z, (unsigned_lit (n + 1)) by lia.
  destruct (Z.ltb_spec (n + 1) (bv_unsigned cap)) as [HC|HC]; cbn [negb].
  - destruct (sbd_room_lt _ _ HC) as [RM RM1].
    destruct (HP ltac:(lia)) as (PW & PD1 & PD2). clear HP.
    assert (BP : 0 <= bv_unsigned p + n /\
      bv_unsigned p + n + Z.min (Z.of_nat (length R) + 1) (sb_dec_room (bv_unsigned cap) n) <= 2^64)
      by (destruct PW as (? & ? & _); lia).
    pose proof (munch_refl [(bv_unsigned b + 16, bv_unsigned b + 28);
      (bv_unsigned p + n, bv_unsigned p + n + Z.min (Z.of_nat (length R) + 1) (sb_dec_room (bv_unsigned cap) n))] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    zstep. zstep. zstep. zstep.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (wr_at_store_ok rsegs mm _ _ 0 1 PW ltac:(lia) ltac:(lia)) as HS end.
    zstep.
    rewrite sbd_le1b. sbd_store. rewrite Z.add_0_r in HW.
    zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      apply (evt_mono rsegs (sbd_epost R m1 (n + 1) ov));
      [| intros ms' PO; exact (sbd_tr_st c R m m1 n ov ms' N0 HC MU WM HW PD1 PO)] end.
    destruct R as [|c' R'].
    + zstep. rewrite (sbd_bnez a1 0) by (cbn [length] in HA1; lia). if_false.
      apply evt_done. eapply sbd_epost_nil; [lia | exact FR | exact MI | exact ST | intros; lia].
    + assert (LEN2 : Z.of_nat (length (c' :: R')) = Z.of_nat (length R') + 1) by (cbn [length]; lia).
      zstep. rewrite (sbd_bnez a1 (Z.of_nat (length R') + 1)) by lia. if_true.
      eapply IH.
      * discriminate.
      * rewrite unsigned_lit by lia. lia.
      * rewrite unsigned_lit by lia.
        replace (bv_unsigned a2 + -1 + 1 - Z.of_nat (length (c' :: R')))
          with (bv_unsigned a2 + 1 - (Z.of_nat (length (c' :: R')) + 1)) by lia.
        exact HD.
      * exact FR.
      * lia.
      * lia.
      * rewrite unsigned_lit by lia. lia.
      * intros H0. rewrite unsigned_lit by lia. split; [|split].
        -- eapply sbd_wr_sub; [exact PW | lia | lia | lia].
        -- lia.
        -- lia.
      * exact MI.
      * exact ST.
  - pose proof (munch_refl [(bv_unsigned b + 16, bv_unsigned b + 28);
      (bv_unsigned p + n, bv_unsigned p + n + Z.min (Z.of_nat (length R) + 1) (sb_dec_room (bv_unsigned cap) n))] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    pose proof (sbd_room_ge _ _ HC) as RM.
    zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      apply (evt_mono rsegs (sbd_epost R m1 n (Z_to_bv 64 1)));
      [| intros ms' PO; exact (sbd_tr_ov c R m m1 n ov ms' N0 HC MU WM PO)] end.
    destruct R as [|c' R'].
    + zstep. rewrite (sbd_bnez a1 0) by (cbn [length] in HA1; lia). if_false.
      apply evt_done. eapply sbd_epost_nil; [lia | exact FR | exact MI | exact ST | intros; lia].
    + assert (LEN2 : Z.of_nat (length (c' :: R')) = Z.of_nat (length R') + 1) by (cbn [length]; lia).
      zstep. rewrite (sbd_bnez a1 (Z.of_nat (length R') + 1)) by lia. if_true.
      eapply IH.
      * discriminate.
      * rewrite unsigned_lit by lia. lia.
      * rewrite unsigned_lit by lia.
        replace (bv_unsigned a2 + -1 + 1 - Z.of_nat (length (c' :: R')))
          with (bv_unsigned a2 + 1 - (Z.of_nat (length (c' :: R')) + 1)) by lia.
        exact HD.
      * exact FR.
      * lia.
      * lia.
      * rewrite unsigned_lit by lia. lia.
      * intros H0. rewrite RM in H0. lia.
      * exact MI.
      * exact ST.
Qed.

End Emit.

Section Main.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 : word) (F : bvmap 5 word) (fc : bv 32)
  (m : word -> option byte) (lo v md : Z) (b p cap n over : word).
Hypothesis HV : 0 <= v < 2^31.
Hypothesis HMD : md = 1 \/ md = 2.
Hypothesis HN : bv_unsigned n + 1 < 2^64 - 3.
Hypothesis HP : 0 < sb_dec_room (bv_unsigned cap) (bv_unsigned n) ->
  bv_unsigned p + bv_unsigned cap <= 2^64 /\
  wr_at rsegs m (bv_unsigned p + bv_unsigned n) (sb_dec_acc v md (bv_unsigned cap) (bv_unsigned n)) /\
  (bv_unsigned p + bv_unsigned n + sb_dec_acc v md (bv_unsigned cap) (bv_unsigned n) <= bv_unsigned b \/
   bv_unsigned b + 28 <= bv_unsigned p + bv_unsigned n) /\
  (bv_unsigned p + bv_unsigned n + sb_dec_acc v md (bv_unsigned cap) (bv_unsigned n) <= bv_unsigned sp - 16 \/
   bv_unsigned sp <= bv_unsigned p + bv_unsigned n).
Hypothesis DB : bv_unsigned b + 28 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= bv_unsigned b.

Definition sbd_post (ms' : machine_state) : Prop :=
  exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp - 16, bv_unsigned sp); (bv_unsigned b + 16, bv_unsigned b + 28);
           (bv_unsigned p + bv_unsigned n,
            bv_unsigned p + bv_unsigned n + sb_dec_acc v md (bv_unsigned cap) (bv_unsigned n))] m m' /\
    wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
    bytes_at rsegs m' (bv_unsigned b)
      (sb_rec p cap (Z_to_bv 64 (bv_unsigned n + sb_dec_acc v md (bv_unsigned cap) (bv_unsigned n)))
         (if sb_dec_room (bv_unsigned cap) (bv_unsigned n) <? Z.of_nat (length (sb_dec_D v md))
          then Z_to_bv 64 1 else over)) /\
    (0 < sb_dec_room (bv_unsigned cap) (bv_unsigned n) ->
     bytes_at rsegs m' (bv_unsigned p + bv_unsigned n)
       (map (Z_to_bv 8) (firstn (Z.to_nat (sb_dec_acc v md (bv_unsigned cap) (bv_unsigned n))) (sb_dec_D v md)))).

Definition sbd_inv (m1 : word -> option byte) : Prop :=
  munch [(bv_unsigned sp - 16, bv_unsigned sp); (bv_unsigned b + 16, bv_unsigned b + 28);
         (bv_unsigned p + bv_unsigned n,
          bv_unsigned p + bv_unsigned n + sb_dec_acc v md (bv_unsigned cap) (bv_unsigned n))] m m1 /\
  wmono rsegs m m1 /\ mem_inv rsegs m1 /\ stk rsegs m1 lo (bv_unsigned sp) /\
  rw_cells rsegs m1 (bv_unsigned b) [C8 p; C8 cap; C8 n; C4 over] /\ wr_at rsegs m1 (bv_unsigned sp - 4) 4.

Lemma sbd_tail : forall m1 (t0 t1 t2 a1 a2 a4 a5 a6 a7 t3 t4 t5 : word),
  sbd_inv m1 ->
  bytes_at rsegs m1 (bv_unsigned sp - 4) (map (Z_to_bv 8) (rev (sb_dec_D v md))) ->
  evt rsegs sbd_post
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 b a1 a2
             (Z_to_bv 64 (Z.of_nat (length (sb_dec_D v md)))) a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14510) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 t0 t1 t2 a1 a2 a4 a5 a6 a7 t3 t4 t5 (MU & WM & MI & ST & FR & FW) HD.
  pose proof (zr_word sp) as Rsp. pose proof (zr_word b) as Rb. pose proof (zr_word p) as Rp.
  pose proof (zr_word n) as Rn. pose proof (zr_word cap) as Rc. unfold inr64 in *.
  pose proof (sbd_D_len v md ltac:(lia)) as LD.
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  assert (BF : 0 <= bv_unsigned sp - 4) by (destruct FW as (? & ? & _); lia).
  do 5 zstep.
  eapply evt_cut.
  { eapply (sbd_emit ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
              t3 t4 t5 t6 F fc b p cap lo (bv_unsigned sp) (sb_dec_D v md) m1 (bv_unsigned n) over).
    - intros E. rewrite E in LD. cbn [length] in LD. lia.
    - rewrite unsigned_lit_wrap. Z.div_mod_to_equations. lia.
    - rewrite unsigned_lit by lia.
      replace (Z.of_nat (length (sb_dec_D v md)) + (bv_unsigned sp + -4) + -1 + 1 - Z.of_nat (length (sb_dec_D v md)))
        with (bv_unsigned sp - 4) by lia.
      exact HD.
    - rewrite Z_to_bv_lit_self. exact FR.
    - lia.
    - lia.
    - rewrite unsigned_lit by lia. lia.
    - intros H0. destruct (HP H0) as (_ & PW & PD1 & PD2). unfold sb_dec_acc in *.
      rewrite unsigned_lit by lia. split; [|split].
      + eapply wr_at_transport; [exact PW | exact WM].
      + lia.
      + lia.
    - exact MI.
    - exact ST. }
  intros ms' (a1' & a2' & a4' & a5' & a6' & a7' & m' & E & MU' & WM' & MI' & ST' & HB' & HP').
  subst ms'. unfold sbd_at.
  zstep. zstep.
  apply evt_done. unfold sbd_post.
  exists t0, t1, t2, b, a1', a2', (Z_to_bv 64 1), a4', a5', a6', a7', t3, t4, t5, t6, m'.
  split; [reflexivity|].
  split.
  { apply (munch_trans _ m m1 m'); [exact MU|].
    eapply munch_weaken; [|exact MU']. intros x Hx. cbn [outside] in *. unfold sb_dec_acc in *. lia. }
  split; [exact (wmono_trans _ _ _ _ WM WM')|].
  split; [exact MI'|]. split; [exact ST'|]. split; [exact HB'|]. exact HP'.
Qed.

Lemma sbd_D_eq : sb_dec_D v md =
  rev (if Z.of_nat (length (sb_dec_lsd v 3)) <? md then sb_dec_lsd v 3 ++ [48] else sb_dec_lsd v 3).
Proof. reflexivity. Qed.

Lemma sbd_after : forall m1 (a1 t2 t3 t4 t5 : word),
  sbd_inv m1 ->
  bytes_at rsegs m1 (bv_unsigned sp - 4) (map (Z_to_bv 8) (sb_dec_lsd v 3)) ->
  evt rsegs sbd_post
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp (Z_to_bv 64 1717986919) (Z_to_bv 64 2) t2 s0 s1 b a1
             (Z_to_bv 64 md)
             (Z_to_bv 64 (Z.of_nat (length (sb_dec_lsd v 3)))) (Z_to_bv 64 (Z.of_nat (length (sb_dec_lsd v 3))))
             (Z_to_bv 64 10) (Z_to_bv 64 (bv_unsigned sp + -4)) (Z_to_bv 64 (-20))
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x144f8) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 a1 t2 t3 t4 t5 (MU & WM & MI & ST & FR & FW) HD.
  pose proof (zr_word sp) as Rsp. pose proof (zr_word b) as Rb. unfold inr64 in *.
  pose proof (sbd_lsd_len v) as LK.
  assert (BF : 0 <= bv_unsigned sp - 4) by (destruct FW as (? & ? & _); lia).
  assert (LDM : Z.of_nat (length (map (Z_to_bv 8) (sb_dec_lsd v 3))) = Z.of_nat (length (sb_dec_lsd v 3)))
    by (rewrite length_map; reflexivity).
  zstep.
  rewrite bv_ltu_Z, !unsigned_lit by lia.
  destruct (Z.ltb_spec (Z.of_nat (length (sb_dec_lsd v 3))) md) as [KL|KG]; cbn [negb].
  - zstep. zstep. zstep. zstep.
    pose proof (wr_at_store_ok rsegs m1 (bv_unsigned sp - 4) 4 (Z.of_nat (length (sb_dec_lsd v 3))) 1 FW
                  ltac:(lia) ltac:(lia)) as HS.
    zstep.
    rewrite sbd_le1 by lia. sbd_store.
    replace (Z_to_bv 64 (Z.of_nat (length (sb_dec_lsd v 3)) + 1)) with (Z_to_bv 64 (Z.of_nat (length (sb_dec_D v md)))).
    2: { f_equal. rewrite sbd_D_eq, (proj2 (Z.ltb_lt _ _) KL), length_rev, length_app. cbn [length]. lia. }
    eapply sbd_tail.
    + exact (conj MU (conj WM (conj MI (conj ST (conj FR FW))))).
    + rewrite sbd_D_eq, (proj2 (Z.ltb_lt _ _) KL), rev_involutive, map_app.
      apply bytes_at_app. split; [exact HD|]. rewrite LDM. exact HW.
  - replace (Z_to_bv 64 (Z.of_nat (length (sb_dec_lsd v 3)))) with (Z_to_bv 64 (Z.of_nat (length (sb_dec_D v md)))).
    2: { f_equal. rewrite sbd_D_eq, (proj2 (Z.ltb_ge _ _) KG), length_rev. reflexivity. }
    eapply sbd_tail.
    + exact (conj MU (conj WM (conj MI (conj ST (conj FR FW))))).
    + rewrite sbd_D_eq, (proj2 (Z.ltb_ge _ _) KG), rev_involutive. exact HD.
Qed.

Lemma sbd_dl : forall (j : nat) (i x : Z) (P : list Z) m1 (t2 t3 t4 t5 : word),
  (1 <= j)%nat -> i + Z.of_nat j = 3 -> Z.of_nat (length P) = i ->
  P ++ sb_dec_lsd x j = sb_dec_lsd v 3 -> 0 <= x < 2^31 ->
  sbd_inv m1 -> bytes_at rsegs m1 (bv_unsigned sp - 4) (map (Z_to_bv 8) P) ->
  evt rsegs sbd_post
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp (Z_to_bv 64 1717986919) (Z_to_bv 64 2) t2 s0 s1 b
             (Z_to_bv 64 x) (Z_to_bv 64 md)
             (Z_to_bv 64 i) (Z_to_bv 64 i) (Z_to_bv 64 10) (Z_to_bv 64 (bv_unsigned sp + -4)) (Z_to_bv 64 (-20))
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x144b8) fc None m1 (seg_rom rsegs)).
Proof.
  induction j as [|j IH]; intros i x P m1 t2 t3 t4 t5 J1 IJ LP HPfx HX INV HD; [lia|].
  destruct INV as (MU & WM & MI & ST & FR & FW).
  pose proof (zr_word sp) as Rsp. pose proof (zr_word b) as Rb. unfold inr64 in *.
  assert (BF : 0 <= bv_unsigned sp - 4) by (destruct FW as (? & ? & _); lia).
  assert (LPM : Z.of_nat (length (map (Z_to_bv 8) P)) = i) by (rewrite length_map; exact LP).
  pose proof (Z.mod_pos_bound x 10 ltac:(lia)) as XM.
  rewrite (sbd_lsd_S x j) in HPfx.
  do 12 zstep.
  rewrite (sbd_q x HX), (sbd_r x HX), (sbd_swrap (x + -10)) by lia.
  pose proof (wr_at_store_ok rsegs m1 (bv_unsigned sp - 4) 4 i 1 FW ltac:(lia) ltac:(lia)) as HS.
  zstep.
  rewrite sbd_le1 by lia. sbd_store.
  zstep. rewrite (sbd_swrap (i + 1)) by lia.
  zstep. rewrite (sbd_lt10 x HX).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m2 _) =>
    assert (HD2 : bytes_at rsegs m2 (bv_unsigned sp - 4) (map (Z_to_bv 8) (P ++ [48 + x mod 10])))
  end.
  { rewrite map_app. apply bytes_at_app. split; [exact HD|]. rewrite LPM. cbn [map].
    replace (48 + x mod 10) with (x mod 10 + 48) by lia. exact HW. }
  destruct (Z.lt_ge_cases x 10) as [X10|X10].
  - if_true.
    rewrite (proj2 (Z.ltb_lt x 10) X10) in HPfx. cbv iota in HPfx.
    replace (Z_to_bv 64 (i + 1)) with (Z_to_bv 64 (Z.of_nat (length (sb_dec_lsd v 3)))).
    2: { rewrite <- HPfx, length_app. cbn [length]. f_equal. lia. }
    eapply sbd_after.
    + exact (conj MU (conj WM (conj MI (conj ST (conj FR FW))))).
    + rewrite <- HPfx. exact HD2.
  - if_false.
    rewrite (proj2 (Z.ltb_ge x 10) X10) in HPfx. cbv iota in HPfx.
    zstep. rewrite bv_ltu_Z, !unsigned_lit by lia.
    destruct (Z.lt_ge_cases i 2) as [I2|I2].
    + if_true.
      eapply (IH (i + 1) (x / 10) (P ++ [48 + x mod 10])).
      * lia.
      * lia.
      * rewrite length_app. cbn [length]. lia.
      * rewrite <- app_assoc. cbn [app]. exact HPfx.
      * split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
      * exact (conj MU (conj WM (conj MI (conj ST (conj FR FW))))).
      * exact HD2.
    + if_false.
      assert (J0 : j = O) by lia. subst j. change (sb_dec_lsd (x / 10) 0) with (@nil Z) in HPfx.
      replace (Z_to_bv 64 (i + 1)) with (Z_to_bv 64 (Z.of_nat (length (sb_dec_lsd v 3)))).
      2: { rewrite <- HPfx, length_app. cbn [length]. f_equal. lia. }
      eapply sbd_after.
      * exact (conj MU (conj WM (conj MI (conj ST (conj FR FW))))).
      * rewrite <- HPfx. exact HD2.
Qed.

End Main.

Theorem sb_dec_holds : sb_dec_contract.
Proof.
  unfold sb_dec_contract, SB_DEC, SB_DEC_K.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo v md
    p cap n over HV HA1 HMD HA2 HB HW HN HP MI ST LO DB.
  subst a1 a2.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  assert (FR : rw_cells rsegs m (bv_unsigned a0) [C8 p; C8 cap; C8 n; C4 over]).
  { split; [split; [cbn; tauto|] |].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
    - exact HW. }
  pose proof (sbd_stk_wr m lo (bv_unsigned sp) (bv_unsigned sp - 4) 4 ST ltac:(lia) ltac:(lia) ltac:(lia)) as FW.
  do 9 zstep.
  eapply sbd_dl with (j := 3%nat) (i := 0) (x := v) (P := []) (m1 := m).
  all: try assumption.
  - lia.
  - lia.
  - reflexivity.
  - reflexivity.
  - exact (conj (munch_refl _ _) (conj (wmono_refl _ _) (conj MI (conj ST (conj FR FW))))).
  - apply bytes_at_nil. lia.
Qed.
