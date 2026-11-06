From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import sb_ch_c sb_dec_c.
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


Lemma sbu_stk_tr : forall W m m' lo hi, stk rsegs m lo hi -> munch W m m' -> wmono rsegs m m' ->
  (forall x, lo <= x < hi -> outside W x \/ exists b0, mrd rsegs m' (wa x) = Some b0) -> stk rsegs m' lo hi.
Proof.
  intros W m m' lo hi (H1 & H2 & H) MU WM HC. split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as [Hw (b0 & Hb)]. split; [apply WM; exact Hw|].
  destruct (HC a Ha) as [Ho|E]; [|exact E].
  exists b0. unfold mrd in *. rewrite MU; [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
Qed.

Lemma sbu_bytes_mrd : forall m a bs x, bytes_at rsegs m a bs -> a <= x < a + Z.of_nat (length bs) ->
  exists b0, mrd rsegs m (wa x) = Some b0.
Proof.
  intros m a bs x (H1 & H2 & H) Hx.
  pose proof (H (Z.to_nat (x - a)) ltac:(lia)) as E.
  replace (a + Z.of_nat (Z.to_nat (x - a))) with x in E by lia.
  rewrite E. destruct (nth_error bs (Z.to_nat (x - a))) eqn:N; [eauto|].
  apply nth_error_None in N. lia.
Qed.

Lemma sbu_bne : forall e k, e = k - 1 -> 0 <= k < 2^64 -> bv_eqb (Z_to_bv 64 e) (Z_to_bv 64 (-1)) = (k =? 0).
Proof.
  intros e k -> Hk. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec k 0) as [->|NE]; [reflexivity|].
  apply Z.eqb_neq. Z.div_mod_to_equations. lia.
Qed.

Lemma sbu_rec_len : forall p cap n ov, Z.of_nat (length (sb_rec p cap n ov)) = 28.
Proof. intros. unfold sb_rec. rewrite !length_app, !length_le8, length_le4. reflexivity. Qed.

Section UEmit.
Variables (sp gp tp s1 s3 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (b p cap : word) (lo hi : Z).
Hypothesis SBCH : sb_ch_contract.
Hypothesis HAL : bv_unsigned b mod 8 = 0.
Hypothesis HS1 : bv_unsigned s1 = 2^64 - 1 - bv_unsigned s3.

Definition sbu_epost (R : list Z) (m : word -> option byte) (n : Z) (ov : word) (ms' : machine_state) : Prop :=
  exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra' sp gp tp t0' t1' t2' b s1 a0' a1' a2' a3' a4' a5' a6' a7' s2' s3 (Z_to_bv 64 (-1))
                  s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x14840) fc None m' (seg_rom rsegs) /\
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

Lemma sbu_epost_nil : forall m1 n ov (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' t3' t4' t5' t6' : word),
  0 <= n -> bytes_at rsegs m1 (bv_unsigned b) (sb_rec p cap (Z_to_bv 64 n) ov) ->
  mem_inv rsegs m1 -> stk rsegs m1 lo hi ->
  (0 < sb_dec_room (bv_unsigned cap) n -> 0 <= bv_unsigned p + n <= 2^64) ->
  sbu_epost [] m1 n ov
    (MS (mkR ra' sp gp tp t0' t1' t2' b s1 a0' a1' a2' a3' a4' a5' a6' a7' s2' s3 (Z_to_bv 64 (-1))
             s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x14840) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 n ov ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' t3' t4' t5' t6' N0 HB MI ST HPN.
  pose proof (sbd_room_nn (bv_unsigned cap) n) as RN.
  exists ra', t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', s2', t3', t4', t5', t6', m1.
  split; [reflexivity|].
  split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|]. split; [exact ST|]. split.
  - cbn [length]. replace (n + Z.min (Z.of_nat 0) (sb_dec_room (bv_unsigned cap) n)) with n by lia.
    replace (sb_dec_room (bv_unsigned cap) n <? Z.of_nat 0) with false by (symmetry; apply Z.ltb_ge; lia).
    exact HB.
  - intros H. replace (Z.to_nat (Z.min (Z.of_nat (length (@nil Z))) (sb_dec_room (bv_unsigned cap) n))) with O
      by (cbn [length]; lia).
    cbn [firstn map]. apply bytes_at_nil. apply HPN. exact H.
Qed.

Lemma sbu_tr_st : forall c R m m1 n ov ms',
  0 <= n -> n + 1 < bv_unsigned cap ->
  munch [(bv_unsigned b + 16, bv_unsigned b + 24); (bv_unsigned p + n, bv_unsigned p + n + 1)] m m1 ->
  wmono rsegs m m1 ->
  bytes_at rsegs m1 (bv_unsigned p + n) [Z_to_bv 8 c] ->
  (bv_unsigned p + n + Z.min (Z.of_nat (length R) + 1) (sb_dec_room (bv_unsigned cap) n) <= bv_unsigned b \/
   bv_unsigned b + 28 <= bv_unsigned p + n) ->
  sbu_epost R m1 (n + 1) ov ms' -> sbu_epost (c :: R) m n ov ms'.
Proof.
  intros c R m m1 n ov ms' N0 HC MU WM HBY DP
    (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & t3' & t4' & t5' & t6' & m' &
     E & MU' & WM' & MI' & ST' & HB' & HP').
  destruct (sbd_room_lt _ _ HC) as [RM RM1].
  assert (LEN : Z.of_nat (length (c :: R)) = Z.of_nat (length R) + 1) by (cbn [length]; lia).
  pose proof (bytes_at_bound _ _ _ _ HBY) as BY. cbn [length] in BY.
  exists ra', t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', s2', t3', t4', t5', t6', m'.
  split; [exact E|].
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

Lemma sbu_tr_ov : forall c R m m1 n ov ms',
  0 <= n -> bv_unsigned cap <= n + 1 ->
  munch [(bv_unsigned b + 24, bv_unsigned b + 28)] m m1 ->
  wmono rsegs m m1 ->
  sbu_epost R m1 n (Z_to_bv 64 1) ms' -> sbu_epost (c :: R) m n ov ms'.
Proof.
  intros c R m m1 n ov ms' N0 HC MU WM
    (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & t3' & t4' & t5' & t6' & m' &
     E & MU' & WM' & MI' & ST' & HB' & HP').
  pose proof (sbd_room_ge _ _ HC) as RM.
  assert (LEN : Z.of_nat (length (c :: R)) = Z.of_nat (length R) + 1) by (cbn [length]; lia).
  exists ra', t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', s2', t3', t4', t5', t6', m'.
  split; [exact E|].
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

Lemma sbu_emit : forall (R : list Z) (m : word -> option byte) (n : Z)
                        (ov ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  R <> [] ->
  bytes_at rsegs m (bv_unsigned s3) (map (Z_to_bv 8) (rev R)) ->
  bytes_at rsegs m (bv_unsigned b) (sb_rec p cap (Z_to_bv 64 n) ov) ->
  wr_at rsegs m (bv_unsigned b) 28 ->
  0 <= n -> n + Z.of_nat (length R) < 2^64 - 1 ->
  (bv_unsigned b + 28 <= bv_unsigned s3 \/ bv_unsigned s3 + Z.of_nat (length R) <= bv_unsigned b) ->
  (0 < sb_dec_room (bv_unsigned cap) n ->
     bv_unsigned p <> 0 /\
     wr_at rsegs m (bv_unsigned p + n) (Z.min (Z.of_nat (length R)) (sb_dec_room (bv_unsigned cap) n)) /\
     (bv_unsigned p + n + Z.min (Z.of_nat (length R)) (sb_dec_room (bv_unsigned cap) n) <= bv_unsigned b \/
      bv_unsigned b + 28 <= bv_unsigned p + n) /\
     (bv_unsigned p + n + Z.min (Z.of_nat (length R)) (sb_dec_room (bv_unsigned cap) n) <= bv_unsigned s3 \/
      bv_unsigned s3 + Z.of_nat (length R) <= bv_unsigned p + n)) ->
  mem_inv rsegs m -> stk rsegs m lo hi ->
  evt rsegs (sbu_epost R m n ov)
    (MS (mkR ra sp gp tp t0 t1 t2 b s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.of_nat (length R) - 1)) s3
             (Z_to_bv 64 (-1)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14824) fc None m (seg_rom rsegs)).
Proof.
  induction R as [|c R IH];
    intros m n ov ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 NE HD HB HW N0 NR DRD HP MI ST; [congruence|].
  clear NE.
  pose proof (zr_word b) as Rb. pose proof (zr_word p) as Rp. pose proof (zr_word cap) as Rc.
  pose proof (zr_word s3) as Rs3. unfold inr64 in *.
  assert (LEN : Z.of_nat (length (c :: R)) = Z.of_nat (length R) + 1) by (cbn [length]; lia).
  rewrite LEN in NR, DRD, HP.
  replace (Z.of_nat (length (c :: R)) - 1) with (Z.of_nat (length R)) by lia.
  assert (LHD : length (map (Z_to_bv 8) (rev R)) = length R) by (rewrite length_map, length_rev; reflexivity).
  pose proof (bytes_at_bound _ _ _ _ HB) as BB. rewrite sbu_rec_len in BB.
  cbn [rev] in HD. rewrite map_app in HD. cbn [map] in HD. apply bytes_at_app in HD. destruct HD as [HD HC].
  rewrite LHD in HC.
  pose proof (bytes_at_bound _ _ _ _ HC) as BC. cbn [length] in BC.
  assert (HR : ov_read_bytes rsegs m (wa (bv_unsigned s3 + Z.of_nat (length R) + 0)) 1 = Some [Z_to_bv 8 c])
    by (rewrite (bytes_at_read rsegs m _ _ 0 1 HC) by (cbn; lia); reflexivity).
  clear HC.
  zstep.
  rewrite bv_ltu_Z, HS1, (unsigned_lit (Z.of_nat (length R))) by lia. if_false.
  zstep. zstep. zstep. zstep.
  eapply evt_cut.
  { eapply SBCH with (p := p) (cap := cap) (n := Z_to_bv 64 n) (over := ov).
    - exact HAL.
    - exact HB.
    - exact HW.
    - rewrite unsigned_lit by lia. lia.
    - rewrite unsigned_lit by lia. intros HC. destruct (sbd_room_lt _ _ HC) as [RM RM1].
      destruct (HP ltac:(lia)) as (P0 & PW & PD1 & PD2).
      pose proof PW as (PW1 & PW2 & _).
      split; [exact P0|]. split; [lia|]. split.
      + eapply sbd_wr_sub; [exact PW | lia | lia | lia].
      + lia.
    - exact MI. }
  intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & WM' & MI' & POST).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x14838)) with (Z_to_bv 64 0x14838) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  rewrite (unsigned_lit n) in POST by lia.
  apply (wr_at_transport rsegs m m') in HW; [|exact WM'].
  destruct POST as [(HC & MU' & HB') | (HC & MU' & HB' & HBY)].
  - pose proof (sbd_room_ge _ _ HC) as RM.
    eapply bytes_at_transport in HD; [|exact MU' | cbn [disjoint_from]; rewrite LHD; repeat split; lia].
    assert (ST2 : stk rsegs m' lo hi).
    { apply (sbu_stk_tr _ m m' lo hi ST MU' WM'). intros x Hx. cbn [outside].
         destruct (Z_lt_le_dec x (bv_unsigned b + 24)); [left; split; [lia|exact I]|].
         destruct (Z_lt_le_dec x (bv_unsigned b + 28)); [right|left; split; [lia|exact I]].
         apply (sbu_bytes_mrd _ _ _ _ HB'). rewrite sbu_rec_len. lia. }
    clear ST. rename ST2 into ST.
    zstep.
    apply (evt_mono rsegs (sbu_epost R m' n (Z_to_bv 64 1)));
      [| intros ms'' PO; exact (sbu_tr_ov c R m m' n ov ms'' N0 HC MU' WM' PO)].
    destruct R as [|c' R'].
    + zstep. rewrite (sbu_bne _ 0) by (cbn [length]; lia). if_false.
      apply evt_done. eapply sbu_epost_nil; [lia | exact HB' | exact MI' | exact ST | intros H0; rewrite RM in H0; lia].
    + assert (LEN2 : Z.of_nat (length (c' :: R')) = Z.of_nat (length R') + 1) by (cbn [length]; lia).
      zstep. rewrite (sbu_bne _ (Z.of_nat (length (c' :: R')))) by lia. if_true.
      replace (Z.of_nat (length (c' :: R')) + -1) with (Z.of_nat (length (c' :: R')) - 1) by lia.
      eapply IH.
      * discriminate.
      * exact HD.
      * exact HB'.
      * exact HW.
      * lia.
      * lia.
      * lia.
      * intros H0. rewrite RM in H0. lia.
      * exact MI'.
      * exact ST.
  - destruct (sbd_room_lt _ _ HC) as [RM RM1].
    destruct (HP ltac:(lia)) as (P0 & PW & PD1 & PD2). clear HP.
    pose proof PW as (PW1 & PW2 & _).
    rewrite sbd_le1b in HBY.
    eapply bytes_at_transport in HD; [|exact MU' | cbn [disjoint_from]; rewrite LHD; repeat split; lia].
    apply (wr_at_transport rsegs m m') in PW; [|exact WM'].
    assert (ST2 : stk rsegs m' lo hi).
    { apply (sbu_stk_tr _ m m' lo hi ST MU' WM'). intros x Hx. cbn [outside].
         destruct (Z_lt_le_dec x (bv_unsigned b + 16)).
         { destruct (Z_lt_le_dec x (bv_unsigned p + n)); [left; split; [lia|split; [lia|exact I]]|].
           destruct (Z_lt_le_dec x (bv_unsigned p + n + 1)); [right|left; split; [lia|split; [lia|exact I]]].
           apply (sbu_bytes_mrd _ _ _ _ HBY). cbn [length]. lia. }
         destruct (Z_lt_le_dec x (bv_unsigned b + 24)); [right; apply (sbu_bytes_mrd _ _ _ _ HB'); rewrite sbu_rec_len; lia|].
         destruct (Z_lt_le_dec x (bv_unsigned p + n)); [left; split; [lia|split; [lia|exact I]]|].
         destruct (Z_lt_le_dec x (bv_unsigned p + n + 1)); [right|left; split; [lia|split; [lia|exact I]]].
         apply (sbu_bytes_mrd _ _ _ _ HBY). cbn [length]. lia. }
    clear ST. rename ST2 into ST.
    zstep.
    apply (evt_mono rsegs (sbu_epost R m' (n + 1) ov));
      [| intros ms'' PO; exact (sbu_tr_st c R m m' n ov ms'' N0 HC MU' WM' HBY PD1 PO)].
    destruct R as [|c' R'].
    + zstep. rewrite (sbu_bne _ 0) by (cbn [length]; lia). if_false.
      apply evt_done. eapply sbu_epost_nil; [lia | exact HB' | exact MI' | exact ST | intros; lia].
    + assert (LEN2 : Z.of_nat (length (c' :: R')) = Z.of_nat (length R') + 1) by (cbn [length]; lia).
      zstep. rewrite (sbu_bne _ (Z.of_nat (length (c' :: R')))) by lia. if_true.
      replace (Z.of_nat (length (c' :: R')) + -1) with (Z.of_nat (length (c' :: R')) - 1) by lia.
      eapply IH.
      * discriminate.
      * exact HD.
      * exact HB'.
      * exact HW.
      * lia.
      * lia.
      * lia.
      * intros H0. split; [exact P0|]. split; [|split].
        -- eapply sbd_wr_sub; [exact PW | lia | lia | lia].
        -- lia.
        -- lia.
      * exact MI'.
      * exact ST.
Qed.

End UEmit.

Lemma sbu_neq_m1 : forall z, 0 <= z < 2^64 - 1 -> bv_eqb (Z_to_bv 64 z) (Z_to_bv 64 (-1)) = false.
Proof.
  intros z Hz. unfold bv_eqb. rewrite (unsigned_lit z) by lia. rewrite unsigned_lit_wrap.
  apply Z.eqb_neq. Z.div_mod_to_equations. lia.
Qed.

Lemma sbu_not : forall x, 0 <= x < 2^64 ->
  bv_unsigned (Z_to_bv 64 (Z.lxor x 18446744073709551615)) = 2^64 - 1 - bv_unsigned (Z_to_bv 64 x).
Proof. intros x Hx. rewrite zb_lxor_ones by lia. rewrite !unsigned_lit by lia. lia. Qed.

Section Main.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m : word -> option byte) (lo v md : Z) (b p cap n over : word).
Hypothesis SBCH : sb_ch_contract.
Hypothesis HV : 0 <= v < 2^31.
Hypothesis HMD : md = 1 \/ md = 2.
Hypothesis HAL : bv_unsigned b mod 8 = 0.
Hypothesis HN : bv_unsigned n + 1 < 2^64 - 3.
Hypothesis HP : 0 < sb_dec_room (bv_unsigned cap) (bv_unsigned n) ->
  bv_unsigned p <> 0 /\
  bv_unsigned p + bv_unsigned cap <= 2^64 /\
  wr_at rsegs m (bv_unsigned p + bv_unsigned n) (sb_dec_acc v md (bv_unsigned cap) (bv_unsigned n)) /\
  (bv_unsigned p + bv_unsigned n + sb_dec_acc v md (bv_unsigned cap) (bv_unsigned n) <= bv_unsigned b \/
   bv_unsigned b + 28 <= bv_unsigned p + bv_unsigned n) /\
  (bv_unsigned p + bv_unsigned n + sb_dec_acc v md (bv_unsigned cap) (bv_unsigned n) <= bv_unsigned sp - 64 \/
   bv_unsigned sp <= bv_unsigned p + bv_unsigned n).
Hypothesis DB : bv_unsigned b + 28 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= bv_unsigned b.

Definition sbu_post (ms' : machine_state) : Prop :=
  exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp - 64, bv_unsigned sp); (bv_unsigned b + 16, bv_unsigned b + 28);
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

Definition sbu_inv (m1 : word -> option byte) : Prop :=
  munch [(bv_unsigned sp - 64, bv_unsigned sp); (bv_unsigned b + 16, bv_unsigned b + 28);
         (bv_unsigned p + bv_unsigned n,
          bv_unsigned p + bv_unsigned n + sb_dec_acc v md (bv_unsigned cap) (bv_unsigned n))] m m1 /\
  wmono rsegs m m1 /\ mem_inv rsegs m1 /\ stk rsegs m1 lo (bv_unsigned sp) /\
  rw_cells rsegs m1 (bv_unsigned b) [C8 p; C8 cap; C8 n; C4 over] /\ wr_at rsegs m1 (bv_unsigned sp - 52) 4 /\
  rw_cells rsegs m1 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma sbu_tail : forall m1 (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  sbu_inv m1 ->
  bytes_at rsegs m1 (bv_unsigned sp - 52) (map (Z_to_bv 8) (rev (sb_dec_D v md))) ->
  evt rsegs sbu_post
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 b
             (Z_to_bv 64 (Z.lxor (bv_unsigned sp + -52) 18446744073709551615))
             (Z_to_bv 64 (Z.of_nat (length (sb_dec_D v md)))) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14818) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (MU & WM & MI & ST & FR & FW & FRr) HD.
  pose proof (zr_word sp) as Rsp. pose proof (zr_word b) as Rb. pose proof (zr_word p) as Rp.
  pose proof (zr_word n) as Rn. pose proof (zr_word cap) as Rc. unfold inr64 in *.
  pose proof (sbd_D_len v md ltac:(lia)) as LD.
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  assert (BF : 0 <= bv_unsigned sp - 52) by (destruct FW as (? & ? & _); lia).
  destruct FR as [[_ HB] HW]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
  change (Z.of_nat (cells_size [C8 p; C8 cap; C8 n; C4 over])) with 28 in HW.
  do 3 zstep.
  replace (Z.of_nat (length (sb_dec_D v md)) + -1) with (Z.of_nat (length (sb_dec_D v md)) - 1) by lia.
  assert (HS1 : bv_unsigned (Z_to_bv 64 (Z.lxor (bv_unsigned sp + -52) 18446744073709551615)) =
                2^64 - 1 - bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -52))) by (apply sbu_not; lia).
  eapply evt_cut.
  { eapply (sbu_emit (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp
              (Z_to_bv 64 (Z.lxor (bv_unsigned sp + -52) 18446744073709551615)) (Z_to_bv 64 (bv_unsigned sp + -52))
              s5 s6 s7 s8 s9 s10 s11 F fc b p cap lo (bv_unsigned sp) SBCH HAL HS1 (sb_dec_D v md) m1 (bv_unsigned n) over).
    - intros E. rewrite E in LD. cbn [length] in LD. lia.
    - rewrite unsigned_lit by lia. replace (bv_unsigned sp + -52) with (bv_unsigned sp - 52) by lia. exact HD.
    - rewrite Z_to_bv_lit_self. exact HB.
    - exact HW.
    - lia.
    - lia.
    - rewrite unsigned_lit by lia. lia.
    - intros H0. destruct (HP H0) as (P0 & _ & PW & PD1 & PD2). unfold sb_dec_acc in *.
      rewrite unsigned_lit by lia. split; [exact P0|]. split; [|split].
      + eapply wr_at_transport; [exact PW | exact WM].
      + lia.
      + lia.
    - exact MI.
    - exact ST. }
  intros ms' (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & t3' & t4' & t5' & t6' & m' &
              E & MU' & WM' & MI' & ST' & HB' & HP').
  subst ms'.
  assert (FR2 : rw_cells rsegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { destruct (Z.ltb_spec 0 (sb_dec_room (bv_unsigned cap) (bv_unsigned n))) as [Hr|Hr].
    - destruct (HP Hr) as (_ & _ & _ & _ & PD2). unfold sb_dec_acc in *.
      eapply rw_cells_transport; [exact FRr | exact MU' | exact WM' |].
      cbn [disjoint_from cells_size csize Nat.add]. repeat split; lia.
    - pose proof (sbd_room_nn (bv_unsigned cap) (bv_unsigned n)) as RN.
      assert (MU2 : munch [(bv_unsigned b + 16, bv_unsigned b + 28)] m1 m').
      { eapply munch_weaken; [|exact MU']. intros x Hx. cbn [outside] in *. lia. }
      eapply rw_cells_transport; [exact FRr | exact MU2 | exact WM' |].
      cbn [disjoint_from cells_size csize Nat.add]. repeat split; lia. }
  clear FRr.
  do 8 zstep.
  apply evt_done. unfold sbu_post.
  exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [reflexivity|].
  split.
  { apply (munch_trans _ m m1 m'); [exact MU|].
    eapply munch_weaken; [|exact MU']. intros x Hx. cbn [outside] in *. unfold sb_dec_acc in *. lia. }
  split; [exact (wmono_trans _ _ _ _ WM WM')|].
  split; [exact MI'|]. split; [exact ST'|]. split; [exact HB'|]. exact HP'.
Qed.

Lemma sbu_D_eq : sb_dec_D v md =
  rev (if Z.of_nat (length (sb_dec_lsd v 3)) <? md then sb_dec_lsd v 3 ++ [48] else sb_dec_lsd v 3).
Proof. reflexivity. Qed.

Lemma sbu_after : forall m1 (t1 t2 a1 t3 t4 t5 t6 : word),
  sbu_inv m1 ->
  bytes_at rsegs m1 (bv_unsigned sp - 52) (map (Z_to_bv 8) (sb_dec_lsd v 3)) ->
  evt rsegs sbu_post
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp (Z_to_bv 64 2) t1 t2 b
             (Z_to_bv 64 (Z.lxor (bv_unsigned sp + -52) 18446744073709551615))
             (Z_to_bv 64 (Z.of_nat (length (sb_dec_lsd v 3)))) a1 (Z_to_bv 64 md)
             (Z_to_bv 64 (Z.of_nat (length (sb_dec_lsd v 3)))) (Z_to_bv 64 (bv_unsigned sp + -52))
             (Z_to_bv 64 10) (Z_to_bv 64 (-20)) (Z_to_bv 64 1717986919)
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x147fc) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 t1 t2 a1 t3 t4 t5 t6 (MU & WM & MI & ST & FR & FW & FRr) HD.
  pose proof (zr_word sp) as Rsp. pose proof (zr_word b) as Rb. unfold inr64 in *.
  pose proof (sbd_lsd_len v) as LK.
  assert (BF : 0 <= bv_unsigned sp - 52) by (destruct FW as (? & ? & _); lia).
  assert (LDM : Z.of_nat (length (map (Z_to_bv 8) (sb_dec_lsd v 3))) = Z.of_nat (length (sb_dec_lsd v 3)))
    by (rewrite length_map; reflexivity).
  zstep.
  rewrite bv_ltu_Z, !unsigned_lit by lia.
  destruct (Z.ltb_spec (Z.of_nat (length (sb_dec_lsd v 3))) md) as [KL|KG]; cbn [negb].
  - assert (K1 : Z.of_nat (length (sb_dec_lsd v 3)) = 1) by lia.
    zstep. zstep. zstep.
    rewrite sbu_neq_m1 by lia. cbv iota.
    zstep.
    pose proof (wr_at_store_ok rsegs m1 (bv_unsigned sp - 52) 4 1 1 FW ltac:(lia) ltac:(lia)) as HS.
    zstep.
    rewrite sbd_le1 by lia. sbd_store.
    zstep.
    replace (Z_to_bv 64 2) with (Z_to_bv 64 (Z.of_nat (length (sb_dec_D v md)))).
    2: { f_equal. rewrite sbu_D_eq, (proj2 (Z.ltb_lt _ _) KL), length_rev, length_app. cbn [length]. lia. }
    eapply sbu_tail.
    + exact (conj MU (conj WM (conj MI (conj ST (conj FR (conj FW FRr)))))).
    + rewrite sbu_D_eq, (proj2 (Z.ltb_lt _ _) KL), rev_involutive, map_app.
      apply bytes_at_app. split; [exact HD|]. rewrite LDM, K1. exact HW.
  - replace (Z_to_bv 64 (Z.of_nat (length (sb_dec_lsd v 3)))) with (Z_to_bv 64 (Z.of_nat (length (sb_dec_D v md)))).
    2: { f_equal. rewrite sbu_D_eq, (proj2 (Z.ltb_ge _ _) KG), length_rev. reflexivity. }
    eapply sbu_tail.
    + exact (conj MU (conj WM (conj MI (conj ST (conj FR (conj FW FRr)))))).
    + rewrite sbu_D_eq, (proj2 (Z.ltb_ge _ _) KG), rev_involutive. exact HD.
Qed.

Lemma sbu_dl : forall (j : nat) (i x : Z) (P : list Z) m1 (t1 t2 t3 t4 t5 t6 : word),
  (1 <= j)%nat -> i + Z.of_nat j = 3 -> Z.of_nat (length P) = i ->
  P ++ sb_dec_lsd x j = sb_dec_lsd v 3 -> 0 <= x < 2^31 ->
  sbu_inv m1 -> bytes_at rsegs m1 (bv_unsigned sp - 52) (map (Z_to_bv 8) P) ->
  evt rsegs sbu_post
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp (Z_to_bv 64 2) t1 t2 b
             (Z_to_bv 64 (Z.lxor (bv_unsigned sp + -52) 18446744073709551615))
             (Z_to_bv 64 i) (Z_to_bv 64 x) (Z_to_bv 64 md) (Z_to_bv 64 i) (Z_to_bv 64 (bv_unsigned sp + -52))
             (Z_to_bv 64 10) (Z_to_bv 64 (-20)) (Z_to_bv 64 1717986919)
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x147bc) fc None m1 (seg_rom rsegs)).
Proof.
  induction j as [|j IH]; intros i x P m1 t1 t2 t3 t4 t5 t6 J1 IJ LP HPfx HX INV HD; [lia|].
  destruct INV as (MU & WM & MI & ST & FR & FW & FRr).
  pose proof (zr_word sp) as Rsp. pose proof (zr_word b) as Rb. unfold inr64 in *.
  assert (BF : 0 <= bv_unsigned sp - 52) by (destruct FW as (? & ? & _); lia).
  assert (LPM : Z.of_nat (length (map (Z_to_bv 8) P)) = i) by (rewrite length_map; exact LP).
  pose proof (Z.mod_pos_bound x 10 ltac:(lia)) as XM.
  rewrite (sbd_lsd_S x j) in HPfx.
  do 12 zstep.
  rewrite (sbd_q x HX), (sbd_r x HX), (sbd_swrap (x + -10)) by lia.
  pose proof (wr_at_store_ok rsegs m1 (bv_unsigned sp - 52) 4 i 1 FW ltac:(lia) ltac:(lia)) as HS.
  zstep.
  rewrite sbd_le1 by lia. sbd_store.
  zstep. rewrite (sbd_swrap (i + 1)) by lia.
  zstep. rewrite (sbd_lt10 x HX).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m2 _) =>
    assert (HD2 : bytes_at rsegs m2 (bv_unsigned sp - 52) (map (Z_to_bv 8) (P ++ [48 + x mod 10])))
  end.
  { rewrite map_app. apply bytes_at_app. split; [exact HD|]. rewrite LPM. cbn [map].
    replace (48 + x mod 10) with (x mod 10 + 48) by lia. exact HW. }
  destruct (Z.lt_ge_cases x 10) as [X10|X10].
  - if_true.
    rewrite (proj2 (Z.ltb_lt x 10) X10) in HPfx. cbv iota in HPfx.
    replace (Z_to_bv 64 (i + 1)) with (Z_to_bv 64 (Z.of_nat (length (sb_dec_lsd v 3)))).
    2: { rewrite <- HPfx, length_app. cbn [length]. f_equal. lia. }
    eapply sbu_after.
    + exact (conj MU (conj WM (conj MI (conj ST (conj FR (conj FW FRr)))))).
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
      * exact (conj MU (conj WM (conj MI (conj ST (conj FR (conj FW FRr)))))).
      * exact HD2.
    + if_false.
      assert (J0 : j = O) by lia. subst j. change (sb_dec_lsd (x / 10) 0) with (@nil Z) in HPfx.
      replace (Z_to_bv 64 (i + 1)) with (Z_to_bv 64 (Z.of_nat (length (sb_dec_lsd v 3)))).
      2: { rewrite <- HPfx, length_app. cbn [length]. f_equal. lia. }
      eapply sbu_after.
      * exact (conj MU (conj WM (conj MI (conj ST (conj FR (conj FW FRr)))))).
      * rewrite <- HPfx. exact HD2.
Qed.

End Main.

Theorem sb_dec_holds : sb_ch_contract -> sb_dec_contract.
Proof.
  intros SBCH. unfold sb_dec_contract, SB_DEC, SB_DEC_K.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo v md
    p cap n over HV HA1 HMD HA2 HB HW HAL HN HP MI ST LO DB.
  subst a1 a2.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  assert (FR : rw_cells rsegs m (bv_unsigned a0) [C8 p; C8 cap; C8 n; C4 over]).
  { split; [split; [cbn; tauto|] |].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
    - exact HW. }
  clear HB HW.
  destruct (stk_carve rsegs m lo (bv_unsigned sp) 48 ST ltac:(lia)) as [_ [junk FRr]].
  change (Z.of_nat 48) with 48 in FRr. replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) in FRr by lia.
  pose proof (sbd_stk_wr m lo (bv_unsigned sp) (bv_unsigned sp - 52) 4 ST ltac:(lia) ltac:(lia) ltac:(lia)) as FW.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (bv_unsigned a0 + 16, bv_unsigned a0 + 28);
           (bv_unsigned p + bv_unsigned n,
            bv_unsigned p + bv_unsigned n + sb_dec_acc v md (bv_unsigned cap) (bv_unsigned n))] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 17 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply sbu_dl with (j := 3%nat) (i := 0) (x := v) (P := []) (m1 := mm) end.
  all: try assumption.
  - lia.
  - lia.
  - reflexivity.
  - reflexivity.
  - exact (conj MU (conj WM (conj MI (conj ST (conj FR (conj FW FRr)))))).
  - apply bytes_at_nil. lia.
Qed.
