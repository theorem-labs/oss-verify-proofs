From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_table_c disco_table bcmp_c find_entry_c check_table_c reac_disco_table_observe_c slot_lib slot_frame.
Import ListNotations.
Open Scope Z_scope.

Lemma ne_firstn : forall {A} n (l : list A) i, nth_error (firstn n l) i = if (i <? n)%nat then nth_error l i else None.
Proof.
  intros A n. induction n as [|n IH]; intros l i; [destruct i; reflexivity|].
  destruct l as [|x l]; destruct i as [|i]; cbn [firstn nth_error];
    [reflexivity | destruct (S i <? S n)%nat; reflexivity | reflexivity | rewrite IH; reflexivity].
Qed.

Lemma ne_sub : forall (bs : list byte) k n i, 0 <= k ->
  nth_error (sub bs k n) i = if (i <? n)%nat then nth_error bs (Z.to_nat k + i) else None.
Proof. intros bs k n i Hk. unfold sub. rewrite ne_firstn. destruct (i <? n)%nat; [apply nth_skipn | reflexivity]. Qed.

Lemma ne_upd : forall (bs v : list byte) k i, 0 <= k -> (Z.to_nat k + length v <= length bs)%nat ->
  nth_error (upd bs k v) i =
  if ((Z.to_nat k <=? i) && (i <? Z.to_nat k + length v))%nat then nth_error v (i - Z.to_nat k) else nth_error bs i.
Proof.
  intros bs v k i Hk Hl. unfold upd, upd_bytes. set (K := Z.to_nat k) in *.
  destruct (Nat.ltb_spec i K).
  - rewrite nth_error_app1 by (rewrite length_firstn; lia). rewrite ne_firstn.
    replace (i <? K)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
    replace (K <=? i)%nat with false by (symmetry; apply Nat.leb_gt; lia). reflexivity.
  - rewrite nth_error_app2 by (rewrite length_firstn; lia). rewrite length_firstn, Nat.min_l by lia.
    replace (K <=? i)%nat with true by (symmetry; apply Nat.leb_le; lia). cbn [andb].
    destruct (Nat.ltb_spec i (K + length v)).
    + rewrite nth_error_app1 by lia. reflexivity.
    + rewrite nth_error_app2 by lia. rewrite nth_skipn. f_equal. lia.
Qed.

Lemma length_upd : forall (bs v : list byte) k, 0 <= k -> k + Z.of_nat (length v) <= Z.of_nat (length bs) ->
  length (upd bs k v) = length bs.
Proof. intros bs v k Hk H. unfold upd. apply upd_bytes_length. lia. Qed.

Lemma len_ite : forall (c : bool) (bs v : list byte) k, 0 <= k -> k + Z.of_nat (length v) <= Z.of_nat (length bs) ->
  length (if c then upd bs k v else bs) = length bs.
Proof. intros [|] bs v k Hk H; [apply length_upd; assumption | reflexivity]. Qed.

Lemma sub_upd_out : forall (bs v : list byte) k k' n, 0 <= k -> 0 <= k' ->
  (k' + Z.of_nat n <= k \/ k + Z.of_nat (length v) <= k') -> k + Z.of_nat (length v) <= Z.of_nat (length bs) ->
  sub (upd bs k v) k' n = sub bs k' n.
Proof.
  intros bs v k k' n Hk Hk' Hd Hl. apply nth_error_ext. intros i. rewrite !ne_sub by lia.
  destruct (Nat.ltb_spec i n); [|reflexivity].
  rewrite ne_upd by lia.
  replace ((Z.to_nat k <=? Z.to_nat k' + i) && (Z.to_nat k' + i <? Z.to_nat k + length v))%nat with false;
    [reflexivity|].
  symmetry. apply andb_false_iff. destruct Hd; [left; apply Nat.leb_gt | right; apply Nat.ltb_ge]; lia.
Qed.

Lemma sub_upd_d : forall (bs v : list byte) k d n, 0 <= k -> 0 <= d -> d + Z.of_nat n <= Z.of_nat (length v) ->
  k + Z.of_nat (length v) <= Z.of_nat (length bs) ->
  sub (upd bs k v) (k + d) n = sub v d n.
Proof.
  intros bs v k d n Hk Hd Hn Hl. apply nth_error_ext. intros i. rewrite !ne_sub by lia.
  destruct (Nat.ltb_spec i n); [|reflexivity].
  rewrite ne_upd by lia.
  replace ((Z.to_nat k <=? Z.to_nat (k + d) + i) && (Z.to_nat (k + d) + i <? Z.to_nat k + length v))%nat with true.
  - f_equal. lia.
  - symmetry. apply andb_true_iff. split; [apply Nat.leb_le | apply Nat.ltb_lt]; lia.
Qed.

Lemma sub_all : forall (v : list byte) n, length v = n -> sub v 0 n = v.
Proof. intros v n H. unfold sub. cbn [Z.to_nat skipn]. apply firstn_all2. lia. Qed.

Lemma sub_upd_eq : forall (bs v : list byte) k n, 0 <= k -> length v = n ->
  k + Z.of_nat (length v) <= Z.of_nat (length bs) ->
  sub (upd bs k v) k n = v.
Proof.
  intros bs v k n Hk Hn Hl. rewrite <- (Z.add_0_r k) at 2. rewrite sub_upd_d by lia. apply sub_all. exact Hn.
Qed.

Lemma sub_ite_out : forall (c : bool) (bs v : list byte) k k' n, 0 <= k -> 0 <= k' ->
  (k' + Z.of_nat n <= k \/ k + Z.of_nat (length v) <= k') -> k + Z.of_nat (length v) <= Z.of_nat (length bs) ->
  sub (if c then upd bs k v else bs) k' n = sub bs k' n.
Proof. intros [|] bs v k k' n Hk Hk' Hd Hl; [apply sub_upd_out; assumption | reflexivity]. Qed.

Lemma sub_ite_eq : forall (c : bool) (bs v : list byte) k n, 0 <= k -> length v = n ->
  k + Z.of_nat (length v) <= Z.of_nat (length bs) ->
  sub (if c then upd bs k v else bs) k n = if c then v else sub bs k n.
Proof. intros [|] bs v k n Hk Hn Hl; [apply sub_upd_eq; assumption | reflexivity]. Qed.

Lemma len_ite3 : forall (c : bool) (bs v1 v2 v3 : list byte) k1 k2 k3, 0 <= k1 -> k2 = k1 + 1 -> k3 = k1 + 2 ->
  length v1 = 1%nat -> length v2 = 1%nat -> length v3 = 1%nat -> k1 + 3 <= Z.of_nat (length bs) ->
  length (if c then upd (upd (upd bs k1 v1) k2 v2) k3 v3 else bs) = length bs.
Proof.
  intros [|] bs v1 v2 v3 k1 k2 k3 Hk E2 E3 L1 L2 L3 Hl; [|reflexivity].
  assert (A1 : length (upd bs k1 v1) = length bs) by (apply length_upd; lia).
  assert (A2 : length (upd (upd bs k1 v1) k2 v2) = length bs) by (rewrite length_upd; lia).
  rewrite length_upd; lia.
Qed.

Lemma sub_ite3_out : forall (c : bool) (bs v1 v2 v3 : list byte) k1 k2 k3 k' n, 0 <= k1 -> k2 = k1 + 1 -> k3 = k1 + 2 ->
  length v1 = 1%nat -> length v2 = 1%nat -> length v3 = 1%nat -> k1 + 3 <= Z.of_nat (length bs) -> 0 <= k' ->
  (k' + Z.of_nat n <= k1 \/ k1 + 3 <= k') ->
  sub (if c then upd (upd (upd bs k1 v1) k2 v2) k3 v3 else bs) k' n = sub bs k' n.
Proof.
  intros [|] bs v1 v2 v3 k1 k2 k3 k' n Hk E2 E3 L1 L2 L3 Hl Hk' Hd; [|reflexivity].
  assert (A1 : length (upd bs k1 v1) = length bs) by (apply length_upd; lia).
  assert (A2 : length (upd (upd bs k1 v1) k2 v2) = length bs) by (rewrite length_upd; lia).
  rewrite sub_upd_out by lia. rewrite sub_upd_out by lia. rewrite sub_upd_out by lia. reflexivity.
Qed.

Lemma sub_ite3_1 : forall (c : bool) (bs v1 v2 v3 : list byte) k1 k2 k3, 0 <= k1 -> k2 = k1 + 1 -> k3 = k1 + 2 ->
  length v1 = 1%nat -> length v2 = 1%nat -> length v3 = 1%nat -> k1 + 3 <= Z.of_nat (length bs) ->
  sub (if c then upd (upd (upd bs k1 v1) k2 v2) k3 v3 else bs) k1 1 = if c then v1 else sub bs k1 1.
Proof.
  intros [|] bs v1 v2 v3 k1 k2 k3 Hk E2 E3 L1 L2 L3 Hl; [|reflexivity].
  assert (A1 : length (upd bs k1 v1) = length bs) by (apply length_upd; lia).
  assert (A2 : length (upd (upd bs k1 v1) k2 v2) = length bs) by (rewrite length_upd; lia).
  rewrite sub_upd_out by lia. rewrite sub_upd_out by lia. apply sub_upd_eq; lia.
Qed.

Lemma sub_ite3_2 : forall (c : bool) (bs v1 v2 v3 : list byte) k1 k2 k3, 0 <= k1 -> k2 = k1 + 1 -> k3 = k1 + 2 ->
  length v1 = 1%nat -> length v2 = 1%nat -> length v3 = 1%nat -> k1 + 3 <= Z.of_nat (length bs) ->
  sub (if c then upd (upd (upd bs k1 v1) k2 v2) k3 v3 else bs) k2 1 = if c then v2 else sub bs k2 1.
Proof.
  intros [|] bs v1 v2 v3 k1 k2 k3 Hk E2 E3 L1 L2 L3 Hl; [|reflexivity].
  assert (A1 : length (upd bs k1 v1) = length bs) by (apply length_upd; lia).
  assert (A2 : length (upd (upd bs k1 v1) k2 v2) = length bs) by (rewrite length_upd; lia).
  rewrite sub_upd_out by lia. apply sub_upd_eq; lia.
Qed.

Lemma sub_ite3_3 : forall (c : bool) (bs v1 v2 v3 : list byte) k1 k2 k3, 0 <= k1 -> k2 = k1 + 1 -> k3 = k1 + 2 ->
  length v1 = 1%nat -> length v2 = 1%nat -> length v3 = 1%nat -> k1 + 3 <= Z.of_nat (length bs) ->
  sub (if c then upd (upd (upd bs k1 v1) k2 v2) k3 v3 else bs) k3 1 = if c then v3 else sub bs k3 1.
Proof.
  intros [|] bs v1 v2 v3 k1 k2 k3 Hk E2 E3 L1 L2 L3 Hl; [|reflexivity].
  assert (A1 : length (upd bs k1 v1) = length bs) by (apply length_upd; lia).
  assert (A2 : length (upd (upd bs k1 v1) k2 v2) = length bs) by (rewrite length_upd; lia).
  apply sub_upd_eq; lia.
Qed.

Definition c_role (T G : list byte) (r : Z) : bool :=
  negb (s_role G =? 0) && negb (role_of_e T r =? s_role G) && negb ((role_of_e T r =? 1) && (s_role G =? 2)).
Definition c_decl (T G : list byte) (r : Z) : bool :=
  negb (s_hd G =? 0) && ((hd_of T r =? 0) || negb (din_of T r =? s_din G) || negb (dout_of T r =? s_dout G)).
Definition c_slots (T G : list byte) (r : Z) : bool := negb (s_slots G =? 0) && negb (slots_of T r =? s_slots G).
Definition c_fam (T G : list byte) (r : Z) : bool := negb (s_fam G =? 0) && negb (fam_of T r =? s_fam G).
Definition c_ch (T G : list byte) (r : Z) : bool := ch_of T r <? s_ch G.
Definition c_own (T : list byte) (ow r : Z) : bool := negb (ow =? 0) && (owned_of T r =? 0).
Definition c_any (T G : list byte) (ow r : Z) : bool :=
  c_role T G r || c_decl T G r || c_slots T G r || c_fam T G r || c_ch T G r || c_own T ow r.

Lemma ok_struct : forall T G ow now i, exists Ta Tb Tc Td Te Tf Tg,
  Ta = upd T (48 * i + 40) (Z_to_le_bytes 8 now) /\
  Tb = (if c_role T G i then upd Ta (48 * i + 8) (sub G 8 4) else Ta) /\
  Tc = (if c_decl T G i then upd (upd (upd Tb (48 * i + 12) [Z_to_bv 8 1]) (48 * i + 13) (sub G 13 1))
                                 (48 * i + 14) (sub G 14 1) else Tb) /\
  Td = (if c_slots T G i then upd Tc (48 * i + 16) (sub G 16 1) else Tc) /\
  Te = (if c_fam T G i then upd Td (48 * i + 15) (sub G 15 1) else Td) /\
  Tf = (if c_ch T G i then upd Te (48 * i + 20) (sub G 20 4) else Te) /\
  Tg = (if c_own T ow i then upd Tf (48 * i + 24) (Z_to_le_bytes 4 1) else Tf) /\
  observe_known T G ow now i = (if c_any T G ow i then (upd Tg 392 (Z_to_le_bytes 4 (seq_of T + 1)), 1) else (Tg, 0)).
Proof. intros. do 7 eexists. repeat split. Qed.

Ltac lside := first [ reflexivity | rewrite ?length_sub by lia; cbn [length]; rewrite ?length_Z_to_le_bytes; lia ].

Ltac ssimp :=
  repeat first [ rewrite sub_upd_out by lside | rewrite sub_ite_out by lside | rewrite sub_ite3_out by lside
               | rewrite sub_upd_eq by lside | rewrite sub_ite_eq by lside
               | rewrite sub_ite3_1 by lside | rewrite sub_ite3_2 by lside | rewrite sub_ite3_3 by lside ].

Lemma ok_facts : forall T G ow now r T' ret,
  length T = 400%nat -> length G = 24%nat -> 0 <= r < 8 ->
  (T', ret) = observe_known T G ow now r ->
  length T' = 400%nat /\
  (forall j, 0 <= j < 8 -> mac_of T' j = mac_of T j) /\
  sub T' 384 4 = sub T 384 4 /\
  sub T' (48 * r + 8) 4 = (if c_role T G r then sub G 8 4 else sub T (48 * r + 8) 4) /\
  sub T' (48 * r + 12) 1 = (if c_decl T G r then [Z_to_bv 8 1] else sub T (48 * r + 12) 1) /\
  sub T' (48 * r + 13) 1 = (if c_decl T G r then sub G 13 1 else sub T (48 * r + 13) 1) /\
  sub T' (48 * r + 14) 1 = (if c_decl T G r then sub G 14 1 else sub T (48 * r + 14) 1) /\
  sub T' (48 * r + 15) 1 = (if c_fam T G r then sub G 15 1 else sub T (48 * r + 15) 1) /\
  sub T' (48 * r + 16) 1 = (if c_slots T G r then sub G 16 1 else sub T (48 * r + 16) 1) /\
  sub T' (48 * r + 20) 4 = (if c_ch T G r then sub G 20 4 else sub T (48 * r + 20) 4) /\
  sub T' (48 * r + 24) 4 = (if c_own T ow r then Z_to_le_bytes 4 1 else sub T (48 * r + 24) 4) /\
  sub T' (48 * r + 32) 8 = sub T (48 * r + 32) 8 /\
  sub T' (48 * r + 40) 8 = Z_to_le_bytes 8 now /\
  sub T' 392 4 = (if c_any T G ow r then Z_to_le_bytes 4 (seq_of T + 1) else sub T 392 4) /\
  ret = (if c_any T G ow r then 1 else 0).
Proof.
  intros T G ow now r T' ret LT LG Hr E.
  destruct (ok_struct T G ow now r) as (Ta & Tb & Tc & Td & Te & Tf & Tg & Ea & Eb & Ec & Ed & Ee & Ef & Eg & EO).
  rewrite EO in E. clear EO.
  assert (La : length Ta = 400%nat) by (rewrite Ea, length_upd; lside).
  assert (Lb : length Tb = 400%nat) by (rewrite Eb, len_ite; lside).
  assert (Lc : length Tc = 400%nat) by (rewrite Ec, len_ite3; lside).
  assert (Ld : length Td = 400%nat) by (rewrite Ed, len_ite; lside).
  assert (Le : length Te = 400%nat) by (rewrite Ee, len_ite; lside).
  assert (Lf : length Tf = 400%nat) by (rewrite Ef, len_ite; lside).
  assert (Lg : length Tg = 400%nat) by (rewrite Eg, len_ite; lside).
  assert (ET : T' = (if c_any T G ow r then upd Tg 392 (Z_to_le_bytes 4 (seq_of T + 1)) else Tg) /\
               ret = (if c_any T G ow r then 1 else 0))
    by (destruct (c_any T G ow r); injection E as E1 E2; split; assumption).
  destruct ET as [ET Eret]. subst T' ret. clear E.
  assert (Lt : length (if c_any T G ow r then upd Tg 392 (Z_to_le_bytes 4 (seq_of T + 1)) else Tg) = 400%nat)
    by (rewrite len_ite; lside).
  split; [exact Lt|]. split; [intros j Hj; unfold mac_of|].
  all: repeat match goal with |- _ /\ _ => split end.
  all: ssimp; try (rewrite Eg; ssimp); try (rewrite Ef; ssimp); try (rewrite Ee; ssimp);
    try (rewrite Ed; ssimp); try (rewrite Ec; ssimp); try (rewrite Eb; ssimp); try (rewrite Ea; ssimp); reflexivity.
Qed.

Lemma rwc_bytes : forall m a n bs, rw_cells rsegs m a [CB n bs] -> bytes_at rsegs m a bs.
Proof. intros m a n bs [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B. Qed.

Lemma rwc_len : forall m a n bs, rw_cells rsegs m a [CB n bs] -> length bs = n.
Proof. intros m a n bs [[[W _] _] _]. exact W. Qed.

Lemma rwc_mac : forall m a G, rw_cells rsegs m a [CB 24 G] -> bytes_at rsegs m a (s_mac G).
Proof.
  intros m a G H. pose proof (rwc_len _ _ _ _ H) as L. apply rwc_bytes in H.
  rewrite <- (Z.add_0_r a). apply bytes_at_sub; [exact H | lia | rewrite L; lia].
Qed.

Lemma len_mac : forall G, length G = 24%nat -> length (s_mac G) = 6%nat.
Proof. intros G L. apply length_sub; lia. Qed.

Lemma shl_w : forall r k, 0 <= k -> Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 r)) k) = Z_to_bv 64 (r * 2 ^ k).
Proof.
  intros r k Hk. apply Z_to_bv_eqm. rewrite Z.shiftl_mul_pow2 by lia. rewrite unsigned_lit_wrap.
  apply Z.mul_mod_idemp_l. lia.
Qed.

Lemma add_ww : forall a b, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 a) + bv_unsigned (Z_to_bv 64 b)) = Z_to_bv 64 (a + b).
Proof. intros a b. apply Z_to_bv_eqm. rewrite !unsigned_lit_wrap. rewrite <- Zplus_mod. reflexivity. Qed.

Lemma sub_ww : forall a b, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 a) - bv_unsigned (Z_to_bv 64 b)) = Z_to_bv 64 (a - b).
Proof. intros a b. apply Z_to_bv_eqm. rewrite !unsigned_lit_wrap. rewrite <- Zminus_mod. reflexivity. Qed.

Lemma so_ld : forall bs, length bs = 8%nat -> bv_extract 0 64 (le_bytes_to_word bs) = Z_to_bv 64 (bytes_le_to_Z bs).
Proof.
  intros bs L. apply bv_eq. rewrite extract_low_mod by lia. unfold le_bytes_to_word.
  pose proof (ble_range bs) as H. rewrite L in H. change (8 * Z.of_nat 8) with 64 in H.
  rewrite !unsigned_lit by lia. change (Z.of_N 64) with 64. apply Z.mod_small. lia.
Qed.

Definition R22 : Z := 0x13860.
Definition R23 : Z := 0x13e1c.
Definition R24 : Z := 0x13ed4.
Definition R25 : Z := 0x14380.

Definition old_w (r v : Z) : word := Z_to_bv 64 (if r <? 0 then 0 else v).
Definition fs_of (T : list byte) (i : Z) : Z := u_at T (48 * i + 32) 8.
Definition chs_of (T : list byte) (i : Z) : Z := s32_at T (48 * i + 20).
Definition own_bit (op : Z) : Z := (op / 8) mod 2.

Definition old_cells (T : list byte) (r : Z) (j : list byte) : list cell :=
  [CB 32 j; C8 (old_w r (fs_of T r)); C8 (Z_to_bv 64 (r * 64)); C8 (Z_to_bv 64 (r * 16));
   C8 (old_w r (hd_of T r)); C8 (old_w r (din_of T r)); C8 (old_w r (dout_of T r));
   C8 (old_w r (slots_of T r)); C8 (old_w r (owned_of T r)); C8 (old_w r (chs_of T r))].

Ltac rdh A B k n :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with H : bytes_at rsegs mm A B |- _ =>
      let RD := fresh "RD" in pose proof (rd_sub mm A B k n H ltac:(lia) ltac:(lia)) as RD
    end
  end.

Lemma slot_R22 : find_entry_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X lo : Z) (T G jsp : list byte) (push : word),
  sp = Z_to_bv 64 X -> 0 < X -> X mod 16 = 0 -> X + 2592 < 2 ^ 63 ->
  rw_cells rsegs m (X + 40) [CB 104 jsp] -> rw_cells rsegs m (X + 152) [C8 push] ->
  rw_cells rsegs m (X + 512) [CB 400 T] -> tbl_T1 T -> rw_cells rsegs m (X + 1024) [CB 24 G] ->
  mem_inv rsegs m -> stk rsegs m lo X -> lo + FIND_ENTRY_K <= X ->
  evt rsegs
    (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                       (m' : word -> option byte) (r : Z) (j : list byte),
       ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                     s2 s3 s4 s5 s6 (Z_to_bv 64 r) s8 (old_w r (fam_of T r)) s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 R23) fc None m' (seg_rom rsegs) /\
       munch [(lo, X); (X + 40, X + 144); (X + 152, X + 160)] m m' /\ wmono rsegs m m' /\
       mem_inv rsegs m' /\ stk rsegs m' lo X /\ find_res T (s_mac G) r /\
       rw_cells rsegs m' (X + 40) (old_cells T r j) /\
       rw_cells rsegs m' (X + 152) [C8 (old_w r (role_of_e T r))] /\
       rw_cells rsegs m' (X + 512) [CB 400 T] /\ rw_cells rsegs m' (X + 1024) [CB 24 G])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 R22) fc None m (seg_rom rsegs)).
Proof.
  intros FEC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m X lo T G jsp push Esp HX0 HX16 HX1 RS RP RT T1 RG MI ST HLO.
  subst sp. unfold R22, R23 in *. unfold FIND_ENTRY_K in HLO.
  pose proof (munch_refl [(lo, X); (X + 40, X + 144); (X + 152, X + 160)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (rwc_len _ _ _ _ RT) as LT. pose proof (rwc_len _ _ _ _ RG) as LG.
  pose proof (rwc_bytes _ _ _ _ RT) as HT.
  step. step. step.
  eapply evt_cut.
  { eapply FEC with (lo := lo) (t := X + 512) (p := X + 1024) (T := T) (P := s_mac G).
    - reflexivity.
    - reflexivity.
    - lia.
    - Z.div_mod_to_equations; lia.
    - exact HT.
    - exact LT.
    - exact (rwc_mac _ _ _ RG).
    - exact (len_mac G LG).
    - exact T1.
    - exact MI.
    - rewrite (unsigned_lit X) by lia. exact ST.
    - rewrite (unsigned_lit X) by lia. unfold FIND_ENTRY_K. lia.
    - unfold off_window. rewrite (unsigned_lit X) by lia. lia.
    - unfold off_window. rewrite (unsigned_lit X) by lia. lia. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & r &
              Eq & MUc & WMc & MI2 & ST2 & FR).
  subst ms'.
  rewrite (unsigned_lit X) in MUc, ST2 by lia. unfold FIND_ENTRY_K in MUc.
  transport_after_call rsegs m m2 MUc WMc. clear MUc WMc MI.
  rewrite (ret_pc_even 79980) by (first [lia | reflexivity]).
  pose proof T1 as T1'. unfold tbl_T1 in T1'.
  assert (Hr : r = -1 \/ 0 <= r < n_of T) by (destruct FR as [[-> _] | [? _]]; lia).
  step. step. step.
  rewrite !shl_w by lia. change (2 ^ 4) with 16. change (2 ^ 6) with 64.
  step. step. step.
  rewrite lts_lit by lia.
  destruct (Z.ltb_spec r 0) as [Hneg|Hpos].
  - assert (E1 : r = -1) by lia. subst r. cbv iota.
    step. step. step. step. step. step. step. step. step.
    apply evt_done. do 17 eexists. exists (-1). eexists. unfold old_cells. split; [reflexivity|].
    repeat (split; [eassumption|]). eassumption.
  - cbv iota. step. step. step.
    rewrite (unsigned_lit (r * 64)), (unsigned_lit (r * 16)) by lia.
    replace (r * 64 - r * 16) with (48 * r) by lia.
    rdh (X + 512) T (48 * r + 8) 4%nat. step. rewrite lw_val by (apply length_sub; lia). step.
    rdh (X + 512) T (48 * r + 12) 1%nat. step. rewrite lbu_val by (apply length_sub; lia). step.
    rdh (X + 512) T (48 * r + 13) 1%nat. step. rewrite lbu_val by (apply length_sub; lia). step.
    rdh (X + 512) T (48 * r + 14) 1%nat. step. rewrite lbu_val by (apply length_sub; lia). step.
    rdh (X + 512) T (48 * r + 15) 1%nat. rdh (X + 512) T (48 * r + 16) 1%nat.
    step. rewrite lbu_val by (apply length_sub; lia).
    step. rewrite lbu_val by (apply length_sub; lia). step.
    rdh (X + 512) T (48 * r + 20) 4%nat. step. rewrite lw_val by (apply length_sub; lia). step.
    rdh (X + 512) T (48 * r + 24) 4%nat. step. rewrite lw_val by (apply length_sub; lia). step.
    rdh (X + 512) T (48 * r + 32) 8%nat. step. rewrite so_ld by (apply length_sub; lia). step.
    step.
    apply evt_done. do 17 eexists. exists r. eexists. unfold old_cells, old_w.
    replace (r <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
    split; [reflexivity|].
    repeat (split; [eassumption|]). eassumption.
Qed.

Lemma find_res_unique : forall T P r1 r2, find_res T P r1 -> find_res T P r2 -> r1 = r2.
Proof.
  intros T P r1 r2 [[E1 N1] | (R1 & M1 & B1)] [[E2 N2] | (R2 & M2 & B2)].
  - lia.
  - exfalso. exact (N1 r2 R2 M2).
  - exfalso. exact (N2 r1 R1 M1).
  - destruct (Z.lt_trichotomy r1 r2) as [H|[H|H]];
      [exfalso; exact (B2 r1 ltac:(lia) M1) | exact H | exfalso; exact (B1 r2 ltac:(lia) M2)].
Qed.

Lemma find_res_eqv : forall T T' P r, n_of T' = n_of T -> 0 <= n_of T <= 8 ->
  (forall j, 0 <= j < 8 -> mac_of T' j = mac_of T j) -> find_res T' P r -> find_res T P r.
Proof.
  intros T T' P r EN HN EM [[E N] | (R & M & B)].
  - left. split; [exact E|]. intros j Hj. rewrite <- EM by lia. apply N. lia.
  - right. split; [lia|]. split; [rewrite <- EM by lia; exact M|]. intros j Hj. rewrite <- EM by lia. apply B. lia.
Qed.

Lemma rwc_split : forall m a n bs, rw_cells rsegs m a [CB n bs] ->
  length bs = n /\ bytes_at rsegs m a bs /\ wr_at rsegs m a (Z.of_nat n).
Proof.
  intros m a n bs [[[W _] B] H]. cbn [cells_bytes cbytes cells_size csize] in B, H.
  rewrite app_nil_r in B. rewrite Nat.add_0_r in H. split; [exact W|]. split; assumption.
Qed.

Lemma rwc_mk : forall m a n bs, length bs = n -> bytes_at rsegs m a bs -> wr_at rsegs m a (Z.of_nat n) ->
  rw_cells rsegs m a [CB n bs].
Proof.
  intros m a n bs L B W. split; [split|].
  - cbn. split; [exact L | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact W.
Qed.

Lemma own_bit_w : forall op, 0 <= op < 2 ^ 64 ->
  Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 op)) 60))) 63) =
  Z_to_bv 64 (own_bit op).
Proof.
  intros op Hop. f_equal. rewrite (unsigned_lit op) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite unsigned_lit_wrap. rewrite Z.shiftr_div_pow2 by lia. unfold own_bit.
  replace (2 ^ 64) with (16 * 2 ^ 60) by reflexivity. rewrite Z.mul_mod_distr_r by lia.
  replace (2 ^ 63) with (8 * 2 ^ 60) by reflexivity. rewrite Z.div_mul_cancel_r by lia.
  Z.div_mod_to_equations. lia.
Qed.

Lemma own_bit_range : forall op, 0 <= own_bit op <= 1.
Proof. intros op. unfold own_bit. pose proof (Z.mod_pos_bound (op / 8) 2 ltac:(lia)). lia. Qed.

Lemma obs_ret : forall T G ow now T' ret, length T = 400%nat -> length G = 24%nat -> tbl_T1 T ->
  observe_model T G ow now T' ret -> ret = 0 \/ ret = 1.
Proof.
  intros T G ow now T' ret LT LG T1 (r & FR & [(Hr & E) | [(Hr & HN & E) | (Hr & HN & E)]]).
  - assert (Hr8 : 0 <= r < 8) by (destruct FR as [[? _]|[? _]]; unfold tbl_T1 in T1; lia).
    destruct (ok_facts T G ow now r T' ret LT LG Hr8 E) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eret).
    destruct (c_any T G ow r); lia.
  - unfold observe_full in E. destruct (ov_of T =? 0); injection E as _ E2; lia.
  - unfold observe_new in E. injection E as _ E2. lia.
Qed.

Lemma len_new : forall G ow now, length G = 24%nat -> length (new_entry G ow now) = 48%nat.
Proof.
  intros G ow now LG. unfold new_entry, s_mac, zeros.
  rewrite !length_app, !length_sub by lia. rewrite !repeat_length, !length_Z_to_le_bytes. reflexivity.
Qed.

Lemma new_fields : forall G ow now, length G = 24%nat ->
  sub (new_entry G ow now) 0 6 = s_mac G /\ sub (new_entry G ow now) 8 4 = sub G 8 4 /\
  sub (new_entry G ow now) 12 1 = sub G 12 1 /\ sub (new_entry G ow now) 13 1 = sub G 13 1 /\
  sub (new_entry G ow now) 14 1 = sub G 14 1 /\ sub (new_entry G ow now) 15 1 = sub G 15 1 /\
  sub (new_entry G ow now) 16 1 = sub G 16 1 /\ sub (new_entry G ow now) 20 4 = sub G 20 4 /\
  sub (new_entry G ow now) 24 4 = Z_to_le_bytes 4 (if ow =? 0 then 0 else 1) /\
  sub (new_entry G ow now) 32 8 = Z_to_le_bytes 8 now /\ sub (new_entry G ow now) 40 8 = Z_to_le_bytes 8 now.
Proof.
  intros G ow now LG.
  do 24 (destruct G as [|? G]; [cbn in LG; lia|]). destruct G; [|cbn in LG; lia].
  unfold new_entry, s_mac, sub, zeros. cbn. repeat split; reflexivity.
Qed.

Lemma full_facts : forall T T' ret, length T = 400%nat -> (T', ret) = observe_full T ->
  length T' = 400%nat /\ ret = 0 /\ sub T' 384 4 = sub T 384 4 /\
  sub T' 388 4 = (if ov_of T =? 0 then Z_to_le_bytes 4 1 else sub T 388 4) /\
  sub T' 392 4 = (if ov_of T =? 0 then Z_to_le_bytes 4 (seq_of T + 1) else sub T 392 4) /\
  (forall j, 0 <= j < 8 -> mac_of T' j = mac_of T j).
Proof.
  intros T T' ret LT E. unfold observe_full in E.
  destruct (ov_of T =? 0);
    pose proof (f_equal fst E) as E1; pose proof (f_equal snd E) as E2; cbn [fst snd] in E1, E2; subst T' ret.
  - remember (upd T 388 (Z_to_le_bytes 4 1)) as Ta eqn:Ea.
    assert (A1 : length Ta = 400%nat) by (rewrite Ea, length_upd; lside).
    split; [rewrite length_upd; [exact A1 | lia | rewrite length_Z_to_le_bytes; lia]|]. split; [reflexivity|].
    split; [ssimp; rewrite Ea; ssimp; reflexivity|].
    split; [ssimp; rewrite Ea; ssimp; reflexivity|].
    split; [ssimp; reflexivity|].
    intros j Hj. unfold mac_of. ssimp. rewrite Ea. ssimp. reflexivity.
  - split; [exact LT|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. intros j Hj. reflexivity.
Qed.

Lemma new_facts : forall T G ow now T' ret, length T = 400%nat -> length G = 24%nat -> 0 <= n_of T < 8 ->
  (T', ret) = observe_new T G ow now ->
  length T' = 400%nat /\ ret = 1 /\
  sub T' 384 4 = Z_to_le_bytes 4 (n_of T + 1) /\
  sub T' 392 4 = Z_to_le_bytes 4 (seq_of T + 1) /\
  (forall d w, 0 <= d -> d + Z.of_nat w <= 48 -> sub T' (48 * n_of T + d) w = sub (new_entry G ow now) d w).
Proof.
  intros T G ow now T' ret LT LG HN E. unfold observe_new in E.
  pose proof (f_equal fst E) as E1. pose proof (f_equal snd E) as E2. cbn [fst snd] in E1, E2. subst T' ret.
  pose proof (len_new G ow now LG) as LE.
  remember (upd T 384 (Z_to_le_bytes 4 (n_of T + 1))) as Ta eqn:Ea.
  remember (upd Ta (48 * n_of T) (new_entry G ow now)) as Tb eqn:Eb.
  assert (A1 : length Ta = 400%nat) by (rewrite Ea, length_upd; lside).
  assert (A2 : length Tb = 400%nat) by (rewrite Eb, length_upd by lia; exact A1).
  split; [rewrite length_upd; [exact A2 | lia | rewrite length_Z_to_le_bytes; lia]|]. split; [reflexivity|].
  split; [ssimp; rewrite Eb; ssimp; rewrite Ea; ssimp; reflexivity|].
  split; [ssimp; reflexivity|].
  intros d w Hd Hw. rewrite sub_upd_out by (rewrite ?length_Z_to_le_bytes; lia). rewrite Eb. apply sub_upd_d; lia.
Qed.

Lemma old_w_pos : forall r v, 0 <= r -> old_w r v = Z_to_bv 64 v.
Proof. intros r v Hr. unfold old_w. replace (r <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. Qed.

Lemma old_w_neg : forall r v, r < 0 -> old_w r v = Z_to_bv 64 0.
Proof. intros r v Hr. unfold old_w. replace (r <? 0) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. Qed.

Ltac rdx A B k n RDn :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with H : bytes_at rsegs mm A B |- _ =>
      pose proof (rd_sub mm A B k n H ltac:(lia) ltac:(lia)) as RDn
    end
  end.

Lemma so_eqb_refl : forall w : word, bv_eqb w w = true.
Proof. intros w. unfold bv_eqb. apply Z.eqb_refl. Qed.

Lemma slti_lit : forall z imm, - 2 ^ 63 <= z < 2 ^ 63 -> v_slti (Z_to_bv 64 z) imm = Z_to_bv 64 (Z.b2z (z <? imm)).
Proof. intros z imm Hz. unfold v_slti, zsig. rewrite signed_lit by lia. destruct (z <? imm); reflexivity. Qed.

Lemma sltiu1_lit : forall z, - 2 ^ 63 <= z < 2 ^ 63 -> v_sltiu (Z_to_bv 64 z) 1 = Z_to_bv 64 (Z.b2z (z =? 0)).
Proof.
  intros z Hz. unfold v_sltiu. rewrite unsigned_lit_wrap. change (bv_wrap 64 1) with 1.
  destruct (Z.eqb_spec z 0) as [->|N]; [reflexivity|].
  replace (z mod 2 ^ 64 <? 1) with false; [reflexivity|].
  symmetry. apply Z.ltb_ge. Z.div_mod_to_equations. lia.
Qed.

Lemma so_land : forall b1 b2 : bool,
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (Z.b2z b1))) (bv_unsigned (Z_to_bv 64 (Z.b2z b2)))) =
  Z_to_bv 64 (Z.b2z (b1 && b2)).
Proof. intros [|] [|]; reflexivity. Qed.

Lemma land_not_b2z : forall b1 b2 : bool,
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (Z.b2z b1)))
                     (bv_unsigned (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 (Z.b2z b2))) 18446744073709551615)))) =
  Z_to_bv 64 (Z.b2z (b1 && negb b2)).
Proof. intros [|] [|]; vm_compute; reflexivity. Qed.

Lemma seq_range : forall T, length T = 400%nat -> 0 <= seq_of T < 2 ^ 32.
Proof.
  intros T LT. unfold seq_of, u_at. pose proof (ble_range (sub T 392 4)) as H.
  rewrite length_sub in H by lia. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in H. exact H.
Qed.

Lemma seq_w : forall s ret rf, 0 <= s < 2 ^ 32 -> 0 <= ret -> 0 <= rf -> ret + rf <= 1 ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (ret + bv_swrap 32 s)) + bv_unsigned (Z_to_bv 64 rf))) =
  Z_to_bv 64 (bv_swrap 32 ((s + ret + rf) mod 2 ^ 32)).
Proof.
  intros s ret rf Hs Hr Hf Hrf. f_equal. rewrite !unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  replace (2 ^ 64) with 18446744073709551616 by reflexivity. replace (2 ^ 32) with 4294967296 by reflexivity.
  Z.div_mod_to_equations. lia.
Qed.

Lemma known_arm : forall T G ow now T' ret r, find_res T (s_mac G) r -> 0 <= r ->
  observe_model T G ow now T' ret -> (T', ret) = observe_known T G ow now r.
Proof.
  intros T G ow now T' ret r FR Hr (r' & FR' & H).
  pose proof (find_res_unique _ _ _ _ FR FR') as Er. subst r'.
  destruct H as [(_ & E) | [(Hr' & _ & _) | (Hr' & _ & _)]]; [exact E | lia | lia].
Qed.

Lemma unknown_arm : forall T G ow now T' ret r, find_res T (s_mac G) r -> r < 0 ->
  observe_model T G ow now T' ret ->
  (8 <= n_of T /\ (T', ret) = observe_full T) \/ (n_of T < 8 /\ (T', ret) = observe_new T G ow now).
Proof.
  intros T G ow now T' ret r FR Hr (r' & FR' & H).
  pose proof (find_res_unique _ _ _ _ FR FR') as Er. subst r'.
  destruct H as [(Hr' & _) | [(_ & HN & E) | (_ & HN & E)]];
    [lia | left; split; assumption | right; split; assumption].
Qed.

Lemma n_of_sub : forall T T', sub T' 384 4 = sub T 384 4 -> n_of T' = n_of T.
Proof. intros T T' E. unfold n_of, s32_at, u_at. rewrite E. reflexivity. Qed.

Lemma known_find : forall T G ow now T' ret r idx, length T = 400%nat -> length G = 24%nat -> tbl_T1 T ->
  find_res T (s_mac G) r -> 0 <= r -> observe_model T G ow now T' ret -> find_res T' (s_mac G) idx -> idx = r.
Proof.
  intros T G ow now T' ret r idx LT LG T1 FR Hr OM FR2.
  pose proof T1 as T1'. unfold tbl_T1 in T1'.
  assert (Hr8 : 0 <= r < 8) by (destruct FR as [[? _]|[? _]]; lia).
  pose proof (known_arm T G ow now T' ret r FR Hr OM) as E.
  destruct (ok_facts T G ow now r T' ret LT LG Hr8 E) as (_ & EM & E384 & _).
  apply (find_res_unique T (s_mac G)); [|exact FR].
  apply (find_res_eqv T T'); [apply n_of_sub; exact E384 | exact T1' | exact EM | exact FR2].
Qed.

Lemma c_role_box : forall T G r, role_of_e T r = 1 -> sighting_S1 G -> c_role T G r = false.
Proof. intros T G r E S1. unfold c_role. rewrite E. destruct S1 as [S|[S|S]]; rewrite S; reflexivity. Qed.

Lemma seq_target : forall T G ow now T' ret r, length T = 400%nat -> length G = 24%nat -> tbl_T1 T ->
  find_res T (s_mac G) r -> observe_model T G ow now T' ret ->
  0 <= ret /\ ret + Z.b2z ((r <? 0) && (ov_of T =? 0) && negb (n_of T <? 8)) <= 1 /\
  bytes_le_to_Z (sub T' 392 4) = (seq_of T + ret + Z.b2z ((r <? 0) && (ov_of T =? 0) && negb (n_of T <? 8))) mod 2 ^ 32.
Proof.
  intros T G ow now T' ret r LT LG T1 FR OM.
  pose proof T1 as T1'. unfold tbl_T1 in T1'. pose proof (seq_range T LT) as HS.
  destruct (Z.ltb_spec r 0) as [Hn|Hp].
  - replace (r <? 0) with true by (symmetry; apply Z.ltb_lt; lia).
    destruct (unknown_arm T G ow now T' ret r FR Hn OM) as [(HN & E) | (HN & E)].
    + destruct (full_facts T T' ret LT E) as (_ & Er & _ & _ & E392 & _). subst ret.
      replace (n_of T <? 8) with false by (symmetry; apply Z.ltb_ge; lia). rewrite E392.
      destruct (ov_of T =? 0); cbn [andb negb Z.b2z].
      * rewrite bytes_le_to_Z_to_le_bytes by lia. replace (8 * Z.of_nat 4) with 32 by reflexivity.
        split; [lia|]. split; [lia|]. f_equal. lia.
      * split; [lia|]. split; [lia|]. rewrite !Z.add_0_r. rewrite Z.mod_small by lia. reflexivity.
    + destruct (new_facts T G ow now T' ret LT LG ltac:(lia) E) as (_ & Er & _ & E392 & _). subst ret.
      replace (n_of T <? 8) with true by (symmetry; apply Z.ltb_lt; lia). rewrite E392.
      cbn [negb andb]. rewrite andb_false_r. cbn [Z.b2z].
      rewrite bytes_le_to_Z_to_le_bytes by lia. replace (8 * Z.of_nat 4) with 32 by reflexivity.
      split; [lia|]. split; [lia|]. f_equal. lia.
  - assert (Hr8 : 0 <= r < 8) by (destruct FR as [[? _]|[? _]]; lia).
    pose proof (known_arm T G ow now T' ret r FR Hp OM) as E.
    destruct (ok_facts T G ow now r T' ret LT LG Hr8 E)
      as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E392 & Eret).
    replace (r <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
    cbn [andb Z.b2z]. rewrite E392. subst ret.
    destruct (c_any T G ow r); cbv iota.
    + rewrite bytes_le_to_Z_to_le_bytes by lia. replace (8 * Z.of_nat 4) with 32 by reflexivity.
      split; [lia|]. split; [lia|]. f_equal. lia.
    + split; [lia|]. split; [lia|]. rewrite !Z.add_0_r. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma slot_R23 : reac_disco_table_observe_contract -> check_table_contract -> find_entry_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X lo now op h i r : Z) (T G j : list byte),
  sp = Z_to_bv 64 X -> s7 = Z_to_bv 64 r -> s11 = Z_to_bv 64 now ->
  0 < X -> X mod 16 = 0 -> X + 2592 < 2 ^ 63 -> 0 <= now < 2 ^ 64 -> 0 <= op < 2 ^ 64 ->
  find_res T (s_mac G) r ->
  rw_cells rsegs m (X + 40) (old_cells T r j) ->
  rw_cells rsegs m (X + 144) [C8 (Z_to_bv 64 h)] ->
  rw_cells rsegs m (X + 152) [C8 (old_w r (role_of_e T r))] ->
  rw_cells rsegs m (X + 160) [C8 (Z_to_bv 64 i)] ->
  rw_cells rsegs m (X + 216) [C8 (Z_to_bv 64 op)] ->
  rw_cells rsegs m (X + 512) [CB 400 T] -> tbl_T1 T -> tbl_T2 T -> tbl_T3 T -> tbl_T4 T ->
  rw_cells rsegs m (X + 1024) [CB 24 G] -> sighting_S1 G -> sighting_S2 G ->
  mem_inv rsegs m -> stk rsegs m lo X -> lo + CHECK_TABLE_K <= X ->
  evt rsegs
    (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                       (m' : word -> option byte) (T' : list byte) (ret : Z),
       ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 i) a0' a1' a2' a3' a4' a5' a6' a7'
                     s2 s3 (Z_to_bv 64 h) (Z_to_bv 64 ret) (Z_to_bv 64 (own_bit op)) s7 s8 s9
                     (Z_to_bv 64 (n_of T)) s11 t3' t4' t5' t6')
                F (Z_to_bv 64 (if r <? 0 then R25 else R24)) fc None m' (seg_rom rsegs) /\
       munch [(lo, X); (X + 512, X + 912)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo X /\
       rw_cells rsegs m' (X + 40) (old_cells T r j) /\
       rw_cells rsegs m' (X + 144) [C8 (Z_to_bv 64 h)] /\
       rw_cells rsegs m' (X + 152) [C8 (old_w r (role_of_e T r))] /\
       rw_cells rsegs m' (X + 160) [C8 (Z_to_bv 64 i)] /\
       rw_cells rsegs m' (X + 216) [C8 (Z_to_bv 64 op)] /\
       rw_cells rsegs m' (X + 512) [CB 400 T'] /\ rw_cells rsegs m' (X + 1024) [CB 24 G] /\
       observe_model T G (own_bit op) now T' ret /\ tbl_T1 T' /\ tbl_T2 T' /\ tbl_T3 T' /\ tbl_T4 T')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 R23) fc None m (seg_rom rsegs)).
Proof.
  intros OBC CTC FEC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m X lo now op h i r T G j Esp Es7 Es11 HX0 HX16 HX1 Hnow Hop FR RS RH RO RI RP RT T1 T2 T3 T4 RG S1 S2
    MI ST HLO.
  subst sp s7 s11. unfold R23, R24, R25 in *. unfold CHECK_TABLE_K in HLO. unfold old_cells in RS.
  pose proof (munch_refl [(lo, X); (X + 512, X + 912)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof T1 as T1'. unfold tbl_T1 in T1'.
  assert (Hr : r = -1 \/ 0 <= r < n_of T) by (destruct FR as [[-> _] | [? _]]; lia).
  apply rwc_split in RT. destruct RT as (LT & HT & WT).
  pose proof (rwc_len _ _ _ _ RG) as LG. pose proof (rwc_bytes _ _ _ _ RG) as HG.
  rdh (X + 512) T 384 4%nat. rdh (X + 512) T 388 4%nat. rdh (X + 512) T 392 4%nat.
  step. rewrite lw_val by (apply length_sub; lia).
  step. rewrite lw_val by (apply length_sub; lia).
  step. rewrite lw_val by (apply length_sub; lia).
  change (bv_swrap 32 (bytes_le_to_Z (sub T 384 4))) with (n_of T).
  change (bv_swrap 32 (bytes_le_to_Z (sub T 388 4))) with (ov_of T).
  step. step. step. rewrite own_bit_w by lia.
  pose proof (own_bit_range op) as HOB.
  step. step. step. step. step.
  eapply evt_cut.
  { eapply OBC with (lo := lo) (t := X + 512) (s := X + 1024) (ow := own_bit op) (now := now) (T := T) (G := G).
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - lia.
    - lia.
    - lia.
    - Z.div_mod_to_equations; lia.
    - exact (rwc_mk _ _ _ _ LT HT WT).
    - exact LT.
    - lia.
    - Z.div_mod_to_equations; lia.
    - exact HG.
    - exact LG.
    - lia.
    - exact T1.
    - exact T2.
    - exact T3.
    - exact S1.
    - exact S2.
    - exact MI.
    - rewrite (unsigned_lit X) by lia. exact ST.
    - rewrite (unsigned_lit X) by lia. unfold REAC_DISCO_TABLE_OBSERVE_K. lia.
    - unfold off_window. rewrite (unsigned_lit X) by lia. lia.
    - unfold off_window. rewrite (unsigned_lit X) by lia. lia. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & T' & ret &
              Eq & MUc & WMc & MI2 & ST2 & RT2 & HG2 & OM & T1b & T2b & T3b & T4i).
  subst ms'.
  rewrite (unsigned_lit X) in MUc, ST2 by lia. unfold REAC_DISCO_TABLE_OBSERVE_K in MUc.
  transport_after_call rsegs m m2 MUc WMc. clear MUc WMc MI.
  rewrite (ret_pc_even 81480) by (first [lia | reflexivity]).
  apply rwc_split in RT2. destruct RT2 as (LT2 & HT2 & WT2).
  assert (HRet : ret = 0 \/ ret = 1) by exact (obs_ret T G (own_bit op) now T' ret LT LG T1 OM).
  step. step. step.
  rewrite ltu_lit by lia. replace (ret <? 2) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb].
  step. step.
  eapply evt_cut.
  { eapply CTC with (lo := lo) (t := X + 512) (T := T').
    - reflexivity.
    - Z.div_mod_to_equations; lia.
    - exact HT2.
    - exact LT2.
    - exact T1b.
    - exact T2b.
    - exact T3b.
    - exact MI2.
    - rewrite (unsigned_lit X) by lia. exact ST2.
    - rewrite (unsigned_lit X) by lia. unfold CHECK_TABLE_K. lia.
    - unfold off_window. rewrite (unsigned_lit X) by lia. lia. }
  intros ms' (t0'' & t1'' & t2'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m3 &
              Eq & MUc & WMc & MI3 & ST3).
  subst ms'.
  rewrite (unsigned_lit X) in MUc, ST3 by lia. unfold CHECK_TABLE_K in MUc.
  transport_after_call rsegs m2 m3 MUc WMc. clear MUc WMc MI2.
  rewrite (ret_pc_even 81500) by (first [lia | reflexivity]).
  rdh (X + 512) T' 392 4%nat.
  step. step. step. step. step. rewrite lw_val by (apply length_sub; lia).
  step. step. step. step.
  rewrite (slti_lit r 0) by lia.
  rewrite (sltiu1_lit (ov_of T)) by (pose proof (s32_range T 388); unfold ov_of; lia).
  rewrite (slti_lit (n_of T) 8) by lia.
  rewrite so_land, land_not_b2z.
  change (bytes_le_to_Z (sub T 392 4)) with (seq_of T).
  destruct (seq_target T G (own_bit op) now T' ret r LT LG T1 FR OM) as (Hr0 & Hrf & EST).
  pose proof (seq_range T LT) as HS.
  rewrite seq_w by first [exact HS | lia | match goal with |- 0 <= Z.b2z ?b => destruct b; cbn; lia end].
  rewrite <- EST. step. rewrite so_eqb_refl. cbn [negb].
  step. step. step.
  rewrite lts_lit by lia.
  pose proof (rwc_mk _ _ _ _ LT2 HT2 WT2) as RT3. pose proof (T4i T4) as T4b.
  destruct (Z.ltb_spec r 0) as [Hneg|Hpos].
  - replace (r <? 0) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
    step. rewrite lts_lit by lia. replace (r <? 0) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
    apply evt_done. do 19 eexists. unfold old_cells. split; [reflexivity|].
    repeat (split; [eassumption|]). eassumption.
  - replace (r <? 0) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
    assert (Hr8 : 0 <= r < n_of T) by lia.
    pose proof (T2 r Hr8) as HR2.
    rewrite !old_w_pos in RO by lia. rewrite !old_w_pos in RS by lia.
    step. step. step.
    rewrite eqb_lit by lia.
    destruct (Z.eqb_spec (role_of_e T r) 1) as [E1|E1]; cbn [negb].
    + step. step. step.
      eapply evt_cut.
      { eapply FEC with (lo := lo) (t := X + 512) (p := X + 1024) (T := T') (P := s_mac G).
        - reflexivity.
        - reflexivity.
        - lia.
        - Z.div_mod_to_equations; lia.
        - exact HT2.
        - exact LT2.
        - exact (rwc_mac _ _ _ RG).
        - exact (len_mac G LG).
        - exact T1b.
        - exact MI3.
        - rewrite (unsigned_lit X) by lia. exact ST3.
        - rewrite (unsigned_lit X) by lia. unfold FIND_ENTRY_K. lia.
        - unfold off_window. rewrite (unsigned_lit X) by lia. lia.
        - unfold off_window. rewrite (unsigned_lit X) by lia. lia. }
      intros ms' (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m4 & idx &
                  Eq & MUc & WMc & MI4 & ST4 & FR2).
      subst ms'.
      rewrite (unsigned_lit X) in MUc, ST4 by lia. unfold FIND_ENTRY_K in MUc.
      transport_after_call rsegs m3 m4 MUc WMc. clear MUc WMc MI3.
      rewrite (ret_pc_even 81576) by (first [lia | reflexivity]).
      assert (Eidx : idx = r) by exact (known_find T G (own_bit op) now T' ret r idx LT LG T1 FR ltac:(lia) OM FR2).
      subst idx.
      pose proof (known_arm T G (own_bit op) now T' ret r FR ltac:(lia) OM) as EK.
      destruct (ok_facts T G (own_bit op) now r T' ret LT LG ltac:(lia) EK)
        as (_ & _ & _ & E8 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
      rewrite (c_role_box T G r E1 S1) in E8. cbv iota in E8.
      step. rewrite lts_lit by lia. replace (r <? 0) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
      step. step. rewrite !shl_w by lia. change (2 ^ 4) with 16. change (2 ^ 6) with 64.
      step. step. step.
      rewrite (unsigned_lit (r * 64)), (unsigned_lit (r * 16)) by lia.
      replace (r * 64 - r * 16) with (48 * r) by lia.
      rdx (X + 512) T' (48 * r + 8) 4%nat RDr. rewrite E8 in RDr.
      step. rewrite lw_val by (apply length_sub; lia).
      change (bv_swrap 32 (bytes_le_to_Z (sub T (48 * r + 8) 4))) with (role_of_e T r). rewrite E1.
      step. step. rewrite eqb_lit by lia. cbn [Z.eqb Pos.eqb].
      step.
      apply evt_done. do 19 eexists. unfold old_cells. rewrite !old_w_pos by lia. rewrite E1 in RO. split; [reflexivity|].
      repeat (split; [eassumption|]). eassumption.
    + step. rewrite lts_lit by lia. replace (r <? 0) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
      apply evt_done. do 19 eexists. unfold old_cells. rewrite !old_w_pos by lia. split; [reflexivity|].
      repeat (split; [eassumption|]). eassumption.
Qed.
