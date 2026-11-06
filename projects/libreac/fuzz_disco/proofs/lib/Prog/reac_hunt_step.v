From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Arr Bytes Image.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import CtrlParsed disco_classify_c disco_table_c disco_table hunt_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_rate_snap_c reac_rival_kind_of_c reac_master_only_cadence_ns_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_sender_kind_c reac_disco_table_age_c reac_arbitrate_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import bcmp_c reac_hunt_step_c.
Import ListNotations.
Open Scope Z_scope.

Lemma hs_freg_refl : forall F, freg_kept F F.
Proof. intros F k _ _ _. reflexivity. Qed.

Lemma hs_freg_trans : forall F1 F2 F3, freg_kept F1 F2 -> freg_kept F2 F3 -> freg_kept F1 F3.
Proof. intros F1 F2 F3 A B k H1 H2 H3. rewrite (B k H1 H2 H3). apply A; assumption. Qed.

Lemma hs_mi_stack : forall m m' lo hi k, mem_inv rsegs m -> stk rsegs m lo hi -> lo <= hi - k ->
  munch [(hi - k, hi)] m m' -> mem_inv rsegs m'.
Proof.
  intros m m' lo hi k MI (S1 & S2 & SH) Hk MU x b Hx.
  pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R.
  destruct (Z_lt_le_dec (bv_unsigned x) (hi - k)) as [L|L].
  - rewrite (MU x) in Hx by (cbn; split; [lia | exact I]). exact (MI x b Hx).
  - destruct (Z_lt_le_dec (bv_unsigned x) hi) as [L2|L2].
    + destruct (m x) as [b0|] eqn:E.
      * exact (MI x b0 E).
      * destruct (SH (bv_unsigned x) ltac:(lia)) as [W _].
        unfold wa in W. rewrite Z_to_bv_bv_unsigned in W.
        exact (wview_not_ro rsegs m x W E).
    + rewrite (MU x) in Hx by (cbn; split; [lia | exact I]). exact (MI x b Hx).
Qed.

Lemma hs_ro : forall m, mem_inv rsegs m ->
  bytes_at rsegs m RT RATES /\ bytes_at rsegs m A_P6000 (le8 (Z_to_bv 64 D6000)) /\
  bytes_at rsegs m A_P3837 (le8 (Z_to_bv 64 D3837)).
Proof.
  intros m MI.
  split; [|split]; (apply ro_bytes_at; [exact MI | vm_compute; discriminate | vm_compute; discriminate |]);
    apply ro_bytes_b_sound; vm_compute; reflexivity.
Qed.

Lemma hs_wr_sub : forall m a n a' n', wr_at rsegs m a n -> a <= a' -> a' + n' <= a + n -> wr_at rsegs m a' n'.
Proof.
  intros m a n a' n' (H1 & H2 & H) Ha Hn. split; [lia|]. split; [lia|].
  intros i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply H. lia.
Qed.

Lemma hs_rwc : forall m a bs n, bytes_at rsegs m a bs -> wr_at rsegs m a (Z.of_nat n) -> length bs = n ->
  rw_cells rsegs m a [CB n bs].
Proof. intros m a bs n B W L. subst n. apply rw_cells_of_u8arr. split; assumption. Qed.

Lemma hs_bsub : forall m a bs k n a', bytes_at rsegs m a bs -> 0 <= k -> k + Z.of_nat n <= Z.of_nat (length bs) ->
  a' = a + k -> bytes_at rsegs m a' (sub bs k n).
Proof. intros m a bs k n a' B Hk Hn ->. apply bytes_at_sub; assumption. Qed.

Lemma hs_sub_sub : forall (H : list byte) a n b k, 0 <= a -> 0 <= b -> b + Z.of_nat k <= Z.of_nat n ->
  sub (sub H a n) b k = sub H (a + b) k.
Proof.
  intros H a n b k Ha Hb Hk. unfold sub.
  rewrite skipn_firstn_comm, firstn_firstn, skipn_skipn.
  replace (Z.to_nat (a + b)) with (Z.to_nat b + Z.to_nat a)%nat by lia.
  f_equal. lia.
Qed.

Lemma hs_rd : forall m a (H : list byte) c len k n, bytes_at rsegs m (a + c) (sub H c len) ->
  0 <= c -> c + Z.of_nat len <= Z.of_nat (length H) -> c <= k -> k + Z.of_nat n <= c + Z.of_nat len ->
  ov_read_bytes rsegs m (Z_to_bv 64 (a + k)) n = Some (sub H k n).
Proof.
  intros m a H c len k n B Hc HL Hk Hn.
  pose proof (rd_sub m (a + c) (sub H c len) (k - c) n B ltac:(lia) ltac:(rewrite length_sub; lia)) as R.
  replace (a + c + (k - c)) with (a + k) in R by lia. rewrite R. f_equal.
  rewrite hs_sub_sub by lia. f_equal. lia.
Qed.

Lemma hs_bsub2 : forall m a (H : list byte) c len k n a', bytes_at rsegs m (a + c) (sub H c len) ->
  0 <= c -> c + Z.of_nat len <= Z.of_nat (length H) -> c <= k -> k + Z.of_nat n <= c + Z.of_nat len ->
  a' = a + k -> bytes_at rsegs m a' (sub H k n).
Proof.
  intros m a H c len k n a' B Hc HL Hk Hn ->.
  pose proof (hs_bsub m (a + c) (sub H c len) (k - c) n (a + k) B ltac:(lia) ltac:(rewrite length_sub; lia)
                ltac:(lia)) as R.
  rewrite hs_sub_sub in R by lia. replace (c + (k - c)) with k in R by lia. exact R.
Qed.

Lemma hs_rwc_b : forall m a n bs, rw_cells rsegs m a [CB n bs] -> bytes_at rsegs m a bs.
Proof. intros m a n bs R. apply u8arr_of_rw_cells in R. destruct R as [B _]. exact B. Qed.

Lemma hs_ld : forall bs, bv_extract 0 64 (le_bytes_to_word bs) = Z_to_bv 64 (bytes_le_to_Z bs).
Proof.
  intros bs. transitivity (le_bytes_to_word bs); [|reflexivity].
  apply bv_eq. rewrite bv_extract_unsigned, Z.shiftr_0_r. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma hs_le4_u : forall bs, length bs = 4%nat -> le4 (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof.
  intros bs L. pose proof (ble_range bs) as R. rewrite L in R. cbn in R. unfold le4.
  rewrite unsigned_lit by lia. rewrite <- L. apply Z_to_le_bytes_to_Z.
Qed.

Lemma hs_le8_u : forall bs, length bs = 8%nat -> le8 (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof.
  intros bs L. pose proof (ble_range bs) as R. rewrite L in R. cbn in R.
  rewrite <- store_bytes_8'. rewrite unsigned_lit by lia. rewrite <- L. apply Z_to_le_bytes_to_Z.
Qed.

Lemma hs_b1_u : forall bs, length bs = 1%nat -> [Z_to_bv 8 (bytes_le_to_Z bs)] = bs.
Proof.
  intros bs L. rewrite <- (Z_to_le_bytes_to_Z bs) at 2. rewrite L. reflexivity.
Qed.

Lemma hs_le4_s32 : forall bs, length bs = 4%nat -> le4 (Z_to_bv 64 (bv_swrap 32 (bytes_le_to_Z bs))) = bs.
Proof.
  intros bs L. apply le4_of_mod32; [exact L|]. rewrite <- bytes_le_to_Z_le_val.
  pose proof (ble_range bs) as R. rewrite L in R. cbn in R.
  rewrite unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 32) with 2147483648 by reflexivity.
  replace (bv_modulus 32) with 4294967296 by reflexivity.
  Z.div_mod_to_equations. lia.
Qed.

Lemma hs_eqb0 : forall v, -2^63 <= v < 2^63 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0).
Proof.
  intros v Hv. unfold bv_eqb. rewrite !unsigned_lit_wrap. change (0 mod 2^64) with 0.
  destruct (Z.eqb_spec v 0) as [->|N]; [reflexivity|].
  apply Z.eqb_neq. intros E. apply Z.mod_divide in E; [|lia]. destruct E as [c Ec]. nia.
Qed.

Lemma hs_swrap0 : forall c, 0 <= c < 2^32 -> (bv_swrap 32 c =? 0) = (c =? 0).
Proof.
  intros c Hc. unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 32) with 2147483648 by reflexivity.
  replace (bv_modulus 32) with 4294967296 by reflexivity.
  destruct (Z.eqb_spec c 0) as [->|N]; [reflexivity|]. apply Z.eqb_neq. Z.div_mod_to_equations. lia.
Qed.

Lemma hs_beqb : forall l r, bytes_eqb l r = true <-> l = r.
Proof.
  induction l as [|x l IH]; intros [|y r]; cbn; split; intros E; try discriminate; try reflexivity.
  - apply andb_prop in E. destruct E as [E1 E2]. apply Z.eqb_eq in E1. apply bv_eq in E1. apply IH in E2.
    subst. reflexivity.
  - inversion E. subst. apply andb_true_intro. split; [apply Z.eqb_refl | apply IH; reflexivity].
Qed.

Lemma hs_ex_idx : forall (f : Z -> bool) n,
  existsb f (map Z.of_nat (seq 0 (Z.to_nat n))) = true <-> exists j, 0 <= j < n /\ f j = true.
Proof.
  intros f n. rewrite existsb_exists. split.
  - intros (x & Hx & Fx). apply in_map_iff in Hx. destruct Hx as (k & <- & Hk). apply in_seq in Hk.
    exists (Z.of_nat k). split; [lia | exact Fx].
  - intros (j & Hj & Fj). exists j. split; [|exact Fj]. apply in_map_iff. exists (Z.to_nat j).
    split; [lia|]. apply in_seq. lia.
Qed.

Lemma hs_nex_idx : forall (f : Z -> bool) n, (forall j, 0 <= j < n -> f j = false) ->
  existsb f (map Z.of_nat (seq 0 (Z.to_nat n))) = false.
Proof.
  intros f n H. destruct (existsb f _) eqn:E; [|reflexivity].
  apply hs_ex_idx in E. destruct E as (j & Hj & Fj). rewrite H in Fj by exact Hj. discriminate.
Qed.

Lemma hs_best_range : forall t T P our now j, best t T P our now = Some j -> 0 <= j < n_of T.
Proof.
  intros t T P our now j E. unfold best in E.
  destruct (t =? 0); [discriminate|].
  destruct (cands T P our now) as [|j0 l] eqn:C; [discriminate|].
  apply find_some in E. destruct E as [Hin _]. rewrite <- C in Hin.
  unfold cands in Hin. apply filter_In in Hin. destruct Hin as [Hin _].
  apply in_map_iff in Hin. destruct Hin as (k & Ek & Hk). apply in_seq in Hk. lia.
Qed.

Lemma hs_len_arb : forall t our T P fsm pace now, length T = 400%nat -> length P = 6%nat -> tbl_T1 T ->
  length (arb_model t our T P fsm pace now) = 32%nat.
Proof.
  intros t our T P fsm pace now LT LP T1. unfold tbl_T1 in T1.
  unfold arb_model. cbv zeta.
  destruct (best t T P our now) as [j|] eqn:B.
  - pose proof (hs_best_range _ _ _ _ _ _ B) as Hj.
    assert (LM : length (mac_of T j) = 6%nat) by (unfold mac_of; apply length_sub; lia).
    repeat match goal with |- context [if ?c then _ else _] => destruct c end;
      unfold arb_bytes, z4, MAC0; rewrite !length_app, ?length_le4, ?repeat_length, ?LP, ?LM; reflexivity.
  - repeat match goal with |- context [if ?c then _ else _] => destruct c end;
      unfold arb_bytes, z4, MAC0; rewrite !length_app, ?length_le4, ?repeat_length, ?LP; reflexivity.
Qed.

Lemma hs_sk_range : forall e r d s c fs now, 0 <= reac_sender_kind_model e r d s c fs now <= 4.
Proof.
  intros. unfold reac_sender_kind_model, reac_rival_kind_model.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; lia.
Qed.

Lemma hs_dec_range : forall pinned pin st rv sil op v0 now dgl bp, 0 <= v0 <= 3 ->
  0 <= decide_model pinned pin st rv sil op v0 now dgl bp <= 3.
Proof. intros. unfold decide_model. repeat match goal with |- context [if ?c then _ else _] => destruct c end; lia. Qed.

Lemma hs_mv : forall m1 m2 a bs lo hi, bytes_at rsegs m1 a bs -> munch [(lo, hi)] m1 m2 ->
  a + Z.of_nat (length bs) <= lo \/ hi <= a -> bytes_at rsegs m2 a bs.
Proof.
  intros m1 m2 a bs lo hi B MU D. apply (bytes_at_transport rsegs [(lo, hi)] m1 m2 a bs B MU).
  cbn. split; [lia | exact I].
Qed.

Lemma hs_mw : forall m0 m1 m2 S h, munch [(S - 192, S); (h, h + 400); (h + 440, h + 476)] m0 m1 ->
  munch [(S + -192, S + -80)] m1 m2 -> munch [(S - 192, S); (h, h + 400); (h + 440, h + 476)] m0 m2.
Proof.
  intros m0 m1 m2 S h M1 M2. eapply munch_trans; [exact M1|]. eapply munch_weaken; [|exact M2].
  intros x Hx. cbn [outside] in *. destruct Hx as [Hx _]. split; [lia | exact I].
Qed.

Lemma hs_snez : forall v w, 0 <= v <= 3 -> 0 <= w <= 3 ->
  v_sltu (Z_to_bv 64 0) (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 v)) (bv_unsigned (Z_to_bv 64 w)))) =
  Z_to_bv 64 (if v =? w then 0 else 1).
Proof.
  intros v w Hv Hw.
  assert (Ev : v = 0 \/ v = 1 \/ v = 2 \/ v = 3) by lia. assert (Ew : w = 0 \/ w = 1 \/ w = 2 \/ w = 3) by lia.
  destruct Ev as [-> | [-> | [-> | ->]]]; destruct Ew as [-> | [-> | [-> | ->]]]; reflexivity.
Qed.

Lemma hs_seqz : forall p c, -2^62 <= p < 2^62 -> 0 <= c <= 4 ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (v_sltiu (Z_to_bv 64 p) 1) + c)) = Z_to_bv 64 (if p =? 0 then c + 1 else c).
Proof.
  intros p c Hp Hc. rewrite v_sltiu_b2z, (unsigned_lit_wrap p). change (bv_wrap 64 1) with 1.
  destruct (Z.eqb_spec p 0) as [->|N].
  - change (0 mod 2^64 <? 1) with true. cbn [Z.b2z]. rewrite unsigned_lit by lia. rewrite swrap32_small by lia.
    f_equal; lia.
  - replace (p mod 2^64 <? 1) with false.
    + cbn [Z.b2z]. rewrite unsigned_lit by lia. rewrite swrap32_small by lia. f_equal; lia.
    + symmetry. apply Z.ltb_ge. pose proof (Z.mod_pos_bound p (2^64) ltac:(lia)).
      destruct (Z.eq_dec (p mod 2^64) 0) as [E|E]; [|lia].
      apply Z.mod_divide in E; [|lia]. destruct E as [q Eq]. nia.
Qed.

Lemma hs_eqbk : forall v k, -2^63 <= v < 2^63 -> 0 <= k < 2^63 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 k) = (v =? k).
Proof.
  intros v k Hv Hk. unfold bv_eqb. rewrite !unsigned_lit_wrap. rewrite (Z.mod_small k) by lia.
  destruct (Z.eqb_spec v k) as [->|N]; [rewrite Z.mod_small by lia; apply Z.eqb_refl|]. apply Z.eqb_neq. intros E.
  destruct (Z_lt_le_dec v 0) as [L|L].
  - rewrite <- (Z.mod_add v 1 (2^64)) in E by lia. rewrite Z.mod_small in E by lia. lia.
  - rewrite Z.mod_small in E by lia. lia.
Qed.

Lemma hs_dm_pinned : forall pinned pin st rv sil op v0 now dgl bp, pinned <> 0 ->
  decide_model pinned pin st rv sil op v0 now dgl bp =
  if (pin =? 0) && (st =? 2) && (rv =? 2) then 2 else if pin =? 1 then 2 else 1.
Proof. intros. unfold decide_model. destruct (Z.eqb_spec pinned 0); [lia | reflexivity]. Qed.

Lemma hs_dm_unp : forall pin st rv sil op v0 now dgl bp,
  decide_model 0 pin st rv sil op v0 now dgl bp =
  if st =? 2 then (if rv =? 4 then v0 else if rv =? 3 then 3 else 2)
  else if dgl then 0 else if negb (sil =? 0) then 1
  else if (now - op) mod 2^64 <? REAC_HUNT_WINDOW_NS then 0 else if bp then 1 else 0.
Proof. reflexivity. Qed.

Definition hs_fd (h : Z) (T U : list byte) (now i : Z) : bool :=
  negb (disco_stale T i now) && negb (bytes_eqb (mac_of T i) U) && (role_of_e T i =? 0) &&
  negb (ch_of T i =? 0) && (hs_kind h T now i =? 3).

Definition hs_fb (h : Z) (T : list byte) (now i : Z) : bool :=
  negb (disco_stale T i now) && ((role_of_e T i =? 1) || ((role_of_e T i =? 0) && (hs_kind h T now i =? 2))).

Lemma hs_dgl_false : forall h T U now, (forall j, 0 <= j < n_of T -> hs_fd h T U now j = false) ->
  desk_geometry_live h T U now = false.
Proof. intros h T U now N. unfold desk_geometry_live, hs_idx. apply hs_nex_idx. exact N. Qed.

Lemma hs_dgl_true : forall h T U now i, 0 <= i < n_of T -> hs_fd h T U now i = true ->
  desk_geometry_live h T U now = true.
Proof. intros h T U now i Hi F. unfold desk_geometry_live, hs_idx. apply hs_ex_idx. exists i. split; assumption. Qed.

Lemma hs_bp_false : forall h T now, (forall j, 0 <= j < n_of T -> hs_fb h T now j = false) ->
  box_present h T now = false.
Proof. intros h T now N. unfold box_present, hs_idx. apply hs_nex_idx. exact N. Qed.

Lemma hs_bp_true : forall h T now i, 0 <= i < n_of T -> hs_fb h T now i = true -> box_present h T now = true.
Proof. intros h T now i Hi F. unfold box_present, hs_idx. apply hs_ex_idx. exists i. split; assumption. Qed.

Lemma hs_st1 : forall T i now, now <= last_of T i -> disco_stale T i now = false.
Proof.
  intros T i now L. unfold disco_stale. replace (last_of T i <? now) with false by (symmetry; apply Z.ltb_ge; lia).
  reflexivity.
Qed.

Lemma hs_st2 : forall T i now, last_of T i < now -> disco_stale T i now = (5000000000 <? now - last_of T i).
Proof.
  intros T i now L. unfold disco_stale. replace (last_of T i <? now) with true by (symmetry; apply Z.ltb_lt; lia).
  reflexivity.
Qed.

Lemma hs_entry : forall m h T i, bytes_at rsegs m h T -> length T = 400%nat -> 0 <= i -> 48 * i + 48 <= 400 ->
  -2^31 <= role_of_e T i < 2^31 /\ 0 <= hd_of T i < 2^8 /\ 0 <= slots_of T i < 2^8 /\ 0 <= ch_of T i < 2^32 /\
  0 <= fs_of T i < 2^64 /\
  bytes_at rsegs m (h + 48 * i + 8) (le4 (Z_to_bv 64 (role_of_e T i))) /\
  bytes_at rsegs m (h + 48 * i + 12) [Z_to_bv 8 (hd_of T i)] /\
  bytes_at rsegs m (h + 48 * i + 16) [Z_to_bv 8 (slots_of T i)] /\
  bytes_at rsegs m (h + 48 * i + 20) (le4 (Z_to_bv 64 (ch_of T i))) /\
  bytes_at rsegs m (h + 48 * i + 32) (le8 (Z_to_bv 64 (fs_of T i))).
Proof.
  intros m h T i B L Hi Hn.
  assert (R : forall k n, 0 <= k -> k + Z.of_nat n <= 400 -> 0 <= u_at T k n < 2 ^ (8 * Z.of_nat n)).
  { intros k n Hk Hkn. unfold u_at. pose proof (ble_range (sub T k n)) as R. rewrite length_sub in R by lia.
    exact R. }
  assert (BS : forall k n, 0 <= k -> k + Z.of_nat n <= 48 -> bytes_at rsegs m (h + 48 * i + k) (sub T (48 * i + k) n)).
  { intros k n Hk Hkn. replace (h + 48 * i + k) with (h + (48 * i + k)) by lia.
    apply bytes_at_sub; [exact B | lia | rewrite L; lia]. }
  split; [exact (s32_range T (48 * i + 8))|].
  split; [exact (R (48 * i + 12) 1%nat ltac:(lia) ltac:(lia))|].
  split; [exact (R (48 * i + 16) 1%nat ltac:(lia) ltac:(lia))|].
  split; [exact (R (48 * i + 20) 4%nat ltac:(lia) ltac:(lia))|].
  split; [exact (R (48 * i + 32) 8%nat ltac:(lia) ltac:(lia))|].
  split. { unfold role_of_e, s32_at, u_at. rewrite hs_le4_s32 by (apply length_sub; lia). apply BS; lia. }
  split. { unfold hd_of, u_at. rewrite hs_b1_u by (apply length_sub; lia). apply BS; lia. }
  split. { unfold slots_of, u_at. rewrite hs_b1_u by (apply length_sub; lia). apply BS; lia. }
  split. { unfold ch_of, u_at. rewrite hs_le4_u by (apply length_sub; lia). apply BS; lia. }
  unfold fs_of, u_at. rewrite hs_le8_u by (apply length_sub; lia). apply BS; lia.
Qed.

Lemma hs_mw2 : forall m0 m1 m2 S, munch [(S + -192, S + -80)] m0 m1 -> munch [(S + -80 - 112, S + -80)] m1 m2 ->
  munch [(S + -192, S + -80)] m0 m2.
Proof.
  intros m0 m1 m2 S M1 M2. eapply munch_trans; [exact M1|]. eapply munch_weaken; [|exact M2].
  intros x Hx. cbn [outside] in *. destruct Hx as [Hx _]. split; [lia | exact I].
Qed.

Lemma hs_hunt_ok : forall T' (H : list byte) v A, length T' = 400%nat -> length H = 480%nat -> length A = 32%nat ->
  0 <= v <= 3 -> table_ok T' -> lock_ok (firstn 12 (skipn 400 H)) ->
  hunt_ok (T' ++ sub H 400 40 ++ le4 (Z_to_bv 64 v) ++ A ++ skipn 476 H).
Proof.
  intros T' H v A LT LH LA Hv TOK LOK.
  assert (L1 : length (sub H 400 40) = 40%nat) by (apply length_sub; lia).
  assert (L2 : length (skipn 476 H) = 4%nat) by (rewrite length_skipn; lia).
  assert (E1 : skipn 400 (T' ++ sub H 400 40 ++ le4 (Z_to_bv 64 v) ++ A ++ skipn 476 H) =
               sub H 400 40 ++ le4 (Z_to_bv 64 v) ++ A ++ skipn 476 H) by (rewrite <- LT; apply skipn_app_exact).
  assert (E2 : skipn 440 (T' ++ sub H 400 40 ++ le4 (Z_to_bv 64 v) ++ A ++ skipn 476 H) =
               le4 (Z_to_bv 64 v) ++ A ++ skipn 476 H).
  { rewrite app_assoc. replace 440%nat with (length (T' ++ sub H 400 40)) by (rewrite length_app; lia).
    apply skipn_app_exact. }
  assert (E3 : sub (T' ++ sub H 400 40 ++ le4 (Z_to_bv 64 v) ++ A ++ skipn 476 H) 440 4 = le4 (Z_to_bv 64 v)).
  { unfold sub at 1. change (Z.to_nat 440) with 440%nat. rewrite E2.
    rewrite firstn_app, length_le4. change (4 - 4)%nat with 0%nat. rewrite firstn_O, app_nil_r.
    apply firstn_all2. rewrite length_le4. lia. }
  unfold hunt_ok. split; [|split; [|split]].
  - rewrite !length_app, LT, L1, length_le4, LA, L2. reflexivity.
  - rewrite <- LT, firstn_app_exact. exact TOK.
  - rewrite E1, firstn_app, L1. change (12 - 40)%nat with 0%nat. rewrite firstn_O, app_nil_r.
    unfold sub. rewrite firstn_firstn. exact LOK.
  - unfold s32_at, u_at. rewrite E3.
    rewrite bytes_le_to_Z_le4, unsigned_lit by lia. rewrite Z.mod_small by lia. rewrite swrap32_small by lia. lia.
Qed.

Lemma hs_assemble : forall m h T' Q B4 A R, bytes_at rsegs m h T' -> bytes_at rsegs m (h + 400) Q ->
  bytes_at rsegs m (h + 440) B4 -> bytes_at rsegs m (h + 444) A -> bytes_at rsegs m (h + 476) R ->
  length T' = 400%nat -> length Q = 40%nat -> length B4 = 4%nat -> length A = 32%nat -> length R = 4%nat ->
  wr_at rsegs m h 480 -> rw_cells rsegs m h [CB 480 (T' ++ Q ++ B4 ++ A ++ R)].
Proof.
  intros m h T' Q B4 A R B1 B2 B3 B5 B6 L1 L2 L3 L5 L6 W.
  apply hs_rwc; [| exact W | rewrite !length_app; lia].
  apply bytes_at_app. split; [exact B1|]. replace (h + Z.of_nat (length T')) with (h + 400) by lia.
  apply bytes_at_app. split; [exact B2|]. replace (h + 400 + Z.of_nat (length Q)) with (h + 440) by lia.
  apply bytes_at_app. split; [exact B3|]. replace (h + 440 + Z.of_nat (length B4)) with (h + 444) by lia.
  apply bytes_at_app. split; [exact B5|]. replace (h + 444 + Z.of_nat (length A)) with (h + 476) by lia.
  exact B6.
Qed.

Theorem reac_hunt_step_holds : reac_disco_table_age_contract -> reac_arbitrate_contract -> bcmp_contract ->
  reac_sender_kind_contract -> reac_hunt_step_contract.
Proof.
  intros AGE ARB BC SKC.
  unfold reac_hunt_step_contract, REAC_HUNT_STEP, REAC_HUNT_STEP_K.
  unfold reac_disco_table_age_contract, REAC_DISCO_TABLE_AGE, REAC_DISCO_TABLE_AGE_K in AGE.
  unfold reac_arbitrate_contract, REAC_ARBITRATE, REAC_ARBITRATE_K in ARB.
  unfold BCMP in BC. unfold reac_sender_kind_contract, REAC_SENDER_KIND in SKC.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo h now H -> -> Hnow Hh0 Hh8 RWH HOK S16 ST LO OW MI RTLO BRT B6 B3.
  clear BRT B6 B3.
  unfold off_window in OW.
  destruct HOK as (LH & TOK & LOK & V0R).
  pose proof (rw_cells_bound rsegs m h _ RWH) as HB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in HB.
  apply u8arr_of_rw_cells in RWH. destruct RWH as [BH WH]. rewrite LH in WH. change (Z.of_nat 480) with 480 in WH.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof ST as (Hlo & _ & _).
  pose proof (munch_refl [(bv_unsigned sp - 192, bv_unsigned sp); (h, h + 400); (h + 440, h + 476)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  assert (L400 : length (sub H 400 40) = 40%nat) by (apply length_sub; lia).
  assert (L440 : length (sub H 440 4) = 4%nat) by (apply length_sub; lia).
  assert (L476 : length (sub H 476 4) = 4%nat) by (apply length_sub; lia).
  assert (L444 : length (sub H 444 32) = 32%nat) by (apply length_sub; lia).
  assert (L412 : length (sub H 412 6) = 6%nat) by (apply length_sub; lia).
  pose proof (hs_bsub m h H 400 40 (h + 400) BH ltac:(lia) ltac:(rewrite LH; lia) eq_refl) as B400.
  pose proof (hs_bsub m h H 440 4 (h + 440) BH ltac:(lia) ltac:(rewrite LH; lia) eq_refl) as B440.
  pose proof (hs_bsub m h H 476 4 (h + 476) BH ltac:(lia) ltac:(rewrite LH; lia) eq_refl) as B476.
  pose proof (hs_bsub m h H 444 32 (h + 444) BH ltac:(lia) ltac:(rewrite LH; lia) eq_refl) as B444.
  pose proof (hs_rwc m h (sub H 0 400) 400 (hs_bsub m h H 0 400 h BH ltac:(lia) ltac:(rewrite LH; lia) ltac:(lia))
                (hs_wr_sub m h 480 h 400 WH ltac:(lia) ltac:(lia)) ltac:(apply length_sub; lia)) as RT0.
  clear BH.
  carve_frame 80%nat ST.
  do 13 step.
  rename m into mI. rename m0 into m1. rename MU into MU0. rename WM into WM0.
  lazymatch goal with HF : rw_cells _ m1 (bv_unsigned sp + -80) ?cs |- _ => set (FRC := cs) in HF; rename HF into FR end.
  assert (LFR : cells_size FRC = 80%nat) by reflexivity.
  assert (Hsp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) = bv_unsigned sp + -80) by (apply unsigned_lit; lia).
  eapply evt_cut.
  { eapply AGE with (t := h) (T := sub H 0 400) (lo := lo);
      [reflexivity | reflexivity | exact Hnow | lia | exact Hh8 | exact RT0 | apply length_sub; lia | exact TOK
      | exact MI | rewrite Hsp; exact ST | rewrite Hsp; lia | unfold off_window; rewrite Hsp; lia]. }
  intros ms' (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m2 & T' & rem &
              Eq & MUc & WMc & MI2 & ST2 & RT2 & AGEM & AGEP).
  subst ms'. rewrite Hsp in MUc, ST2.
  transport_after_call rsegs m1 m2 MUc WMc. clear MUc WMc MI. clear m1.
  rewrite (ret_pc_even 90220) by (first [lia | reflexivity]).
  pose proof AGEP as (LT' & _ & _ & _ & _ & _ & TOK' & _).
  pose proof TOK' as (T1' & T2' & T3' & T4'). unfold tbl_T1 in T1'.
  pose proof (hs_rwc_b m2 h 400 T' RT2) as BT2.
  pose proof (hs_bsub2 m2 h H 400 40 412 6 (h + 412) B400 ltac:(lia) ltac:(rewrite LH; lia) ltac:(lia) ltac:(lia) eq_refl)
    as BP2.
  do 9 step.
  eapply evt_cut.
  { eapply ARB with (t := h) (our := h + 412) (fsm := 0) (pace := 0) (now := now) (out := h + 444) (lo := lo)
      (T := T') (P := sub H 412 6);
      [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
      | lia | lia | lia | lia | exact Hnow | lia
      | rewrite Hsp; lia | rewrite Hsp; exact ST2 | rewrite Hsp; lia
      | intros _; unfold off_window; rewrite Hsp; refine (conj Hh8 (conj LT' (conj BT2 (conj TOK' (conj _ _))))); lia
      | intros _; unfold off_window; rewrite Hsp; refine (conj L412 (conj BP2 (conj _ _))); lia
      | lia | exact L444 | exact B444 | exact (hs_wr_sub m2 h 480 (h + 444) 32 WH ltac:(lia) ltac:(lia))
      | unfold off_window; rewrite Hsp; lia | exact MI2]. }
  intros ms' (y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m3 &
              Eq & MUc & WMc & MI3 & ST3 & BA & BT3 & BP3).
  subst ms'. rewrite Hsp in MUc, ST3.
  specialize (BT3 ltac:(lia)). specialize (BP3 ltac:(lia)).
  clear BT2 BP2 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31.
  transport_after_call rsegs m2 m3 MUc WMc. clear MUc WMc MI2 RT2. clear m2.
  rewrite (ret_pc_even 90256) by (first [lia | reflexivity]).
  set (A := arb_model h (h + 412) T' (sub H 412 6) 0 0 now) in BA.
  assert (LA : length A = 32%nat) by (apply hs_len_arb; assumption).
  assert (HT : hs_table H now = T') by (unfold hs_table; rewrite AGEM; reflexivity).
  assert (HA : hs_arb h H now = A) by (unfold hs_arb; rewrite HT; reflexivity).
  assert (HV0 : hs_verdict h H now =
    decide_model (s32_at H 432) (s32_at H 436) (s32_at A 0) (s32_at A 24) (s32_at H 420) (u_at H 424 8)
      (s32_at H 440) now (desk_geometry_live h T' (sub H 412 6) now) (box_present h T' now))
    by (unfold hs_verdict; rewrite HA, HT; reflexivity).
  assert (EPI : forall (m4 : word -> option byte) (F4 : bvmap 5 word) (v : Z)
                 (ra' x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word),
    munch [(bv_unsigned sp + -192, bv_unsigned sp + -80)] m3 m4 -> wmono rsegs m3 m4 ->
    stk rsegs m4 lo (bv_unsigned sp + -80) -> mem_inv rsegs m4 -> freg_kept F F4 ->
    v = hs_verdict h H now ->
    evt rsegs QQ (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp x5 x6 x7 (Z_to_bv 64 h) x9 (Z_to_bv 64 v)
                          x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
                     F4 (Z_to_bv 64 90304) fc None m4 (seg_rom rsegs))).
  { intros m4 F4 v q1 q5 q6 q7 q9 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q28 q29 q30 q31
      MU4 WM4 ST4 MI4 FK4 Hv.
    assert (VR : 0 <= v <= 3) by (subst v; apply hs_dec_range; exact V0R).
    pose proof (hs_mv m3 m4 _ _ _ _ B440 MU4 ltac:(lia)) as B440'.
    pose proof (hs_mv m3 m4 _ _ _ _ B400 MU4 ltac:(lia)) as B400'.
    pose proof (hs_mv m3 m4 _ _ _ _ B476 MU4 ltac:(lia)) as B476'.
    pose proof (hs_mv m3 m4 _ _ _ _ BA MU4 ltac:(lia)) as BA'.
    pose proof (hs_mv m3 m4 _ _ _ _ BT3 MU4 ltac:(lia)) as BT'.
    pose proof (rw_cells_transport rsegs _ m3 m4 _ _ FR MU4 WM4 ltac:(cbn [disjoint_from]; split; [lia | exact I]))
      as FR'.
    pose proof (wr_at_transport rsegs m3 m4 h 480 WH WM4) as WH'.
    pose proof (hs_mw mI m3 m4 _ _ MU0 MU4) as MU0'.
    pose proof (wmono_trans rsegs mI m3 m4 WM0 WM4) as WM0'.
    clear MU4 WM4.
    pose proof (hs_rd m4 h H 440 4 440 4 B440' ltac:(lia) ltac:(rewrite LH; lia) ltac:(lia) ltac:(lia)) as RD.
    step. rewrite lw_val by (apply length_sub; lia). clear RD.
    change (bv_swrap 32 (bytes_le_to_Z (sub H 440 4))) with (s32_at H 440).
    pose proof (wr_at_store_ok rsegs m4 h 480 440 4 WH' ltac:(lia) ltac:(lia)) as SO.
    step.
    pose proof (bytes_at_write_same rsegs m4 (h + 440) (le4 (Z_to_bv 64 v)) ltac:(lia) ltac:(rewrite length_le4; lia))
      as BV.
    store_done.
    step. step.
    rewrite hs_snez by lia.
    unfold FRC in FR'.
    do 9 step.
    release_frame FR' ST4 (bv_unsigned sp).
    do 2 step.
    subst v.
    assert (SK : skipn 476 H = sub H 476 4)
      by (unfold sub; rewrite firstn_all2 by (rewrite length_skipn; lia); reflexivity).
    apply evt_done. unfold QQ. do 14 eexists. exists F4. eexists. split; [reflexivity|].
    split; [exact FK4|]. split; [exact MU0'|]. split; [exact WM0'|]. split; [exact MI4|]. split; [exact ST4|].
    unfold hs_hunt. rewrite HT, HA. split.
    - rewrite SK. apply hs_assemble; first [assumption | apply length_le4].
    - apply hs_hunt_ok; assumption. }
  pose proof (hs_rd m3 h H 400 40 432 4 B400 ltac:(lia) ltac:(rewrite LH; lia) ltac:(lia) ltac:(lia)) as RD.
  step. rewrite lw_val by (apply length_sub; lia). clear RD.
  change (bv_swrap 32 (bytes_le_to_Z (sub H 432 4))) with (s32_at H 432).
  step.
  rewrite hs_eqb0 by (pose proof (s32_range H 432); lia).
  destruct (Z.eqb_spec (s32_at H 432) 0) as [P0|P1]; cbv iota.
  2: {
    pose proof (s32_range H 436) as R436.
    pose proof (hs_rd m3 h H 400 40 436 4 B400 ltac:(lia) ltac:(rewrite LH; lia) ltac:(lia) ltac:(lia)) as RD.
    step. rewrite lw_val by (apply length_sub; lia). clear RD.
    change (bv_swrap 32 (bytes_le_to_Z (sub H 436 4))) with (s32_at H 436).
    assert (PB : forall a0v a2v : word, (if s32_at H 436 + -1 =? 0 then 1 + 1 else 1) = hs_verdict h H now ->
      evt rsegs QQ (MS (mkR (Z_to_bv 64 90256) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp y5 y6 y7 (Z_to_bv 64 h)
                       (Z_to_bv 64 now) a0v (Z_to_bv 64 (s32_at H 436)) a2v y13 y14 y15 y16 y17
                       (Z_to_bv 64 (h + 412)) (Z_to_bv 64 (h + 444)) s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                     F (Z_to_bv 64 90292) fc None m3 (seg_rom rsegs))).
    { intros a0v a2v Hv. step. step. step.
      rewrite hs_seqz by lia.
      eapply EPI; [apply munch_refl | apply wmono_refl | exact ST3 | exact MI3 | apply hs_freg_refl | exact Hv]. }
    step.
    rewrite hs_eqb0 by lia.
    destruct (Z.eqb_spec (s32_at H 436) 0) as [Q0|Q1]; cbn [negb].
    - pose proof (rd_sub m3 (h + 444) A 0 4 BA ltac:(lia) ltac:(rewrite LA; lia)) as RD.
      step. rewrite lw_val by (apply length_sub; lia). clear RD.
      change (bv_swrap 32 (bytes_le_to_Z (sub A 0 4))) with (s32_at A 0).
      step. step.
      rewrite hs_eqbk by (pose proof (s32_range A 0); lia).
      destruct (Z.eqb_spec (s32_at A 0) 2) as [S2|S2]; cbn [negb].
      + pose proof (rd_sub m3 (h + 444) A 24 4 BA ltac:(lia) ltac:(rewrite LA; lia)) as RD.
        step. rewrite lw_val by (apply length_sub; lia). clear RD.
        change (bv_swrap 32 (bytes_le_to_Z (sub A 24 4))) with (s32_at A 24).
        step.
        rewrite hs_eqbk by (pose proof (s32_range A 24); lia).
        destruct (Z.eqb_spec (s32_at A 24) 2) as [R2|R2]; cbv iota.
        * eapply EPI; [apply munch_refl | apply wmono_refl | exact ST3 | exact MI3 | apply hs_freg_refl |].
          rewrite HV0, hs_dm_pinned by exact P1. rewrite Q0, S2, R2. reflexivity.
        * apply PB. rewrite HV0, hs_dm_pinned by exact P1. rewrite Q0, S2.
          replace (s32_at A 24 =? 2) with false by (symmetry; apply Z.eqb_neq; exact R2). reflexivity.
      + apply PB. rewrite HV0, hs_dm_pinned by exact P1. rewrite Q0.
        replace (s32_at A 0 =? 2) with false by (symmetry; apply Z.eqb_neq; exact S2). reflexivity.
    - apply PB. rewrite HV0, hs_dm_pinned by exact P1.
      replace (s32_at H 436 =? 0) with false by (symmetry; apply Z.eqb_neq; exact Q1). cbn [andb].
      destruct (Z.eqb_spec (s32_at H 436) 1) as [Q2|Q2].
      + rewrite Q2. reflexivity.
      + replace (s32_at H 436 + -1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
  pose proof (rd_sub m3 (h + 444) A 0 4 BA ltac:(lia) ltac:(rewrite LA; lia)) as RD.
  step. rewrite lw_val by (apply length_sub; lia). clear RD.
  change (bv_swrap 32 (bytes_le_to_Z (sub A 0 4))) with (s32_at A 0).
  step. step.
  rewrite hs_eqbk by (pose proof (s32_range A 0); lia).
  destruct (Z.eqb_spec (s32_at A 0) 2) as [S2|S2]; cbn [negb].
  { pose proof (rd_sub m3 (h + 444) A 24 4 BA ltac:(lia) ltac:(rewrite LA; lia)) as RD.
    step. rewrite lw_val by (apply length_sub; lia). clear RD.
    change (bv_swrap 32 (bytes_le_to_Z (sub A 24 4))) with (s32_at A 24).
    step. step.
    rewrite hs_eqbk by (pose proof (s32_range A 24); lia).
    destruct (Z.eqb_spec (s32_at A 24) 4) as [R4|R4]; cbn [negb].
    - pose proof (hs_rd m3 h H 440 4 440 4 B440 ltac:(lia) ltac:(rewrite LH; lia) ltac:(lia) ltac:(lia)) as RD.
      step. rewrite lw_val by (apply length_sub; lia). clear RD.
      change (bv_swrap 32 (bytes_le_to_Z (sub H 440 4))) with (s32_at H 440).
      step.
      eapply EPI; [apply munch_refl | apply wmono_refl | exact ST3 | exact MI3 | apply hs_freg_refl |].
      rewrite HV0, P0, hs_dm_unp, S2, R4. reflexivity.
    - step. step. step. step.
      rewrite hs_seqz by (pose proof (s32_range A 24); lia).
      eapply EPI; [apply munch_refl | apply wmono_refl | exact ST3 | exact MI3 | apply hs_freg_refl |].
      rewrite HV0, P0, hs_dm_unp, S2.
      replace (s32_at A 24 =? 4) with false by (symmetry; apply Z.eqb_neq; exact R4).
      destruct (Z.eqb_spec (s32_at A 24) 3) as [R3|R3].
      + rewrite R3. reflexivity.
      + replace (s32_at A 24 + -3 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
  pose proof (rd_sub m3 h T' 384 4 BT3 ltac:(lia) ltac:(rewrite LT'; lia)) as RD.
  step. rewrite lw_val by (apply length_sub; lia). clear RD.
  change (bv_swrap 32 (bytes_le_to_Z (sub T' 384 4))) with (n_of T') in *.
  set (n := n_of T') in *.
  set (U := sub H 412 6) in *.
  assert (POSTD : forall (m4 : word -> option byte) (F4 : bvmap 5 word)
                   (ra' x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x28 x29 x30 x31 : word),
    desk_geometry_live h T' U now = false ->
    munch [(bv_unsigned sp + -192, bv_unsigned sp + -80)] m3 m4 -> wmono rsegs m3 m4 ->
    stk rsegs m4 lo (bv_unsigned sp + -80) -> mem_inv rsegs m4 -> freg_kept F F4 ->
    evt rsegs QQ (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp x5 x6 x7 (Z_to_bv 64 h) (Z_to_bv 64 now)
                          x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 n) x21 x22 x23 s8 s9 s10 s11
                          x28 x29 x30 x31)
                     F4 (Z_to_bv 64 90516) fc None m4 (seg_rom rsegs))).
  { intros m4 F4 ra' x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x28 x29 x30 x31
      DGL MU4 WM4 ST4 MI4 FK4.
    pose proof (hs_mv m3 m4 _ _ _ _ B400 MU4 ltac:(lia)) as B4.
    pose proof (hs_rd m4 h H 400 40 420 4 B4 ltac:(lia) ltac:(rewrite LH; lia) ltac:(lia) ltac:(lia)) as RD.
    step. rewrite lw_val by (apply length_sub; lia). clear RD.
    change (bv_swrap 32 (bytes_le_to_Z (sub H 420 4))) with (s32_at H 420).
    step.
    rewrite hs_eqb0 by (pose proof (s32_range H 420); lia).
    destruct (Z.eqb_spec (s32_at H 420) 0) as [SL0|SL1]; cbv iota.
    2: { step. step.
         eapply EPI; [exact MU4 | exact WM4 | exact ST4 | exact MI4 | exact FK4 |].
         rewrite HV0, P0, hs_dm_unp. replace (s32_at A 0 =? 2) with false by (symmetry; apply Z.eqb_neq; exact S2).
         rewrite DGL. replace (s32_at H 420 =? 0) with false by (symmetry; apply Z.eqb_neq; exact SL1).
         reflexivity. }
    pose proof (hs_rd m4 h H 400 40 424 8 B4 ltac:(lia) ltac:(rewrite LH; lia) ltac:(lia) ltac:(lia)) as RD.
    step. rewrite hs_ld. clear RD.
    change (bytes_le_to_Z (sub H 424 8)) with (u_at H 424 8).
    do 6 step.
    assert (OPR : 0 <= u_at H 424 8 < 2^64).
    { unfold u_at. pose proof (ble_range (sub H 424 8)) as R. rewrite length_sub in R by lia. exact R. }
    assert (WCE : bv_ltu (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 now) - bv_unsigned (Z_to_bv 64 (u_at H 424 8))))
                    (Z_to_bv 64 3000000000) = ((now - u_at H 424 8) mod 2^64 <? REAC_HUNT_WINDOW_NS)).
    { unfold bv_ltu. rewrite (unsigned_lit now), (unsigned_lit (u_at H 424 8)) by lia.
      rewrite !unsigned_lit_wrap. reflexivity. }
    rewrite WCE.
    destruct ((now - u_at H 424 8) mod 2^64 <? REAC_HUNT_WINDOW_NS) eqn:WC; cbv iota.
    { eapply EPI; [exact MU4 | exact WM4 | exact ST4 | exact MI4 | exact FK4 |].
      rewrite HV0, P0, hs_dm_unp. replace (s32_at A 0 =? 2) with false by (symmetry; apply Z.eqb_neq; exact S2).
      rewrite DGL, SL0, WC. reflexivity. }
    step.
    rewrite lts_lit by lia.
    destruct (Z.ltb_spec 0 n) as [Hn|Hn]; cbn [negb].
    2: { eapply EPI; [exact MU4 | exact WM4 | exact ST4 | exact MI4 | exact FK4 |].
         rewrite HV0, P0, hs_dm_unp. replace (s32_at A 0 =? 2) with false by (symmetry; apply Z.eqb_neq; exact S2).
         rewrite DGL, SL0, WC. rewrite (hs_bp_false h T' now). { reflexivity. }
         intros j Hj. change (n_of T') with n in Hj. lia. }
    assert (LOOPB : forall k i (m5 : word -> option byte) (F5 : bvmap 5 word)
                     (rb z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 : word),
      Z.of_nat k = n - i -> 0 <= i < n -> (forall j, 0 <= j < i -> hs_fb h T' now j = false) ->
      munch [(bv_unsigned sp + -192, bv_unsigned sp + -80)] m3 m5 -> wmono rsegs m3 m5 ->
      stk rsegs m5 lo (bv_unsigned sp + -80) -> mem_inv rsegs m5 -> freg_kept F F5 ->
      evt rsegs QQ (MS (mkR rb (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp z5 z6 z7 (Z_to_bv 64 h) (Z_to_bv 64 now)
                            z10 z11 z12 z13 z14 z15 z16 z17 (Z_to_bv 64 (h + 48 * i)) (Z_to_bv 64 i)
                            (Z_to_bv 64 n) (Z_to_bv 64 2) (Z_to_bv 64 5000000000) (Z_to_bv 64 1) s8 s9 s10 s11
                            z28 z29 z30 z31)
                       F5 (Z_to_bv 64 90608) fc None m5 (seg_rom rsegs))).
    { induction k as [|k IH];
        intros i m5 F5 rb z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 Hk Hi NW MU5 WM5 ST5 MI5 FK5;
        [lia|].
      pose proof (hs_mv m3 m5 _ _ _ _ BT3 MU5 ltac:(lia)) as BT5.
      assert (BPV1 : hs_fb h T' now i = true -> 1 = hs_verdict h H now).
      { intros FBT. rewrite HV0, P0, hs_dm_unp.
        replace (s32_at A 0 =? 2) with false by (symmetry; apply Z.eqb_neq; exact S2).
        rewrite DGL, SL0, WC. rewrite (hs_bp_true h T' now i ltac:(change (n_of T') with n; lia) FBT). reflexivity. }
      assert (NEXTB : forall (m6 : word -> option byte) (F6 : bvmap 5 word)
                        (rc c5 c6 c7 c10 c11 c12 c13 c14 c15 c16 c17 c28 c29 c30 c31 : word),
        hs_fb h T' now i = false ->
        munch [(bv_unsigned sp + -192, bv_unsigned sp + -80)] m3 m6 -> wmono rsegs m3 m6 ->
        stk rsegs m6 lo (bv_unsigned sp + -80) -> mem_inv rsegs m6 -> freg_kept F F6 ->
        evt rsegs QQ (MS (mkR rc (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp c5 c6 c7 (Z_to_bv 64 h) (Z_to_bv 64 now)
                              c10 c11 c12 c13 c14 c15 c16 c17 (Z_to_bv 64 (h + 48 * i)) (Z_to_bv 64 i)
                              (Z_to_bv 64 n) (Z_to_bv 64 2) (Z_to_bv 64 5000000000) (Z_to_bv 64 1) s8 s9 s10 s11
                              c28 c29 c30 c31)
                         F6 (Z_to_bv 64 90664) fc None m6 (seg_rom rsegs))).
      { intros m6 F6 rc c5 c6 c7 c10 c11 c12 c13 c14 c15 c16 c17 c28 c29 c30 c31 FB MU6 WM6 ST6 MI6 FK6.
        step. step. step.
        rewrite lts_lit by lia.
        destruct (Z.ltb_spec (i + 1) n) as [Lt|Ge]; cbv iota.
        - replace (h + 48 * i + 48) with (h + 48 * (i + 1)) by lia.
          apply (IH (i + 1)); try assumption; try lia.
          intros j Hj. destruct (Z.eq_dec j i) as [->|Ji]; [exact FB|]. apply NW. lia.
        - step. step.
          eapply EPI; [exact MU6 | exact WM6 | exact ST6 | exact MI6 | exact FK6 |].
          rewrite HV0, P0, hs_dm_unp. replace (s32_at A 0 =? 2) with false by (symmetry; apply Z.eqb_neq; exact S2).
          rewrite DGL, SL0, WC. rewrite (hs_bp_false h T' now). { reflexivity. }
          intros j Hj. change (n_of T') with n in Hj.
          destruct (Z.eq_dec j i) as [->|Ji]; [exact FB|]. apply NW. lia. }
      assert (LIVEB : forall a0v : word, disco_stale T' i now = false ->
        evt rsegs QQ (MS (mkR rb (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp z5 z6 z7 (Z_to_bv 64 h) (Z_to_bv 64 now)
                              a0v z11 z12 z13 z14 z15 z16 z17 (Z_to_bv 64 (h + 48 * i)) (Z_to_bv 64 i)
                              (Z_to_bv 64 n) (Z_to_bv 64 2) (Z_to_bv 64 5000000000) (Z_to_bv 64 1) s8 s9 s10 s11
                              z28 z29 z30 z31)
                         F5 (Z_to_bv 64 90624) fc None m5 (seg_rom rsegs))).
      { intros a0v NS.
        pose proof (rd_sub m5 h T' (48 * i + 8) 4 BT5 ltac:(lia) ltac:(rewrite LT'; lia)) as RD.
        step. rewrite lw_val by (apply length_sub; lia). clear RD.
        change (bv_swrap 32 (bytes_le_to_Z (sub T' (48 * i + 8) 4))) with (role_of_e T' i).
        pose proof (T2' i ltac:(change (n_of T') with n; lia)) as RL.
        step.
        rewrite hs_eqb0 by lia.
        destruct (Z.eqb_spec (role_of_e T' i) 0) as [RL0|RL1]; cbv iota.
        - do 4 step.
          pose proof (hs_entry m5 h T' i BT5 LT' ltac:(lia) ltac:(lia)) as EF.
          pose proof (hs_ro m5 MI5) as (RO1 & RO2 & RO3).
          eapply evt_cut.
          { eapply SKC with (e := h + 48 * i) (fps := 0) (r := role_of_e T' i) (d := hd_of T' i) (s := slots_of T' i)
              (c := ch_of T' i) (fs := fs_of T' i) (lo := lo);
              [reflexivity | lia | lia | reflexivity | exact Hnow | reflexivity | lia | intros _; exact EF
              | rewrite Hsp; exact ST5 | rewrite Hsp; lia | exact RTLO | exact RO1 | exact RO2 | exact RO3]. }
          clear RO1 RO2 RO3 EF.
          intros ms' (b1 & b2 & b3 & b4 & b5 & F6 & m6 & Eq & MUc & WMc & ST6 & FK6).
          subst ms'. rewrite Hsp in MUc, ST6.
          pose proof (hs_mi_stack m5 m6 lo (bv_unsigned sp + -80) 112 MI5 ST5 ltac:(lia) MUc) as MI6.
          pose proof (hs_freg_trans F F5 F6 FK5 FK6) as FK6'.
          transport_after_call rsegs m5 m6 MUc WMc. clear MUc WMc MI5.
          rewrite (ret_pc_even 90656) by (first [lia | reflexivity]).
          change (reac_sender_kind_model (h + 48 * i) (role_of_e T' i) (hd_of T' i) (slots_of T' i) (ch_of T' i)
                    (fs_of T' i) now) with (hs_kind h T' now i).
          pose proof (hs_sk_range (h + 48 * i) (role_of_e T' i) (hd_of T' i) (slots_of T' i) (ch_of T' i)
                        (fs_of T' i) now) as KR.
          change (reac_sender_kind_model (h + 48 * i) (role_of_e T' i) (hd_of T' i) (slots_of T' i) (ch_of T' i)
                    (fs_of T' i) now) with (hs_kind h T' now i) in KR.
          step.
          rewrite eqb_lit by lia.
          destruct (Z.eqb_spec (hs_kind h T' now i) 2) as [K2|K2]; cbv iota.
          + step. step.
            eapply EPI; [exact MU5 | exact WM5 | exact ST6 | exact MI6 | exact FK6' |].
            apply BPV1. unfold hs_fb. rewrite NS, RL0, K2. reflexivity.
          + pose proof (rd_sub m6 h T' 384 4 BT5 ltac:(lia) ltac:(rewrite LT'; lia)) as RD.
            step. rewrite lw_val by (apply length_sub; lia). clear RD.
            change (bv_swrap 32 (bytes_le_to_Z (sub T' 384 4))) with n.
            apply NEXTB; try assumption.
            unfold hs_fb. rewrite NS, RL0.
            replace (hs_kind h T' now i =? 2) with false by (symmetry; apply Z.eqb_neq; exact K2). reflexivity.
        - step.
          rewrite hs_eqbk by lia.
          destruct (Z.eqb_spec (role_of_e T' i) 1) as [R1|R1]; cbv iota.
          + rewrite R1.
            eapply EPI; [exact MU5 | exact WM5 | exact ST5 | exact MI5 | exact FK5 |].
            apply BPV1. unfold hs_fb. rewrite NS, R1. reflexivity.
          + step.
            apply NEXTB; try assumption.
            unfold hs_fb. rewrite NS. replace (role_of_e T' i =? 1) with false by (symmetry; apply Z.eqb_neq; exact R1).
            replace (role_of_e T' i =? 0) with false by (symmetry; apply Z.eqb_neq; exact RL1). reflexivity. }
      pose proof (rd_sub m5 h T' (48 * i + 40) 8 BT5 ltac:(lia) ltac:(rewrite LT'; lia)) as RD.
      step. rewrite hs_ld. clear RD.
      change (bytes_le_to_Z (sub T' (48 * i + 40) 8)) with (last_of T' i).
      assert (LR : 0 <= last_of T' i < 2^64).
      { unfold last_of, u_at. pose proof (ble_range (sub T' (48 * i + 40) 8)) as R. rewrite length_sub in R by lia.
        exact R. }
      step.
      rewrite ltu_lit by lia.
      destruct (Z.ltb_spec (last_of T' i) now) as [LL|LG]; cbn [negb].
      2: { apply LIVEB. apply hs_st1. lia. }
      step. step.
      rewrite (unsigned_lit now) by lia. rewrite (unsigned_lit (last_of T' i)) by lia.
      rewrite ltu_lit by lia.
      destruct (Z.ltb_spec 5000000000 (now - last_of T' i)) as [SS|SN]; cbv iota.
      + apply NEXTB; try assumption. unfold hs_fb. rewrite (hs_st2 T' i now LL).
        replace (5000000000 <? now - last_of T' i) with true by (symmetry; apply Z.ltb_lt; exact SS). reflexivity.
      + apply LIVEB. rewrite (hs_st2 T' i now LL). apply Z.ltb_ge. exact SN. }
    do 7 step.
    pose proof (LOOPB (Z.to_nat n) 0) as L0. rewrite Z.mul_0_r, Z.add_0_r in L0.
    eapply L0; [lia | lia | intros j Hj; lia | exact MU4 | exact WM4 | exact ST4 | exact MI4 | exact FK4]. }
  assert (LOOPD : forall k i (m4 : word -> option byte) (F4 : bvmap 5 word)
                   (ra' x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    Z.of_nat k = n - i -> 0 <= i < n -> (forall j, 0 <= j < i -> hs_fd h T' U now j = false) ->
    munch [(bv_unsigned sp + -192, bv_unsigned sp + -80)] m3 m4 -> wmono rsegs m3 m4 ->
    stk rsegs m4 lo (bv_unsigned sp + -80) -> mem_inv rsegs m4 -> freg_kept F F4 ->
    evt rsegs QQ (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp x5 x6 x7 (Z_to_bv 64 h) (Z_to_bv 64 now)
                          x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (h + 412)) (Z_to_bv 64 (h + 48 * i))
                          (Z_to_bv 64 n) (Z_to_bv 64 i) (Z_to_bv 64 5000000000) (Z_to_bv 64 3) s8 s9 s10 s11
                          x28 x29 x30 x31)
                     F4 (Z_to_bv 64 90428) fc None m4 (seg_rom rsegs))).
  { induction k as [|k IH];
      intros i m4 F4 ra' x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 Hk Hi NW MU4 WM4 ST4 MI4 FK4;
      [lia|].
    pose proof (hs_mv m3 m4 _ _ _ _ BT3 MU4 ltac:(lia)) as BT4.
    pose proof (hs_mv m3 m4 _ _ _ _ BP3 MU4 ltac:(lia)) as BP4.
    assert (NEXT : forall (m5 : word -> option byte) (F5 : bvmap 5 word)
                     (rb z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 : word),
      hs_fd h T' U now i = false ->
      munch [(bv_unsigned sp + -192, bv_unsigned sp + -80)] m3 m5 -> wmono rsegs m3 m5 ->
      stk rsegs m5 lo (bv_unsigned sp + -80) -> mem_inv rsegs m5 -> freg_kept F F5 ->
      evt rsegs QQ (MS (mkR rb (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp z5 z6 z7 (Z_to_bv 64 h) (Z_to_bv 64 now)
                            z10 z11 z12 z13 z14 z15 z16 z17 (Z_to_bv 64 (h + 412)) (Z_to_bv 64 (h + 48 * i))
                            (Z_to_bv 64 n) (Z_to_bv 64 i) (Z_to_bv 64 5000000000) (Z_to_bv 64 3) s8 s9 s10 s11
                            z28 z29 z30 z31)
                       F5 (Z_to_bv 64 90504) fc None m5 (seg_rom rsegs))).
    { intros m5 F5 rb z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 FD MU5 WM5 ST5 MI5 FK5.
      step. step. step.
      rewrite lts_lit by lia.
      destruct (Z.ltb_spec (i + 1) n) as [Lt|Ge]; cbv iota.
      - replace (h + 48 * i + 48) with (h + 48 * (i + 1)) by lia.
        apply (IH (i + 1)); try assumption; try lia.
        intros j Hj. destruct (Z.eq_dec j i) as [->|Ji]; [exact FD|]. apply NW. lia.
      - apply POSTD; try assumption.
        apply hs_dgl_false. intros j Hj. change (n_of T') with n in Hj.
        destruct (Z.eq_dec j i) as [->|Ji]; [exact FD|]. apply NW. lia. }
    assert (LIVE : forall a0v : word, disco_stale T' i now = false ->
      evt rsegs QQ (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp x5 x6 x7 (Z_to_bv 64 h) (Z_to_bv 64 now)
                            a0v x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (h + 412)) (Z_to_bv 64 (h + 48 * i))
                            (Z_to_bv 64 n) (Z_to_bv 64 i) (Z_to_bv 64 5000000000) (Z_to_bv 64 3) s8 s9 s10 s11
                            x28 x29 x30 x31)
                       F4 (Z_to_bv 64 90444) fc None m4 (seg_rom rsegs))).
    { intros a0v NS.
      do 4 step.
      destruct (memcmp6 (mac_of T' i) U ltac:(unfold mac_of; apply length_sub; lia) L412) as (v & Hv & Veq & Vr).
      eapply evt_cut.
      { eapply BC with (ls := mac_of T' i) (rs := U) (v := v).
        - rewrite unsigned_lit by lia. unfold mac_of. apply bytes_at_sub; [exact BT4 | lia | rewrite LT'; lia].
        - rewrite unsigned_lit by lia. exact BP4.
        - exact Hv.
        - exact MI4. }
      post_call rsegs m4.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m5 end.
      lazymatch goal with HM : mem_inv rsegs m5 |- _ => rename HM into MI5 end.
      step.
      rewrite eqb_small by exact Vr.
      destruct (Z.eqb_spec v 0) as [V0|V1]; cbv iota.
      { apply NEXT; try assumption.
        unfold hs_fd. rewrite NS.
        replace (bytes_eqb (mac_of T' i) U) with true by (symmetry; apply hs_beqb; apply Veq; exact V0).
        reflexivity. }
      pose proof (rd_sub m5 h T' (48 * i + 8) 4 BT4 ltac:(lia) ltac:(rewrite LT'; lia)) as RD.
      step. rewrite lw_val by (apply length_sub; lia). clear RD.
      change (bv_swrap 32 (bytes_le_to_Z (sub T' (48 * i + 8) 4))) with (role_of_e T' i).
      step.
      rewrite hs_eqb0 by (pose proof (s32_range T' (48 * i + 8)); unfold role_of_e; lia).
      destruct (Z.eqb_spec (role_of_e T' i) 0) as [RL0|RL1]; cbn [negb].
      2: { apply NEXT; try assumption.
           unfold hs_fd. rewrite NS. replace (role_of_e T' i =? 0) with false by (symmetry; apply Z.eqb_neq; exact RL1).
           destruct (bytes_eqb (mac_of T' i) U); reflexivity. }
      pose proof (rd_sub m5 h T' (48 * i + 20) 4 BT4 ltac:(lia) ltac:(rewrite LT'; lia)) as RD.
      step. rewrite lw_val by (apply length_sub; lia). clear RD.
      change (bv_swrap 32 (bytes_le_to_Z (sub T' (48 * i + 20) 4))) with (s32_at T' (48 * i + 20)).
      step.
      rewrite hs_eqb0 by (pose proof (s32_range T' (48 * i + 20)); lia).
      assert (CH : (s32_at T' (48 * i + 20) =? 0) = (ch_of T' i =? 0)).
      { unfold s32_at, ch_of. apply hs_swrap0. unfold u_at.
        pose proof (ble_range (sub T' (48 * i + 20) 4)) as R. rewrite length_sub in R by lia. exact R. }
      rewrite CH.
      destruct (Z.eqb_spec (ch_of T' i) 0) as [C0|C1]; cbv iota.
      { apply NEXT; try assumption.
        unfold hs_fd. rewrite NS, RL0. replace (ch_of T' i =? 0) with true by (symmetry; apply Z.eqb_eq; exact C0).
        destruct (bytes_eqb (mac_of T' i) U); reflexivity. }
      do 4 step.
      pose proof (hs_entry m5 h T' i BT4 LT' ltac:(lia) ltac:(lia)) as EF.
      pose proof (hs_ro m5 MI5) as (RO1 & RO2 & RO3).
      eapply evt_cut.
      { eapply SKC with (e := h + 48 * i) (fps := 0) (r := role_of_e T' i) (d := hd_of T' i) (s := slots_of T' i)
          (c := ch_of T' i) (fs := fs_of T' i) (lo := lo);
          [reflexivity | lia | lia | reflexivity | exact Hnow | reflexivity | lia | intros _; exact EF
          | rewrite Hsp; exact ST4 | rewrite Hsp; lia | exact RTLO | exact RO1 | exact RO2 | exact RO3]. }
      clear RO1 RO2 RO3 EF.
      intros ms' (b1 & b2 & b3 & b4 & b5 & F6 & m6 & Eq & MUc & WMc & ST6 & FK6).
      subst ms'. rewrite Hsp in MUc, ST6.
      pose proof (hs_mi_stack m5 m6 lo (bv_unsigned sp + -80) 112 MI5 ST4 ltac:(lia) MUc) as MI6.
      pose proof (hs_freg_trans F F4 F6 FK4 FK6) as FK6'.
      transport_after_call rsegs m5 m6 MUc WMc. clear MUc WMc MI5.
      rewrite (ret_pc_even 90496) by (first [lia | reflexivity]).
      change (reac_sender_kind_model (h + 48 * i) (role_of_e T' i) (hd_of T' i) (slots_of T' i) (ch_of T' i)
                (fs_of T' i) now) with (hs_kind h T' now i).
      pose proof (hs_sk_range (h + 48 * i) (role_of_e T' i) (hd_of T' i) (slots_of T' i) (ch_of T' i) (fs_of T' i) now)
        as KR.
      change (reac_sender_kind_model (h + 48 * i) (role_of_e T' i) (hd_of T' i) (slots_of T' i) (ch_of T' i)
                (fs_of T' i) now) with (hs_kind h T' now i) in KR.
      step.
      rewrite eqb_lit by lia.
      destruct (Z.eqb_spec (hs_kind h T' now i) 3) as [K3|K3]; cbv iota.
      - step. step.
        assert (FDT : hs_fd h T' U now i = true).
        { unfold hs_fd. rewrite NS, RL0, K3. replace (ch_of T' i =? 0) with false by (symmetry; apply Z.eqb_neq; exact C1).
          replace (bytes_eqb (mac_of T' i) U) with false; [reflexivity|].
          symmetry. destruct (bytes_eqb (mac_of T' i) U) eqn:EB; [|reflexivity].
          apply hs_beqb in EB. exfalso. apply V1. apply Veq. exact EB. }
        eapply EPI; [exact MU4 | exact WM4 | exact ST6 | exact MI6 | exact FK6' |].
        rewrite HV0, P0, hs_dm_unp. replace (s32_at A 0 =? 2) with false by (symmetry; apply Z.eqb_neq; exact S2).
        rewrite (hs_dgl_true h T' U now i ltac:(change (n_of T') with n; lia) FDT). reflexivity.
      - pose proof (rd_sub m6 h T' 384 4 BT4 ltac:(lia) ltac:(rewrite LT'; lia)) as RD.
        step. rewrite lw_val by (apply length_sub; lia). clear RD.
        change (bv_swrap 32 (bytes_le_to_Z (sub T' 384 4))) with n.
        apply NEXT; try assumption.
        unfold hs_fd. replace (hs_kind h T' now i =? 3) with false by (symmetry; apply Z.eqb_neq; exact K3).
        destruct (negb (disco_stale T' i now) && negb (bytes_eqb (mac_of T' i) U) && (role_of_e T' i =? 0) &&
                  negb (ch_of T' i =? 0)); reflexivity. }
    pose proof (rd_sub m4 h T' (48 * i + 40) 8 BT4 ltac:(lia) ltac:(rewrite LT'; lia)) as RD.
    step. rewrite hs_ld. clear RD.
    change (bytes_le_to_Z (sub T' (48 * i + 40) 8)) with (last_of T' i).
    assert (LR : 0 <= last_of T' i < 2^64).
    { unfold last_of, u_at. pose proof (ble_range (sub T' (48 * i + 40) 8)) as R. rewrite length_sub in R by lia.
      exact R. }
    step.
    rewrite ltu_lit by lia.
    destruct (Z.ltb_spec (last_of T' i) now) as [LL|LG]; cbn [negb].
    2: { apply LIVE. apply hs_st1. lia. }
    step. step.
    rewrite (unsigned_lit now) by lia. rewrite (unsigned_lit (last_of T' i)) by lia.
    rewrite ltu_lit by lia.
    destruct (Z.ltb_spec 5000000000 (now - last_of T' i)) as [SS|SN]; cbv iota.
    + apply NEXT; try assumption. unfold hs_fd. rewrite (hs_st2 T' i now LL).
      replace (5000000000 <? now - last_of T' i) with true by (symmetry; apply Z.ltb_lt; exact SS). reflexivity.
    + apply LIVE. rewrite (hs_st2 T' i now LL). apply Z.ltb_ge. exact SN. }
  step.
  rewrite lts_lit by lia.
  destruct (Z.ltb_spec 0 n) as [Hn|Hn]; cbn [negb].
  - do 6 step.
    pose proof (LOOPD (Z.to_nat n) 0) as L0. rewrite Z.mul_0_r, Z.add_0_r in L0.
    eapply L0; [lia | lia | intros j Hj; lia | apply munch_refl | apply wmono_refl | exact ST3 | exact MI3
               | apply hs_freg_refl].
  - eapply POSTD; [ | apply munch_refl | apply wmono_refl | exact ST3 | exact MI3 | apply hs_freg_refl].
    apply hs_dgl_false. intros j Hj. change (n_of T') with n in Hj. lia.
Qed.
