(* Pure lemmas about the model's frame, announce and notice checks (TCb.v, TSess.v, TSess0.v) that the rx
   simulation (ops 0/1/2/8) uses: memcmp of 6 bytes, find_mac against host_offset, desk_named's prefix,
   check_state_desk / check_state_data on the notices the library makes, check_inflight_acked,
   check_state_online, and the length of an announce field. No world (upd / sub) algebra. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TNeed TSess0 TCb TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Import Agree Links.
Import ListNotations.
Open Scope Z_scope.

(* ---- list helpers ---- *)

Lemma rx_firstn_le_eq : forall {A} (l1 l2 : list A) m k, firstn m l1 = firstn m l2 -> (k <= m)%nat ->
  firstn k l1 = firstn k l2.
Proof.
  intros A l1 l2 m k E H. rewrite <- (Nat.min_l k m H), <- !firstn_firstn, E. reflexivity.
Qed.

Lemma rx_firstn_skipn_window : forall {A} (l1 l2 : list A) n m N, firstn N l1 = firstn N l2 ->
  (n + m <= N)%nat -> firstn m (skipn n l1) = firstn m (skipn n l2).
Proof.
  intros A l1 l2 n m N E H. rewrite !firstn_skipn_comm. f_equal. apply (rx_firstn_le_eq _ _ N); assumption.
Qed.

Lemma rx_firstn_skipn_firstn : forall {A} (l : list A) o k nn, (o + k <= nn)%nat ->
  firstn k (skipn o (firstn nn l)) = firstn k (skipn o l).
Proof.
  intros A l o k nn H. rewrite !firstn_skipn_comm, firstn_firstn, Nat.min_l by lia. reflexivity.
Qed.

(* ---- bytes, strings and fields ---- *)

Lemma rx_beq_bytes_refl : forall l, beq_bytes l l = true.
Proof.
  intros l. unfold beq_bytes. destruct (list_eq_dec Z.eq_dec (zs l) (zs l)); [reflexivity|contradiction].
Qed.

Lemma rx_strz_len_length : forall s, (strz_len s <= length s)%nat.
Proof.
  intros s. unfold strz_len. pose proof (nz_run_le (firstn 9 s)) as H. rewrite length_firstn in H. lia.
Qed.

Lemma rx_list_strz_len_some : forall r, (9 <= length r)%nat -> list_strz_len r = Some (strz_len r).
Proof.
  intros r H. unfold list_strz_len. cbv zeta.
  destruct (Nat.ltb_spec (length r) (Nat.min 9 (S (strz_len r)))); [lia|reflexivity].
Qed.

Lemma ann_field_len : forall src, length (ann_field src) = S (copy_len 10 9 src).
Proof.
  intros src. unfold ann_field. rewrite length_app, length_firstn. cbn [length].
  change (copy_len 10 9 src) with (strz_len src). pose proof (rx_strz_len_length src). lia.
Qed.

Lemma rx_ann_field_len_strz : forall s, length (ann_field s) = S (strz_len s).
Proof. intros s. exact (ann_field_len s). Qed.

Lemma rx_ann_field_prefix : forall s, firstn (strz_len s) (ann_field s) = firstn (strz_len s) s.
Proof.
  intros s. unfold ann_field. change (copy_len 10 9 s) with (strz_len s). pose proof (rx_strz_len_length s) as L.
  rewrite firstn_app, firstn_firstn, Nat.min_id, length_firstn.
  replace (strz_len s - Nat.min (strz_len s) (length s))%nat with O by lia.
  rewrite app_nil_r. reflexivity.
Qed.

Lemma rx_ann_field_nth : forall s, nth (strz_len s) (ann_field s) (b8 0) = b8 0.
Proof.
  intros s. unfold ann_field. change (copy_len 10 9 s) with (strz_len s). pose proof (rx_strz_len_length s) as L.
  rewrite app_nth2 by (rewrite length_firstn; lia). rewrite length_firstn.
  replace (strz_len s - Nat.min (strz_len s) (length s))%nat with O by lia. reflexivity.
Qed.

Lemma rx_leb_S_n : forall k, (S k <=? k)%nat = false.
Proof. intros k. apply Nat.leb_gt. lia. Qed.

Lemma rx_truth_b8_0 : truth (bz (b8 0)) = false.
Proof. unfold truth. rewrite bz_b8 by lia. reflexivity. Qed.

(* ---- memcmp of 6 bytes ---- *)

Lemma rx_memeq_firstn : forall n x y, memeq n x y = memeq n (firstn n x) y.
Proof.
  intros n x y. unfold memeq.
  assert (G : forall l, (forall i, In i l -> (i < n)%nat) ->
    forallb (fun i => at8 x i =? at8 y i) l = forallb (fun i => at8 (firstn n x) i =? at8 y i) l).
  { induction l as [|i l IH]; intros Hl; cbn [forallb]; [reflexivity|].
    rewrite at8_firstn by (apply Hl; left; reflexivity).
    rewrite IH by (intros j Hj; apply Hl; right; exact Hj). reflexivity. }
  apply G. intros i Hi. apply in_seq in Hi. lia.
Qed.

(* memcmp of 6 bytes: the library's memeq and the harness's beq_bytes *)
Lemma memeq6_beq : forall x y : list byte,
  length x = 6%nat -> length y = 6%nat -> memeq 6 x y = beq_bytes x y.
Proof.
  intros x y Hx Hy.
  destruct x as [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 [|x6 x]]]]]]]; cbn in Hx; try lia.
  destruct y as [|y0 [|y1 [|y2 [|y3 [|y4 [|y5 [|y6 y]]]]]]]; cbn in Hy; try lia.
  unfold memeq, beq_bytes, zs, at8, bz. cbn [seq forallb nth map].
  destruct (list_eq_dec Z.eq_dec _ _) as [E|E].
  - injection E as E0 E1 E2 E3 E4 E5. rewrite E0, E1, E2, E3, E4, E5, !Z.eqb_refl. reflexivity.
  - destruct (Z.eqb_spec (bv_unsigned x0) (bv_unsigned y0)); [|reflexivity].
    destruct (Z.eqb_spec (bv_unsigned x1) (bv_unsigned y1)); [|reflexivity].
    destruct (Z.eqb_spec (bv_unsigned x2) (bv_unsigned y2)); [|reflexivity].
    destruct (Z.eqb_spec (bv_unsigned x3) (bv_unsigned y3)); [|reflexivity].
    destruct (Z.eqb_spec (bv_unsigned x4) (bv_unsigned y4)); [|reflexivity].
    destruct (Z.eqb_spec (bv_unsigned x5) (bv_unsigned y5)); [|reflexivity].
    exfalso. apply E. congruence.
Qed.

(* find_mac (DS:168-174) over the library's announce and host_offset (FT:256-262) over the model's body *)
Lemma find_mac_host_offset : forall body1 body2 : list byte,
  (15 <= length body1)%nat -> (15 <= length body2)%nat -> firstn 15 body1 = firstn 15 body2 ->
  host_offset_loop 10 body1 0 = Some (find_mac_m (ann_unknown body2) 15 HOST).
Proof.
  intros body1 body2 H1 H2 E.
  assert (HL6 : length HOST = 6%nat) by reflexivity.
  assert (G : forall fuel i, 0 <= i -> i + Z.of_nat fuel = 10 ->
    host_offset_loop fuel body1 i = Some (find_mac_loop (firstn 15 body2) HOST i fuel)).
  { induction fuel as [|fuel IH]; intros i Hi Hf; cbn [host_offset_loop find_mac_loop]; [reflexivity|].
    unfold SPEC_MAC, SPEC_ANN_UNKNOWN.
    destruct (Z.leb_spec (i + 6) 15); [|lia].
    destruct (Z.ltb_spec (Z.of_nat (length body1)) (i + 6)); [lia|].
    assert (Ew : memeq 6 (skipn (Z.to_nat i) (firstn 15 body2)) HOST = beq_bytes (sub body1 i 6) HOST).
    { rewrite rx_memeq_firstn, <- memeq6_beq.
      - unfold sub. f_equal.
        rewrite <- E, !firstn_skipn_comm, firstn_firstn, Nat.min_l by lia. reflexivity.
      - unfold sub. rewrite length_firstn, length_skipn. lia.
      - exact HL6. }
    rewrite Ew. destruct (beq_bytes (sub body1 i 6) HOST); [reflexivity|].
    apply IH; lia. }
  unfold find_mac_m, ann_unknown. change (Z.to_nat (15 - DIGINET_MAC_LEN + 1)) with 10%nat.
  apply G; lia.
Qed.

(* desk_named_m reads only the 33 first bytes of rest *)
Lemma desk_named_prefix : forall I B1 B2 r1 r2,
  (33 <= length r1)%nat -> (33 <= length r2)%nat -> firstn 33 r1 = firstn 33 r2 ->
  option_map snd (desk_named_m I B1 r1) = option_map snd (desk_named_m I B2 r2).
Proof.
  intros I B1 B2 r1 r2 H1 H2 E.
  assert (E9 : firstn 9 (skipn 24 r1) = firstn 9 (skipn 24 r2)).
  { apply (rx_firstn_skipn_window _ _ 24 9 33); [exact E|lia]. }
  assert (S9 : strz_len (skipn 24 r1) = strz_len (skipn 24 r2)) by (unfold strz_len; rewrite E9; reflexivity).
  assert (F9 : firstn (strz_len (skipn 24 r2)) (skipn 24 r1) = firstn (strz_len (skipn 24 r2)) (skipn 24 r2)).
  { apply (rx_firstn_le_eq _ _ 9); [exact E9|apply strz_len_le]. }
  unfold desk_named_m. change (Z.to_nat SPEC_ANN_NAME) with 24%nat. cbv zeta.
  rewrite !rx_list_strz_len_some by (rewrite length_skipn; lia).
  cbv beta iota. rewrite S9, F9.
  destruct (_ && _); [reflexivity|]. destruct (_ && _); reflexivity.
Qed.

(* ---- reads of the heap frame ---- *)

Lemma rx_frame_strz_len_at : forall a bytes (o : nat) p, p = a + Z.of_nat o -> (o + 9 <= length bytes)%nat ->
  frame_strz_len (Some (TFrame a bytes)) p = Some (strz_len (skipn o bytes)).
Proof.
  intros a bytes o p -> H. unfold frame_strz_len. cbn [tf_addr tf_bytes].
  replace (a + Z.of_nat o - a) with (Z.of_nat o) by lia.
  destruct (Z.ltb_spec (Z.of_nat o) 0); [lia|].
  rewrite Nat2Z.id. apply rx_list_strz_len_some. rewrite length_skipn. lia.
Qed.

Lemma rx_frame_read_at : forall a bytes (o k : nat) p, p = a + Z.of_nat o -> (o + k <= length bytes)%nat ->
  frame_read (Some (TFrame a bytes)) p (Z.of_nat k) = Some (firstn k (skipn o bytes)).
Proof.
  intros a bytes o k p -> H. unfold frame_read. cbn [tf_addr tf_bytes].
  destruct (Z.eqb_spec (Z.of_nat k) 0) as [E|E].
  - replace k with O by lia. reflexivity.
  - replace (a + Z.of_nat o - a) with (Z.of_nat o) by lia.
    destruct (Z.ltb_spec (Z.of_nat o) 0); [lia|].
    destruct (Z.ltb_spec (Z.of_nat k) 0); [lia|].
    destruct (Z.ltb_spec (Z.of_nat (length bytes)) (Z.of_nat o + Z.of_nat k)); [lia|].
    cbn [orb]. unfold sub. rewrite !Nat2Z.id. reflexivity.
Qed.

Lemma rx_frame_read_at_Z : forall a bytes (o : nat) (n p : Z), p = a + Z.of_nat o -> 0 <= n ->
  (o + Z.to_nat n <= length bytes)%nat ->
  frame_read (Some (TFrame a bytes)) p n = Some (firstn (Z.to_nat n) (skipn o bytes)).
Proof.
  intros a bytes o n p Hp Hn Hk. pose proof (rx_frame_read_at a bytes o (Z.to_nat n) p Hp Hk) as R.
  rewrite Z2Nat.id in R by exact Hn. exact R.
Qed.

(* the body the library parses from the first nn bytes of the block is the bytes at 30 of the block *)
Lemma rx_fr_body_firstn : forall bytes nn, (nn <= length bytes)%nat -> fr_code (firstn nn bytes) = DIGINET_OK ->
  fr_body (firstn nn bytes) = firstn (Z.to_nat (fr_body_len (firstn nn bytes))) (skipn 30 bytes).
Proof.
  intros bytes nn Hnn Hc. destruct (fr_body_len_ok _ Hc) as (H0 & H1 & H2). rewrite length_firstn in H2.
  unfold fr_body. apply rx_firstn_skipn_firstn. lia.
Qed.

(* ---- the checks ---- *)

(* check_state_desk (FT:527-557) on the N_DESK notice on_announce makes (DS:196-198), m_rx having run on the
   same heap frame. bytes = the heap block, buf = its first nn bytes (the library's view). *)
Lemma check_state_desk_ok : forall (HL : links) I B (a : Z) (bytes : list byte) (nn : nat) st dp,
  timg_ok I -> (nn <= length bytes)%nat ->
  let buf := firstn nn bytes in
  fr_code buf = DIGINET_OK -> ann_cmd (fr_cmd buf) = true -> 33 <= fr_body_len buf ->
  let body := fr_body buf in
  let ann := TAnn (ann_field (skipn 15 body)) (ann_field (skipn 24 body)) in
  let name := skipn 24 body in
  let p := diginet_personality_from_name (firstn (copy_len 10 9 name) name) in
  let pv := match p with Some i => ti_personalities I + 24 * i | None => 0 end in
  let off := if fr_cmd buf =? DIGINET_CMD_ANNOUNCE_SESSION then find_mac_m (ann_unknown body) 15 HOST else -1 in
  GOT_desk B <= OW_desk B -> OW_desk_off B = off ->
  option_map snd (desk_named_m I B (skipn 30 bytes)) = Some dp -> OW_desk_p B = dp ->
  0 < a -> OW_desk_body B = a + 30 ->
  check_state_desk_m I (Some (TFrame a bytes)) B (Ntc DIGINET_N_DESK st 0 0 0 0 off pv (Some ann) [] 0) = Some (B, tt).
Proof.
  intros HL I B a bytes nn st dp HI Hnn. cbv zeta.
  intros Hcode _ Hblen Hgot Hoff Hdn Hdp Ha Hdb.
  assert (Ha0 : (a + 30 =? 0) = false) by (apply Z.eqb_neq; lia).
  destruct HL as (_ & _ & _ & _ & HL5 & _).
  pose proof (rx_fr_body_firstn bytes nn Hnn Hcode) as Ebody.
  destruct (fr_body_len_ok _ Hcode) as (Hb0 & Hp0 & Hlen). rewrite length_firstn in Hlen.
  pose proof (length_fr_body _ Hcode) as Lbody.
  set (buf := firstn nn bytes) in *. clearbody buf.
  set (body := fr_body buf) in *. clearbody body.
  assert (Lb33 : (33 <= length body)%nat) by lia.
  assert (Lby : (63 <= length bytes)%nat) by lia.
  assert (F33 : firstn 33 body = firstn 33 (skipn 30 bytes)).
  { rewrite Ebody, firstn_firstn, Nat.min_l by lia. reflexivity. }
  (* the desk desk_named names and the personality, through L5 *)
  assert (Hrest : SPEC_ANN_MIN <= Z.of_nat (length body)) by (unfold SPEC_ANN_MIN; lia).
  pose proof (HL5 I B body Hrest) as H5. cbv zeta in H5.
  destruct H5 as (dp' & Hdn' & Hp).
  assert (Edp : dp' = dp).
  { pose proof (desk_named_prefix I B B body (skipn 30 bytes) Lb33 ltac:(rewrite length_skipn; lia) F33) as E.
    rewrite Hdn, Hdn' in E. cbn in E. congruence. }
  subst dp'.
  change (Z.to_nat SPEC_ANN_NAME) with 24%nat in Hp.
  (* the version and the name: the block's bytes at 45 and 54 are the body's at 15 and 24 *)
  assert (W : forall X, (X + 9 <= 33)%nat -> firstn 9 (skipn X body) = firstn 9 (skipn (X + 30) bytes)).
  { intros X HX. rewrite <- skipn_skipn. apply (rx_firstn_skipn_window _ _ X 9 33); [exact F33|exact HX]. }
  pose proof (W 15%nat ltac:(lia)) as W15. pose proof (W 24%nat ltac:(lia)) as W24.
  cbn [Nat.add] in W15, W24.
  assert (K1 : strz_len (skipn 45 bytes) = strz_len (skipn 15 body)) by (unfold strz_len; rewrite W15; reflexivity).
  assert (K2 : strz_len (skipn 54 bytes) = strz_len (skipn 24 body)) by (unfold strz_len; rewrite W24; reflexivity).
  assert (P1 : firstn (strz_len (skipn 15 body)) (skipn 45 bytes) = firstn (strz_len (skipn 15 body)) (skipn 15 body)).
  { symmetry. apply (rx_firstn_le_eq _ _ 9); [exact W15|apply strz_len_le]. }
  assert (P2 : firstn (strz_len (skipn 24 body)) (skipn 54 bytes) = firstn (strz_len (skipn 24 body)) (skipn 24 body)).
  { symmetry. apply (rx_firstn_le_eq _ _ 9); [exact W24|apply strz_len_le]. }
  pose proof (strz_len_le (skipn 45 bytes)) as Z45. pose proof (strz_len_le (skipn 54 bytes)) as Z54.
  rewrite <- Hoff.
  revert Hp. destruct (diginet_personality_from_name _) as [i|] eqn:Ep; intros Hp.
  all: unfold check_state_desk_m; cbn [n_pers n_mac_offset n_ann ta_version ta_name].
  all: rewrite Hdp, Hdb, Z.eqb_refl, Ha0.
  all: destruct (Z.ltb_spec (OW_desk B) (GOT_desk B)); [lia|].
  (* goal 1, personalities[i]: desk_named names the desk with its device and strips *)
  destruct Hp as (pp & d & Hpa & Hcase & Hdev & Hst).
  destruct (ti_personalities_ok I HI) as (Hpers & _).
  pose proof (ti_spec_c24_ok I HI) as Hc24. pose proof (ti_spec_pc_ok I HI) as Hpc.
  pose proof (ti_c24_pc I HI) as Hne.
  assert (Hpv : (ti_personalities I + 24 * i =? 0) = false).
  { apply Z.eqb_neq. destruct Hcase as [(-> & _) | (-> & _)]; lia. }
  assert (Hpp : personality_ptr I (ti_personalities I + 24 * i) = Some pp).
  { unfold personality_ptr. replace (ti_personalities I + 24 * i - ti_personalities I) with (24 * i) by lia.
    destruct Hcase as [(-> & _) | (-> & _)]; exact Hpa. }
  assert (Hdesk : spec_desk_at I dp = Some d).
  { unfold spec_desk_at. destruct Hcase as [(_ & -> & ->) | (_ & -> & ->)].
    - rewrite Z.eqb_refl. reflexivity.
    - rewrite (proj2 (Z.eqb_neq (ti_spec_pc I) (ti_spec_c24 I))) by congruence.
      rewrite Z.eqb_refl. reflexivity. }
  assert (Hdp0 : (dp =? 0) = false).
  { apply Z.eqb_neq. destruct Hcase as [(_ & -> & _) | (_ & -> & _)]; lia. }
  rewrite Hpv, Hdp0, Hpp, Hdesk. cbn [Bool.eqb negb orb].
  rewrite Hdev, Hst, !Z.eqb_refl. cbn [negb orb].
  (* goal 2, no personality: desk_named is NULL *)
  2: (rewrite Hp; cbn [Bool.eqb negb orb Z.eqb]).
  (* both: the version and the name the notice carries are the strings at body + 15 and body + 24 *)
  all: unfold SPEC_ANN_VERSION, SPEC_ANN_NAME.
  all: rewrite (rx_frame_strz_len_at a bytes 45 (a + 30 + 15)) by lia.
  all: rewrite (rx_frame_strz_len_at a bytes 54 (a + 30 + 24)) by lia.
  all: cbv beta iota.
  all: rewrite (rx_frame_read_at a bytes 45 (strz_len (skipn 45 bytes)) (a + 30 + 15)) by lia.
  all: rewrite (rx_frame_read_at a bytes 54 (strz_len (skipn 54 bytes)) (a + 30 + 24)) by lia.
  all: cbv beta iota.
  all: rewrite K1, K2, P1, P2.
  all: rewrite !rx_ann_field_prefix, !rx_beq_bytes_refl, !rx_ann_field_len_strz, !rx_leb_S_n,
         !rx_ann_field_nth, !rx_truth_b8_0.
  all: reflexivity.
Qed.

(* check_state_data (FT:559-569) on the N_DATA notice on_data makes (DS:257-260) *)
Lemma check_state_data_ok : forall (HL : links) B (a : Z) (bytes : list byte) (nn : nat) st g,
  (nn <= length bytes)%nat ->
  let buf := firstn nn bytes in
  fr_code buf = DIGINET_OK ->
  GOT_ndata B = g -> 0 <= g < 2 -> g < OW_ndata B ->
  OW_dn_len B g = fr_body_len buf -> OW_dn_body B g = a + 30 ->
  OW_dn_counter B g = fr_send buf -> OW_dn_retry B g = fr_retry buf ->
  check_state_data_m (Some (TFrame a bytes)) B
    (Ntc DIGINET_N_DATA st 0 0 (fr_send buf) (fr_retry buf) 0 0 None (fr_body buf) (fr_body_len buf)) = Some (B, tt).
Proof.
  intros _ B a bytes nn st g Hnn. cbv zeta.
  intros Hcode Hg Hg2 Hgo Hlen Hbody Hctr Hret.
  pose proof (rx_fr_body_firstn bytes nn Hnn Hcode) as Ebody.
  destruct (fr_body_len_ok _ Hcode) as (Hb0 & Hp0 & Hl). rewrite length_firstn in Hl.
  pose proof (length_fr_body _ Hcode) as Lbody.
  set (buf := firstn nn bytes) in *. clearbody buf.
  unfold check_state_data_m. cbn [n_body_len n_body n_counter n_retry].
  rewrite Hg, Hlen, Hbody, Hctr, Hret, !Z.eqb_refl.
  destruct (Z.leb_spec (OW_ndata B) g); [lia|].
  destruct (Z.leb_spec 2 g); [lia|].
  destruct (Z.ltb_spec g 0); [lia|].
  cbn [orb negb].
  rewrite (rx_frame_read_at_Z a bytes 30 (fr_body_len buf) (a + 30)) by lia.
  rewrite <- Ebody. cbv beta iota.
  destruct (Z.ltb_spec (Z.of_nat (length (fr_body buf))) (fr_body_len buf)); [lia|].
  rewrite firstn_all2 by lia. rewrite rx_beq_bytes_refl. reflexivity.
Qed.

(* check_inflight_acked (FT:476-484) on the N_ACKED notice on_ack makes (DS:230-232) *)
Lemma check_inflight_acked_ok : forall B n, GOT_acked B <= OW_acked B ->
  n_counter n = OW_acked_counter B -> n_retry n = OW_acked_retry B -> check_inflight_acked_m B n = Some (B, tt).
Proof.
  intros B n H Hc Hr. unfold check_inflight_acked_m. rewrite Hc, Hr, !Z.eqb_refl.
  destruct (Z.ltb_spec (OW_acked B) (GOT_acked B)); [lia|]. reflexivity.
Qed.

(* check_state_online (FT:497-505) *)
Lemma check_state_online_ok : forall B, M_e2_acked B = 1 -> M_e1_us B = 1 -> check_state_online_m B = Some (B, tt).
Proof. intros B H1 H2. unfold check_state_online_m, truth. rewrite H1, H2. reflexivity. Qed.
