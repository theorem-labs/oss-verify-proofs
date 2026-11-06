From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import RcModel RcLeaf RcParse CtrlParsed disco_classify_c disco_table_c disco_table.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_frame_clean_len_c reac_disco_table_observe_c reac_disco_table_observe.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import hunt_c reac_hunt_observe_c HuntObsLib.
Import ListNotations.
Open Scope Z_scope.

Lemma le4_lw : forall bs, length bs = 4%nat -> le4 (Z_to_bv 64 (bv_swrap 32 (bytes_le_to_Z bs))) = bs.
Proof.
  intros bs L. apply le4_of_mod32; [exact L|]. rewrite <- bytes_le_to_Z_le_val.
  pose proof (ble_range bs) as R. rewrite L in R. cbn in R.
  rewrite unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 32) with 2147483648 by reflexivity.
  replace (bv_modulus 32) with 4294967296 by reflexivity.
  Z.div_mod_to_equations. lia.
Qed.

Lemma fb0_eq : forall FR, (50 <= length FR)%nat -> firstn 50 (FR ++ repeat (zb 0) 50) = firstn 50 FR.
Proof.
  intros FR H. rewrite firstn_app. replace (50 - length FR)%nat with 0%nat by lia. cbn [firstn]. apply app_nil_r.
Qed.

Lemma cm_pad : forall FR L U Lo, (50 <= L -> (50 <= length FR)%nat) ->
  cm_ret (firstn 50 (FR ++ repeat (zb 0) 50)) L U Lo = cm_ret (firstn 50 FR) L U Lo /\
  (forall OB, cm_out (firstn 50 (FR ++ repeat (zb 0) 50)) L U Lo OB = cm_out (firstn 50 FR) L U Lo OB) /\
  cm_lock (firstn 50 (FR ++ repeat (zb 0) 50)) L U Lo = cm_lock (firstn 50 FR) L U Lo.
Proof.
  intros FR L U Lo H.
  assert (E : classify_model (firstn 50 (FR ++ repeat (zb 0) 50)) L U Lo = classify_model (firstn 50 FR) L U Lo).
  { destruct (Z.leb_spec 50 L) as [HL|HL].
    - rewrite fb0_eq by (apply H; exact HL). reflexivity.
    - unfold classify_model, dkind, ctrlparse, cp_hdr.
      replace (50 <=? L) with false by (symmetry; apply Z.leb_gt; exact HL). reflexivity. }
  unfold cm_ret, cm_out, cm_lock. rewrite E. split; [reflexivity|]. split; reflexivity.
Qed.

Lemma ho_out_cells : forall m out T G i b16,
  length T = 400%nat -> length G = 24%nat -> 0 <= i < 8 -> sub T (48 * i + 16) 1 = [b16] ->
  rw_cells rsegs m out
    [CB 8 (firstn 8 G);
     C4 (Z_to_bv 64 (bv_swrap 32 (bytes_le_to_Z (sub T (48 * i + 8) 4))));
     C4 (Z_to_bv 64 (bv_swrap 32 (bytes_le_to_Z (sub T (48 * i + 12) 4))));
     C1 b16; CB 3 (firstn 3 (skipn 1 (skipn 4 (skipn 12 G))));
     C4 (Z_to_bv 64 (bv_swrap 32 (bytes_le_to_Z (sub T (48 * i + 20) 4))))] ->
  rw_cells rsegs m out [CB 24 (ho_entry T G i)].
Proof.
  intros m out T G i b16 LT LG Hi E16 R. apply rwc_flat in R.
  cbn [cells_size csize Nat.add] in R. cbn [cells_bytes cbytes] in R.
  rewrite !le4_lw in R by (apply len_sub; lia).
  unfold ho_entry. replace 9%nat with (4 + (4 + 1))%nat by reflexivity.
  rewrite !sub_split by lia. rewrite <- E16 in R.
  replace (48 * i + 8 + Z.of_nat 4) with (48 * i + 12) in * by lia.
  replace (48 * i + 12 + Z.of_nat 4) with (48 * i + 16) in * by lia.
  rewrite !skipn_skipn in R. rewrite app_nil_r in R. cbn [Nat.add] in R.
  rewrite <- !app_assoc. exact R.
Qed.

Lemma sub_mid : forall (A B C : list byte) k n, length A = k -> length B = n ->
  sub (A ++ B ++ C) (Z.of_nat k) n = B.
Proof.
  intros A B C k n HA HB. subst k n. unfold sub. rewrite Nat2Z.id, skipn_app, skipn_all2 by lia.
  rewrite Nat.sub_diag, skipn_O. cbn [app]. rewrite firstn_app, Nat.sub_diag, firstn_all, firstn_O.
  apply app_nil_r.
Qed.

Lemma sub_end : forall (A B : list byte) k n, length A = k -> length B = n -> sub (A ++ B) (Z.of_nat k) n = B.
Proof.
  intros A B k n HA HB. subst k n. unfold sub. rewrite Nat2Z.id, skipn_app, skipn_all2 by lia.
  rewrite Nat.sub_diag, skipn_O. cbn [app]. apply firstn_all.
Qed.

Lemma sight_fields : forall F len, length F = 50%nat ->
  sub (sight F len) 0 6 = src F /\
  sub (sight F len) 8 4 = le4 (Z_to_bv 64 (role F (dkind F len))) /\
  sub (sight F len) 12 3 =
    (match sdecl F with Some (i, o) => [zb 1; zb i; zb o] | None => [zb 0; zb 0; zb 0] end) /\
  sub (sight F len) 20 4 = le4 (Z_to_bv 64 (geo len)).
Proof.
  intros F len HF. pose proof (len_src F HF) as LS. unfold sight.
  destruct (sdecl F) as [[a b]|]; cbv beta iota; (split; [|split; [|split]]).
  all: first
    [ rewrite sub_app_l by (try rewrite LS; lia); apply sub_whole; exact LS
    | rewrite app_assoc; change 8 with (Z.of_nat 8);
      apply sub_mid; [rewrite length_app, LS; reflexivity | apply length_le4]
    | rewrite app_assoc, app_assoc; change 12 with (Z.of_nat 12);
      apply sub_mid; [rewrite !length_app, LS, length_le4; reflexivity | reflexivity]
    | rewrite !app_assoc; change 20 with (Z.of_nat 20);
      apply sub_end; [rewrite !length_app, LS, length_le4; reflexivity | apply length_le4] ].
Qed.

Lemma role_rng : forall F k, 0 <= role F k <= 2.
Proof. intros F k. unfold role. repeat match goal with |- context [if ?c then _ else _] => destruct c end; lia. Qed.

Lemma geo_rng : forall len, 0 <= geo len < 2^32.
Proof.
  intros len. unfold geo. destruct (_ && _); [apply Z.mod_pos_bound; lia | lia].
Qed.

Lemma cnt_nn : forall f bs k, 0 <= cnt f bs k.
Proof. intros f bs k. induction k as [|k IH]; cbn [cnt]; [lia|]. destruct (f _); lia. Qed.

Lemma sw32_small : forall v, 0 <= v < 2^31 -> bv_swrap 32 v = v.
Proof.
  intros v H. unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 32) with 2147483648 by reflexivity.
  replace (bv_modulus 32) with 4294967296 by reflexivity.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma zb_val : forall z, 0 <= z < 256 -> bv_unsigned (zb z) = z.
Proof.
  intros z H. unfold zb. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia.
Qed.

Lemma sub12 : forall (G : list byte) x0 x1 x2, sub G 12 3 = [x0; x1; x2] ->
  sub G 12 1 = [x0] /\ sub G 13 1 = [x1] /\ sub G 14 1 = [x2].
Proof.
  intros G x0 x1 x2 E.
  assert (A0 : sub G 12 1 = sub (sub G 12 3) 0 1) by (rewrite sub_sub by lia; reflexivity).
  assert (A1 : sub G 13 1 = sub (sub G 12 3) 1 1) by (rewrite sub_sub by lia; reflexivity).
  assert (A2 : sub G 14 1 = sub (sub G 12 3) 2 1) by (rewrite sub_sub by lia; reflexivity).
  rewrite A0, A1, A2, E. split; [reflexivity|]. split; reflexivity.
Qed.

Lemma sight_vals : forall F len, length F = 50%nat ->
  s_mac (sight F len) = src F /\ s_role (sight F len) = role F (dkind F len) /\
  s_ch (sight F len) = geo len /\
  (s_hd (sight F len) = 0 \/ s_hd (sight F len) = 1) /\
  (s_hd (sight F len) = 1 -> s_din (sight F len) <= 40 /\ s_dout (sight F len) <= 40).
Proof.
  intros F len HF. destruct (sight_fields F len HF) as (E0 & E8 & E12 & E20).
  pose proof (role_rng F (dkind F len)) as RR. pose proof (geo_rng len) as GR.
  unfold s_mac, s_role, s_ch, s_hd, s_din, s_dout, s32_at, u_at.
  rewrite E0, E8, E20, !ble_le4 by lia. rewrite sw32_small by lia.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  destruct (sdecl F) as [[a b]|] eqn:SD; cbv beta iota in E12; destruct (sub12 _ _ _ _ E12) as (B12 & B13 & B14);
    rewrite B12, B13, B14, !ble1.
  - unfold sdecl in SD. cbv zeta in SD.
    destruct (decl (fld F 18 20) && (4 * n_in (fld F 18 20) <=? 40) && (4 * n_out (fld F 18 20) <=? 40)) eqn:C;
      [|discriminate].
    injection SD as Ea Eb. apply andb_prop in C as [C Co]. apply andb_prop in C as [_ Ci].
    apply Z.leb_le in Ci, Co.
    assert (Ni : 0 <= n_in (fld F 18 20)) by (unfold n_in; apply cnt_nn).
    assert (No : 0 <= n_out (fld F 18 20)) by (unfold n_out; apply cnt_nn).
    rewrite !zb_val by lia. split; [right; reflexivity|]. intros _. lia.
  - rewrite !zb_val by lia. split; [left; reflexivity|]. intros X. discriminate.
Qed.

Lemma sight_len : forall F len, length F = 50%nat -> length (sight F len) = 24%nat.
Proof.
  intros F len HF. pose proof (len_src F HF) as LS. unfold sight.
  destruct (sdecl F) as [[a b]|]; cbv beta iota; rewrite !length_app, !length_le4, LS; reflexivity.
Qed.

Lemma sight_ok : forall F len, length F = 50%nat -> sighting_S1 (sight F len) /\ sighting_S2 (sight F len).
Proof.
  intros F len HF. destruct (sight_vals F len HF) as (_ & ER & _ & H1 & H2).
  pose proof (role_rng F (dkind F len)) as RR. unfold sighting_S1, sighting_S2. rewrite ER.
  split; [lia|]. split; [exact H1|exact H2].
Qed.

Lemma obs_c01 : forall T G ow now T' c, observe_model T G ow now T' c -> c = 0 \/ c = 1.
Proof.
  intros T G ow now T' c (r & _ & [(_ & E)|[(_ & _ & E)|(_ & _ & E)]]);
    apply (f_equal snd) in E; cbn [snd] in E.
  - unfold observe_known in E. cbv zeta in E.
    match type of E with c = snd (if ?b then _ else _) => destruct b end; cbn [snd] in E; lia.
  - unfold observe_full in E. destruct (ov_of T =? 0); cbn [snd] in E; lia.
  - unfold observe_new in E. cbn [snd] in E. lia.
Qed.

Lemma fr_eq : forall T P r j, find_res T P r -> 0 <= j < n_of T -> mac_of T j = P ->
  (forall i, 0 <= i < j -> mac_of T i <> P) -> r = j.
Proof.
  intros T P r j [(_ & M) | (Hr & E & M)] Hj Ej N.
  - exfalso. exact (M j Hj Ej).
  - destruct (Z.lt_total r j) as [X|[X|X]].
    + exfalso. exact (N r ltac:(lia) E).
    + exact X.
    + exfalso. exact (M j ltac:(lia) Ej).
Qed.

Lemma kn_T' : forall T G ow now r T' ret, (T', ret) = observe_known T G ow now r ->
  T' = kG T G ow now r \/ T' = upd (kG T G ow now r) 392 (Z_to_le_bytes 4 (seq_of T + 1)).
Proof.
  intros T G ow now r T' ret H. rewrite known_eq in H.
  match type of H with _ = (if ?c then _ else _) => destruct c end;
    injection H as H1 H2; [right|left]; exact H1.
Qed.

Lemma kn_ch : forall T G ow now r T' ret, length T = 400%nat -> length G = 24%nat -> 0 <= r < 8 ->
  (T', ret) = observe_known T G ow now r ->
  sub T' (48 * r + 20) 4 = if cC T G r then sub G 20 4 else sub T (48 * r + 20) 4.
Proof.
  intros T G ow now r T' ret LT LG Hr H. apply kn_T' in H.
  unfold kG, kF, kE, kD, kC, kB, kA in H.
  destruct (cD T G r), (cC T G r); destruct H as [-> | ->]; mf_go;
    first [apply mf_sub_upd_at; mf_vl; lia | reflexivity].
Qed.

Lemma kn_role : forall T G ow now r T' ret, length T = 400%nat -> length G = 24%nat -> 0 <= r < 8 ->
  cR T G r = false -> (T', ret) = observe_known T G ow now r ->
  sub T' (48 * r + 8) 4 = sub T (48 * r + 8) 4.
Proof.
  intros T G ow now r T' ret LT LG Hr CR H. apply kn_T' in H.
  unfold kG, kF, kE, kD, kC, kB, kA in H. rewrite CR in H.
  destruct (cD T G r); destruct H as [-> | ->]; mf_go; reflexivity.
Qed.

Lemma ne20 : forall G ow now, length G = 24%nat -> sub (new_entry G ow now) 20 4 = sub G 20 4.
Proof.
  intros G ow now LG. unfold new_entry, s_mac, zeros.
  rewrite !sub_app_r by (rewrite ?length_sub, ?repeat_length by lia; lia).
  rewrite ?length_sub, ?repeat_length by lia.
  rewrite sub_app_l by (rewrite ?length_sub by lia; lia).
  rewrite sub_sub by lia. f_equal; lia.
Qed.

Lemma he_mid : forall T G i k n, length T = 400%nat -> length G = 24%nat -> 0 <= i < 8 -> 8 <= k ->
  k + Z.of_nat n <= 17 -> sub (ho_entry T G i) k n = sub T (48 * i + k) n.
Proof.
  intros T G i k n LT LG Hi Hk Hn. unfold ho_entry.
  rewrite sub_app_r by (rewrite length_sub by lia; lia). rewrite length_sub by lia.
  rewrite sub_app_l by (rewrite ?length_sub by lia; lia). rewrite sub_sub by lia. f_equal; lia.
Qed.

Lemma ho_entry_f : forall T G i, length T = 400%nat -> length G = 24%nat -> 0 <= i < 8 ->
  s_mac (ho_entry T G i) = s_mac G /\ s_role (ho_entry T G i) = role_of_e T i /\
  s_hd (ho_entry T G i) = hd_of T i /\ s_din (ho_entry T G i) = din_of T i /\
  s_dout (ho_entry T G i) = dout_of T i /\ s_ch (ho_entry T G i) = ch_of T i.
Proof.
  intros T G i LT LG Hi.
  unfold s_mac, s_role, s_hd, s_din, s_dout, s_ch, role_of_e, hd_of, din_of, dout_of, ch_of, s32_at, u_at.
  rewrite (he_mid T G i 8 4), (he_mid T G i 12 1), (he_mid T G i 13 1), (he_mid T G i 14 1) by lia.
  split; [|split; [reflexivity|split; [reflexivity|split; [reflexivity|split; [reflexivity|]]]]].
  - unfold ho_entry. rewrite sub_app_l by (rewrite ?length_sub by lia; lia). rewrite sub_sub by lia. reflexivity.
  - unfold ho_entry. rewrite !sub_app_r by (rewrite ?length_sub by lia; lia). rewrite !length_sub by lia.
    rewrite sub_sub by lia. f_equal; f_equal; lia.
Qed.

Lemma obs_at : forall T G ow now T' c r, length T = 400%nat -> length G = 24%nat -> tbl_T1 T -> tbl_T3 T ->
  sighting_S1 G -> observe_model T G ow now T' c -> find_res T' (s_mac G) r ->
  (0 <= r -> s_ch G <= ch_of T' r) /\
  (forall j, 0 <= j < n_of T -> mac_of T j = s_mac G -> role_of_e T j = 1 -> 0 <= r /\ role_of_e T' r = 1).
Proof.
  intros T G ow now T' c r LT LG T1 T3 S1 (r0 & F0 & [(H0 & E) | [(H0 & N8 & E) | (H0 & N8 & E)]]) FR;
    unfold tbl_T1 in T1.
  - destruct F0 as [(X & _) | (Hr0 & E0 & M0)]; [lia|].
    destruct (mf_known T G ow now r0 T' c LT LG ltac:(lia) E) as (LT' & FRM & _).
    assert (MAC : forall i, 0 <= i < 8 -> mac_of T' i = mac_of T i).
    { intros i Hi. unfold mac_of. apply FRM; lia. }
    assert (NN : n_of T' = n_of T) by (unfold n_of, s32_at, u_at; rewrite (FRM 384 4%nat) by lia; reflexivity).
    assert (RR : r = r0).
    { apply (fr_eq T' (s_mac G) r r0 FR); [rewrite NN; lia | rewrite MAC by lia; exact E0 |].
      intros i Hi. rewrite MAC by lia. apply M0. exact Hi. }
    subst r. split.
    + intros _. pose proof (kn_ch T G ow now r0 T' c LT LG ltac:(lia) E) as KC.
      unfold ch_of, u_at. rewrite KC. unfold cC.
      destruct (ch_of T r0 <? s_ch G) eqn:C.
      * unfold s_ch, u_at. lia.
      * apply Z.ltb_ge in C. unfold ch_of, u_at in C. exact C.
    + intros j Hj Ej Rj.
      assert (J : r0 = j).
      { apply (fr_eq T (s_mac G) r0 j (or_intror (conj Hr0 (conj E0 M0))) Hj Ej).
        intros i Hi Ei. exact (T3 i j ltac:(lia) ltac:(lia) ltac:(lia) (eq_trans Ei (eq_sym Ej))). }
      subst j. split; [lia|].
      assert (CR : cR T G r0 = false).
      { unfold cR. rewrite Rj. destruct S1 as [S|[S|S]]; rewrite S; reflexivity. }
      pose proof (kn_role T G ow now r0 T' c LT LG ltac:(lia) CR E) as KR.
      unfold role_of_e, s32_at, u_at in Rj |- *. rewrite KR. exact Rj.
  - subst r0. destruct (mf_full T T' c LT E) as (LT' & FRM).
    assert (NN : n_of T' = n_of T) by (unfold n_of, s32_at, u_at; rewrite (FRM 384 4%nat) by lia; reflexivity).
    assert (NOJ : forall j, 0 <= j < n_of T -> mac_of T j <> s_mac G).
    { destruct F0 as [(_ & M) | (X & _)]; [exact M | lia]. }
    split.
    + intros Hr. exfalso. destruct FR as [(X & _) | (Hr' & Er & _)]; [lia|].
      rewrite NN in Hr'. apply (NOJ r Hr'). unfold mac_of in Er |- *.
      rewrite <- (FRM (48 * r) 6%nat) by lia. exact Er.
    + intros j Hj Ej _. exfalso. exact (NOJ j Hj Ej).
  - subst r0. destruct (mf_new T G ow now T' c LT LG ltac:(lia) E) as (LT' & N4 & FRM & ENT).
    assert (NN : n_of T' = n_of T + 1).
    { unfold n_of at 1. unfold s32_at, u_at. rewrite N4. rewrite bytes_le_to_Z_to_le_bytes by lia.
      change (8 * Z.of_nat 4) with 32. rewrite Z.mod_small by lia. apply swrap32_small. lia. }
    assert (NOJ : forall j, 0 <= j < n_of T -> mac_of T j <> s_mac G).
    { destruct F0 as [(_ & M) | (X & _)]; [exact M | lia]. }
    split.
    + intros Hr. destruct FR as [(X & _) | (Hr' & Er & _)]; [lia|]. rewrite NN in Hr'.
      assert (RN : r = n_of T).
      { destruct (Z.eq_dec r (n_of T)) as [X|X]; [exact X|]. exfalso. apply (NOJ r ltac:(lia)).
        unfold mac_of in Er |- *. rewrite <- (FRM (48 * r) 6%nat) by lia. exact Er. }
      subst r. unfold ch_of, u_at. rewrite (ENT 20 4%nat) by lia. rewrite ne20 by exact LG.
      unfold s_ch, u_at. lia.
    + intros j Hj Ej _. exfalso. exact (NOJ j Hj Ej).
Qed.

Lemma ho_facts_ok : forall H FR len now T' c r,
  length H = 480%nat -> hunt_ok H -> length FR = Z.to_nat len -> 0 <= len ->
  cm_ret (firstn 50 FR) (reac_frame_clean_len_model len) (sub H 412 6) (Some (sub H 400 12)) = 0 ->
  observe_model (sub H 0 400) (sight (firstn 50 FR) (reac_frame_clean_len_model len)) 0 now T' c ->
  tbl_T1 T' -> tbl_T2 T' -> (tbl_T4 (sub H 0 400) -> tbl_T4 T') -> length T' = 400%nat ->
  find_res T' (s_mac (sight (firstn 50 FR) (reac_frame_clean_len_model len))) r ->
  ho_facts H FR (reac_frame_clean_len_model len) (sub H 0 400)
    (if r <? 0 then sight (firstn 50 FR) (reac_frame_clean_len_model len)
     else ho_entry T' (sight (firstn 50 FR) (reac_frame_clean_len_model len)) r).
Proof.
  intros H FR len now T' c r LH HOK LFR Hlen R0 OM T1' T2' T4i LT' FRr.
  set (F := firstn 50 FR) in *. set (L := reac_frame_clean_len_model len) in *.
  set (G := sight F L) in *. set (T := sub H 0 400) in *.
  pose proof (cm_ret0_len _ _ _ _ R0) as L50.
  assert (LL : L <= len).
  { unfold L, reac_frame_clean_len_model.
    destruct ((54 <=? len) && ((len - 52) mod 36 =? 2)) eqn:EL; [|lia].
    apply andb_prop in EL. destruct EL as [EL _]. apply Z.leb_le in EL. lia. }
  assert (LF : length F = 50%nat) by (unfold F; rewrite length_firstn; lia).
  destruct (cm_ret0_facts _ _ _ _ R0) as [NU DK].
  destruct (sight_vals F L LF) as (SM & SR & SC & SH & SD). fold G in SM, SR, SC, SH, SD.
  pose proof (sight_len F L LF) as LG. fold G in LG.
  destruct (sight_ok F L LF) as [S1 S2]. fold G in S1, S2.
  assert (TOK : table_ok T) by (destruct HOK as (_ & X & _); exact X).
  destruct TOK as (TT1 & TT2 & TT3 & TT4).
  assert (LT : length T = 400%nat) by (unfold T; apply length_sub; lia).
  destruct (obs_at T G 0 now T' c r LT LG TT1 TT3 S1 OM FRr) as [CH RL].
  assert (MG : s_mac G = sub FR 6 6).
  { rewrite SM. unfold src, fld, sub, F. change (Z.to_nat 6) with 6%nat.
    rewrite skipn_firstn_comm, firstn_firstn. reflexivity. }
  assert (NE : s_mac G <> sub H 412 6).
  { rewrite SM. intros X. unfold bytes_eqb in NU. rewrite X in NU.
    match type of NU with context [list_eq_dec ?d ?a ?b] => destruct (list_eq_dec d a b) as [_|Y] end;
      [discriminate | apply Y; reflexivity]. }
  assert (DF : (fb FR 16 = 0 /\ fb FR 17 = 0) \/ fsum FR = 0).
  { destruct DK as [DK|DK].
    - left. apply dkind1 in DK. destruct DK as [D16 D17].
      assert (NF : forall k, (k < 50)%nat -> fb F k = fb FR k).
      { intros k Hk. unfold fb, F. f_equal. rewrite <- (firstn_skipn 50 FR) at 2.
        rewrite app_nth1; [reflexivity | rewrite length_firstn; lia]. }
      rewrite <- !NF by lia. split; assumption.
    - right. transitivity (fsum F); [|exact DK].
      unfold fsum, fld, F. rewrite skipn_firstn_comm, firstn_firstn. reflexivity. }
  unfold ho_facts. destruct (r <? 0) eqn:RL0; cbv beta iota.
  - apply Z.ltb_lt in RL0.
    split; [lia|]. split; [exact MG|]. split; [exact NE|]. split; [rewrite SC; lia|].
    split; [exact S1|]. split; [exact DF|]. split; [exact SH|].
    split; [intros X; apply SD; lia|].
    intros (j & Hj & Ej & Rj). destruct (RL j Hj Ej Rj) as [X _]. lia.
  - apply Z.ltb_ge in RL0. unfold tbl_T1 in T1'.
    assert (Hrn : 0 <= r < n_of T') by (destruct FRr as [(X & _) | (X & _)]; lia).
    destruct (ho_entry_f T' G r LT' LG ltac:(lia)) as (EM & ER & EH & EI & EO & EC).
    destruct (T4i TT4 r Hrn) as (H01 & H40 & _).
    rewrite EM, ER, EH, EI, EO, EC.
    split; [lia|]. split; [exact MG|]. split; [exact NE|]. split; [rewrite <- SC; apply CH; lia|].
    split; [apply T2'; exact Hrn|]. split; [exact DF|]. split; [exact H01|].
    split; [intros X; apply H40; lia|].
    intros (j & Hj & Ej & Rj). destruct (RL j Hj Ej Rj) as [_ X]. exact X.
Qed.
