(* links_holds discharges the hypothesis (HL : links) of the simulation proofs. Each Lk_stmt of Links.v is
   proved from the shared files (lib/Spec/DgnSpec.v, DgnLib.v, DgnLink.v):
   - L1: DgnLib spec_read_frame_fr (spec_read_frame against the fr_ reading), on the len bytes of b;
   - L2: DgnLib frame_build_bytes (lib_frame is build_frame) and lib_build_code, then lp_read_build_frame;
   - L3: DgnLib spec_system_at_system_at and body_check_spec, DgnLink spec_system_at_prefix;
   - L4: DgnSpec's ann_code, fr_body, strz_len and copy_len, against TSess's ann_field;
   - L5: TNeed's diginet_personality_from_name and TCb's desk_named_m, both by the same two name tests;
   - L6: DgnSpec keepalive_of and oui_of_firstn;
   - L7: TNeedLink tneed_spec_build_frame (TNeed's spec_build_frame is build_frame), then lp_read_build_frame.
   lp_read_build_frame is DgnLink's spec_build_frame_build_frame and spec_build_frame_read_frame:
   spec_read_frame reads a build_frame back with the fields it was built from. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnLink.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TNeed TSess0 TCb TSess TNeedLink.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Import Links.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* ---- lists ---- *)

(* zs b holds the first n bytes of b *)
Lemma lp_holds_firstn : forall (b : list byte) n, holds_body (zs b) (firstn n b).
Proof.
  intros b n i Hi. rewrite length_firstn in Hi.
  rewrite at8_firstn by lia. exact (holds_body_map b i ltac:(lia)).
Qed.

Lemma lp_zs_inj : forall a b : list byte, zs a = zs b -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; unfold zs in H; cbn [map] in H; try discriminate H; [reflexivity|].
  injection H as Hxy Hab. f_equal; [apply bz_inj; exact Hxy | apply IH; exact Hab].
Qed.

Lemma lp_skipn_exact : forall (p r : list byte) n, n = length p -> skipn n (p ++ r) = r.
Proof. intros p r n ->. rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity. Qed.

Lemma lp_firstn_exact : forall (m r : list byte) n, n = length m -> firstn n (m ++ r) = m.
Proof. intros m r n ->. rewrite firstn_app, Nat.sub_diag, firstn_O, app_nil_r, firstn_all. reflexivity. Qed.

Lemma lp_sub_mid : forall (p m r : list byte) k n, k = Z.of_nat (length p) -> n = length m ->
  sub (p ++ m ++ r) k n = m.
Proof.
  intros p m r k n -> ->. unfold sub. rewrite Nat2Z.id, (lp_skipn_exact p (m ++ r) (length p) eq_refl).
  apply lp_firstn_exact. reflexivity.
Qed.

Lemma lp_forallb_zeros : forall k, forallb (fun x => bz x =? 0) (repeat (b8 0) k) = true.
Proof. induction k as [|k IH]; [reflexivity|]. cbn [repeat forallb]. rewrite IH, bz_b8 by lia. reflexivity. Qed.

(* ---- a build_frame, read back (L2, L7) ---- *)

Lemma lp_spec_sum_at : forall body : list byte, spec_sum_at (zs body) 0 (Z.of_nat (length body)) = spec_sum body.
Proof.
  intros body. rewrite <- DgnLink.diginet_sum16_spec_sum_at.
  change (zs body) with (map bz body). rewrite DgnLink.lnk_sum16_map_bz, lib_sum16_eq, spec_sum_eq. reflexivity.
Qed.

Lemma lp_build_frame_split : forall dst src send ack retry cmd ncmds body zb,
  build_frame dst src send ack retry cmd ncmds body zb =
  (dst ++ src ++ put16 0x885f ++ put16 (16 + Z.of_nat (length body)) ++
   put16 (if zb then 0 else spec_sum body) ++ put32 send ++ put32 ack ++ put16 retry ++ [b8 cmd; b8 ncmds]) ++
  body ++ repeat (b8 0) (30 - length body).
Proof. intros. unfold build_frame. rewrite <- !app_assoc. reflexivity. Qed.

Lemma lp_build_frame_split2 : forall dst src send ack retry cmd ncmds body zb,
  build_frame dst src send ack retry cmd ncmds body zb =
  ((dst ++ src ++ put16 0x885f ++ put16 (16 + Z.of_nat (length body)) ++
    put16 (if zb then 0 else spec_sum body) ++ put32 send ++ put32 ack ++ put16 retry ++ [b8 cmd; b8 ncmds]) ++
   body) ++ repeat (b8 0) (30 - length body).
Proof. intros. unfold build_frame. rewrite <- !app_assoc. reflexivity. Qed.

(* spec_read_frame of the frame build_frame makes (zero_sum as spec_build_frame takes it, spec.h:238): every
   field it was built from, the MACs and the body in place, zeros after the body *)
Lemma lp_read_build_frame : forall dst src send ack retry cmd ncmds (body : list byte) zero_sum,
  length dst = 6%nat -> length src = 6%nat -> Z.of_nat (length body) <= 1484 ->
  0 <= send < 2 ^ 32 -> 0 <= ack < 2 ^ 32 -> 0 <= retry < 2 ^ 16 -> 0 <= cmd < 2 ^ 8 -> 0 <= ncmds < 2 ^ 8 ->
  let frame := build_frame dst src send ack retry cmd ncmds body (negb (zero_sum =? 0)) in
  let f := spec_read_frame (zs frame) (frame_len (length body)) in
  Z.of_nat (length frame) = frame_len (length body) /\
  sf_code f = SPEC_OK /\ sub frame (sf_dst f) 6 = dst /\ sub frame (sf_src f) 6 = src /\
  sf_cmd f = cmd /\ sf_send f = send /\ sf_ack f = ack /\ sf_retry f = retry /\ sf_ncmds f = ncmds /\
  sf_body_len f = Z.of_nat (length body) /\ sub frame SPEC_BODY_AT (length body) = body /\
  forallb (fun x => bz x =? 0) (skipn (Z.to_nat (SPEC_BODY_AT + Z.of_nat (length body))) frame) = true /\
  sf_sum f = (if zero_sum =? 0 then spec_sum body else 0).
Proof.
  intros dst src send ack retry cmd ncmds body zero_sum Hd Hs Hl Hse Hac Hre Hc Hn. cbv zeta.
  pose proof (DgnLink.spec_build_frame_build_frame dst src send ack retry cmd ncmds body zero_sum Hd Hs
                ltac:(lia) ltac:(lia)) as EB.
  destruct (DgnLink.spec_build_frame_read_frame (map bz dst) (map bz src) send ack retry cmd ncmds (map bz body)
              (Z.of_nat (length body)) zero_sum ltac:(unfold DgnLink.SPEC_MAX_BODY; lia) Hse Hac Hre) as [_ BF].
  rewrite EB in BF. cbn [snd] in BF. unfold DgnLink.built_frame in BF.
  destruct BF as (_ & BR & _).
  change (map bz (build_frame dst src send ack retry cmd ncmds body (negb (zero_sum =? 0))))
    with (zs (build_frame dst src send ack retry cmd ncmds body (negb (zero_sum =? 0)))) in BR.
  split; [apply length_build_frame; assumption|].
  change (frame_len (length body)) with (Z.max 60 (30 + Z.of_nat (length body))).
  rewrite BR. cbn [sf_code sf_dst sf_src sf_cmd sf_send sf_ack sf_retry sf_ncmds sf_body_len sf_sum].
  split; [reflexivity|].
  split; [unfold build_frame; apply (lp_sub_mid [] dst); [reflexivity | lia]|].
  split; [unfold build_frame; apply (lp_sub_mid dst src); [rewrite Hd; reflexivity | lia]|].
  do 6 (split; [reflexivity|]).
  split.
  { rewrite lp_build_frame_split. apply lp_sub_mid; [|reflexivity].
    unfold SPEC_BODY_AT. rewrite !length_app, Hd, Hs, !length_put16, !length_put32. cbn [length]. lia. }
  split.
  { rewrite lp_build_frame_split2. rewrite lp_skipn_exact; [apply lp_forallb_zeros|].
    unfold SPEC_BODY_AT. rewrite !length_app, Hd, Hs, !length_put16, !length_put32. cbn [length]. lia. }
  destruct (zero_sum =? 0); [exact (lp_spec_sum_at body) | reflexivity].
Qed.

(* ---- L1 ---- *)

Lemma L1_holds : L1_stmt.
Proof.
  unfold L1_stmt. intros b len Hl. cbv zeta.
  pose proof (lp_holds_firstn b (Z.to_nat len)) as Hh.
  assert (Hlen : Z.of_nat (length (firstn (Z.to_nat len) b)) = len) by (rewrite length_firstn; lia).
  destruct (spec_read_frame_fr (zs b) (firstn (Z.to_nat len) b) Hh) as [C F].
  rewrite Hlen in C, F.
  unfold DIGINET_OK, SPEC_OK. split.
  - rewrite C. tauto.
  - intros H0. specialize (F H0). cbv zeta in F.
    destruct F as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14).
    unfold SPEC_MAC, SPEC_BODY_AT. repeat split; assumption.
Qed.

(* ---- L2 ---- *)

Lemma L2_holds : L2_stmt.
Proof.
  unfold L2_stmt. intros dst src send ack retry cmd ncmds bd cap mode Hd Hs Hm Hse Hac Hre Hc Hn.
  assert (Em : negb ((mode =? 0) || (mode =? 1)) = false) by (destruct Hm as [-> | ->]; reflexivity).
  unfold diginet_frame_build_code. rewrite Em.
  unfold lib_build_code, DIGINET_MAX_BODY_LEN, DIGINET_OK, DIGINET_E_REFUSED.
  split; [|split].
  - intros Hl Hb Hcap. cbv zeta.
    assert (E1 : (1484 <? Z.of_nat (length bd)) = false) by (apply Z.ltb_ge; exact Hl).
    assert (E2 : (cap <? frame_len (length bd)) = false) by (apply Z.ltb_ge; exact Hcap).
    rewrite E1, Hb, E2.
    rewrite frame_build_bytes by exact Hm.
    pose proof (lp_read_build_frame dst src send ack retry cmd ncmds bd mode Hd Hs Hl Hse Hac Hre Hc Hn) as R.
    cbv zeta in R.
    assert (Ez : negb (mode =? 0) = (mode =? 1)) by (destruct Hm as [-> | ->]; reflexivity).
    rewrite Ez in R.
    destruct R as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13).
    refine (conj eq_refl (conj R1 (conj R2 (conj R3 (conj R4 (conj R5 (conj R6 (conj R7 (conj R8
              (conj R9 (conj R10 (conj R11 (conj R12 _))))))))))))).
    rewrite R13, (lp_spec_sum_at bd). unfold DIGINET_SUM_ZERO.
    destruct Hm as [-> | ->]; reflexivity.
  - intros Hl Hb.
    assert (E1 : (1484 <? Z.of_nat (length bd)) = false) by (apply Z.ltb_ge; exact Hl).
    assert (E2 : negb (body_check bd =? 0) = true) by (apply negb_true_iff, Z.eqb_neq; exact Hb).
    rewrite E1, E2. reflexivity.
  - intros Hl.
    assert (E1 : (1484 <? Z.of_nat (length bd)) = true) by (apply Z.ltb_lt; exact Hl).
    rewrite E1. reflexivity.
Qed.

(* ---- L3 ---- *)

Lemma L3_holds : L3_stmt.
Proof.
  unfold L3_stmt. intros b n Hn.
  pose proof (lp_holds_firstn b (Z.to_nat n)) as Hh.
  assert (Hlen : Z.of_nat (length (firstn (Z.to_nat n) b)) = n) by (rewrite length_firstn; lia).
  pose proof (spec_system_at_system_at (zs b) (firstn (Z.to_nat n) b) Hh) as S. rewrite Hlen in S.
  rewrite body_check_spec. unfold DIGINET_OK, DIGINET_E_REFUSED.
  split; [|split].
  - revert S. destruct (system_at (firstn (Z.to_nat n) b)); intros S.
    + apply Z.leb_le in S. split; intros H; [discriminate H | lia].
    + apply Z.leb_gt in S. split; intros H; [exact S | reflexivity].
  - destruct (system_at (firstn (Z.to_nat n) b)); [right | left]; reflexivity.
  - exact (DgnLink.spec_system_at_prefix (zs b) n).
Qed.

(* ---- L4 ---- *)

Lemma L4_holds : L4_stmt.
Proof.
  unfold L4_stmt. intros bb Hc Ha.
  pose proof (fr_body_len_ok bb Hc) as (Hb0 & Hp0 & Hsum).
  unfold ann_code. rewrite Ha. cbn [negb]. unfold DIGINET_OK, SPEC_ANN_MIN.
  split.
  - destruct (Z.ltb_spec (fr_body_len bb) 33) as [L|L]; split; intros H; try discriminate H; lia.
  - intros H.
    assert (Hl : 33 <= fr_body_len bb)
      by (destruct (Z.ltb_spec (fr_body_len bb) 33) as [L|L]; [discriminate H | lia]).
    clear H. split.
    + unfold ann_unknown, fr_body, SPEC_ANN_UNKNOWN, SPEC_BODY_AT. rewrite firstn_firstn.
      replace (Nat.min 15 (Z.to_nat (fr_body_len bb))) with 15%nat by lia. reflexivity.
    + intros X HX. cbv zeta.
      assert (HXn : (Z.to_nat X + 9 <= Z.to_nat (fr_body_len bb))%nat)
        by (unfold SPEC_ANN_VERSION, SPEC_ANN_NAME in HX; lia).
      assert (E9 : firstn 9 (skipn (Z.to_nat X) (fr_body bb)) = firstn 9 (skipn (Z.to_nat (SPEC_BODY_AT + X)) bb)).
      { unfold fr_body, SPEC_BODY_AT. rewrite skipn_firstn_comm, firstn_firstn, skipn_skipn.
        replace (Nat.min 9 (Z.to_nat (fr_body_len bb) - Z.to_nat X)) with 9%nat by lia.
        replace (Z.to_nat X + 30)%nat with (Z.to_nat (30 + X)) by (unfold SPEC_ANN_VERSION, SPEC_ANN_NAME in HX; lia).
        reflexivity. }
      set (src := skipn (Z.to_nat X) (fr_body bb)) in *.
      set (at_x := skipn (Z.to_nat (SPEC_BODY_AT + X)) bb) in *.
      assert (Ek : strz_len src = strz_len at_x) by (unfold strz_len; rewrite E9; reflexivity).
      assert (Lk : (strz_len src <= length src)%nat).
      { unfold strz_len. pose proof (nz_run_le (firstn 9 src)) as N. rewrite length_firstn in N. lia. }
      pose proof (strz_len_le src) as K9.
      assert (LF : length (firstn (strz_len src) src) = strz_len src) by (rewrite length_firstn; lia).
      unfold ann_field. change (copy_len 10 9 src) with (strz_len src). rewrite <- Ek.
      split; [exact K9|]. split.
      * rewrite firstn_app, LF, Nat.sub_diag, firstn_O, app_nil_r, firstn_firstn, Nat.min_id.
        transitivity (firstn (strz_len src) (firstn 9 src)).
        { rewrite firstn_firstn. f_equal. lia. }
        rewrite E9, firstn_firstn. f_equal. lia.
      * unfold at8. rewrite app_nth2 by (rewrite LF; lia). rewrite LF, Nat.sub_diag. cbn [nth].
        apply bz_b8. lia.
Qed.

(* ---- L5 ---- *)

Definition lp_c24_list : list Z := [0x43; 0x4e; 0x54; 0x52; 0x4c; 0x7c; 0x32; 0x34].
Definition lp_pc_list : list Z := [0x4d; 0x41; 0x49; 0x4e; 0x55; 0x4e; 0x49; 0x54].

Lemma lp_c24 : zs C24_NAME = lp_c24_list.
Proof. vm_compute. reflexivity. Qed.

Lemma lp_pc : zs PC_NAME = lp_pc_list.
Proof. vm_compute. reflexivity. Qed.

Lemma lp_from_name_cases : forall name, diginet_personality_from_name name =
  if z_list_eqb (zs name) lp_c24_list then Some 0 else if z_list_eqb (zs name) lp_pc_list then Some 1 else None.
Proof. reflexivity. Qed.

(* desk_named's test of an 8-byte name (strlen, then memcmp) is list equality *)
Lemma lp_beq_bytes_name : forall (l name : list byte) (s : list Z) n, length l = n -> zs name = s ->
  length name = 8%nat -> ((n =? 8)%nat && beq_bytes l name) = z_list_eqb (zs l) s.
Proof.
  intros l name s n Hln Hs Hn. apply Bool.eq_true_iff_eq. rewrite andb_true_iff, Nat.eqb_eq, z_list_eqb_eq.
  unfold beq_bytes. rewrite <- Hs. destruct (list_eq_dec Z.eq_dec (zs l) (zs name)) as [E|E].
  - split; [intros _; exact E | intros _; split; [|reflexivity]].
    apply (f_equal (@length Z)) in E. unfold zs in E. rewrite !length_map in E. lia.
  - split; [intros [_ H]; discriminate H | intros H; contradiction].
Qed.

(* desk_named_m on a body of 33 bytes or more: spec_strz_len stays in the block *)
Lemma lp_desk_named_m : forall I B rest, (9 <= length (skipn (Z.to_nat SPEC_ANN_NAME) rest))%nat ->
  desk_named_m I B rest =
  let fld := skipn (Z.to_nat SPEC_ANN_NAME) rest in
  let n := strz_len fld in
  if (n =? 8)%nat && beq_bytes (firstn n fld) C24_NAME then Some (B, ti_spec_c24 I)
  else if (n =? 8)%nat && beq_bytes (firstn n fld) PC_NAME then Some (B, ti_spec_pc I)
  else Some (B, 0).
Proof.
  intros I B rest H. unfold desk_named_m, list_strz_len. cbv zeta.
  replace ((length (skipn (Z.to_nat SPEC_ANN_NAME) rest) <?
            Nat.min 9 (S (strz_len (skipn (Z.to_nat SPEC_ANN_NAME) rest))))%nat) with false
    by (symmetry; apply Nat.ltb_ge; lia).
  reflexivity.
Qed.

Lemma L5_holds : L5_stmt.
Proof.
  unfold L5_stmt. intros I B rest Hr. cbv zeta.
  assert (Hf : (9 <= length (skipn (Z.to_nat SPEC_ANN_NAME) rest))%nat)
    by (rewrite length_skipn; unfold SPEC_ANN_NAME, SPEC_ANN_MIN in *; lia).
  rewrite (lp_desk_named_m I B rest Hf). cbv zeta.
  set (fld := skipn (Z.to_nat SPEC_ANN_NAME) rest) in *.
  change (copy_len 10 9 fld) with (strz_len fld). rewrite lp_from_name_cases.
  pose proof (strz_len_le fld) as K9.
  assert (Lf : length (firstn (strz_len fld) fld) = strz_len fld) by (rewrite length_firstn; lia).
  rewrite (lp_beq_bytes_name (firstn (strz_len fld) fld) C24_NAME lp_c24_list (strz_len fld) Lf lp_c24 eq_refl).
  rewrite (lp_beq_bytes_name (firstn (strz_len fld) fld) PC_NAME lp_pc_list (strz_len fld) Lf lp_pc eq_refl).
  destruct (z_list_eqb (zs (firstn (strz_len fld) fld)) lp_c24_list);
    [|destruct (z_list_eqb (zs (firstn (strz_len fld) fld)) lp_pc_list)]; cbn beta iota.
  - exists (ti_spec_c24 I). split; [reflexivity|].
    eexists; exists c24. split; [reflexivity|].
    split; [left; split; [reflexivity | split; reflexivity] | split; reflexivity].
  - exists (ti_spec_pc I). split; [reflexivity|].
    eexists; exists pc. split; [reflexivity|].
    split; [right; split; [reflexivity | split; reflexivity] | split; reflexivity].
  - exists 0. split; reflexivity.
Qed.

(* ---- L6 ---- *)

Lemma L6_holds : L6_stmt.
Proof.
  unfold L6_stmt. split.
  - intros bb _. unfold fr_keepalive, keepalive_of, DIGINET_CMD_DATA.
    rewrite !andb_true_iff, !Z.eqb_eq. tauto.
  - intros mac Hm. split.
    + intros H. apply (oui_of_firstn mac Hm) in H. unfold beq_bytes. rewrite H.
      destruct (list_eq_dec Z.eq_dec _ _) as [|E]; [reflexivity | exfalso; apply E; reflexivity].
    + intros H. apply (oui_of_firstn mac Hm). unfold beq_bytes in H.
      destruct (list_eq_dec Z.eq_dec (zs (firstn 3 mac)) (zs SPEC_OUI)) as [E|E]; [|discriminate H].
      apply lp_zs_inj in E. rewrite E. reflexivity.
Qed.

(* ---- L7 ---- *)

Lemma L7_holds : L7_stmt.
Proof.
  unfold L7_stmt. intros dst src send ack retry cmd ncmds body Hd Hs Hl Hse Hac Hre Hc Hn. cbv zeta.
  rewrite tneed_spec_build_frame by assumption. cbn [fst snd].
  unfold SPEC_MAX_BODY in Hl.
  pose proof (lp_read_build_frame dst src send ack retry cmd ncmds body 0 Hd Hs Hl Hse Hac Hre Hc Hn) as R.
  cbv zeta in R.
  destruct R as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13).
  exact (conj eq_refl (conj R1 (conj R2 (conj R3 (conj R4 (conj R5 (conj R6 (conj R7 (conj R8
           (conj R9 (conj R10 (conj R11 (conj R12 R13))))))))))))).
Qed.

Theorem links_holds : links.
Proof.
  unfold links.
  exact (conj L1_holds (conj L2_holds (conj L3_holds (conj L4_holds (conj L5_holds (conj L6_holds L7_holds)))))).
Qed.
