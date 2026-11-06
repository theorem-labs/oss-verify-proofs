(* check_latest_sent_seg_model: the pure facts the image-A (ASan) walk of check_latest_sent
   (A/Prog/check_latest_sent_cgW.v) needs about the model lib/TModel/TCb.v (check_latest_sent_m, latest_sent_loop,
   tagged_of_m, q_remove_m, q_remove_loop) and about the world accessors of lib/TModel/TWorld.v. No machine state,
   no image, no segment. Part 1 copies the model-shape lemmas of the plain walk lib/Prog/T/check_latest_sent.v
   (ls_exit .. ls_round, with its list bridges), which this file does not Require. Part 2 gives the value ranges of
   the fields the code compares; part 3 the length and the field reads after the three stores the code makes
   (g_cmd[s].st, g_q[k], g_nq); part 4 the PENDING-command invariant of the contract's premise (cls_inv) and the
   form the walk carries (cls_inv_c, the same bound for s < CMDS_MAX only). The bridge cls_inv_to_c goes from the
   one to the other. cls_inv itself is not kept by a store to g_q when g_ncmd > CMDS_MAX: g_cmd[1024 ..] read
   g_q's bytes (A_Cmd_st 1024 = OFF_g_q). Its preservation lemmas therefore take g_ncmd <= CMDS_MAX; the _c forms
   need no bound on g_ncmd. Part 5 says what a whole q_remove run and a whole round do to the world. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Open Scope Z_scope.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.

(* the side conditions of the TWorldLemmas store lemmas: every offset is a literal of TWorld.v *)
Ltac cls_lia :=
  unfold TW.A_Cmd_st, TW.A_Cmd_display, TW.A_Cmd_bytes, TW.A_Cmd_len, TW.OFF_g_cmd, TW.OFF_g_q, TW.OFF_g_nq,
    TW.OFF_g_ncmd, TW.W_LEN, TC.CMDS_MAX in *;
  rewrite ?length_put; lia.

(* ---- small inversion and list bridges ---- *)

Lemma cls_pair_inv : forall {X Y : Type} (x x' : X) (y y' : Y), Some (x, y) = Some (x', y') -> x = x' /\ y = y'.
Proof.
  intros X Y x x' y y' H. split.
  - exact (f_equal (fun o => match o with Some (a, _) => a | None => x end) H).
  - exact (f_equal (fun o => match o with Some (_, b) => b | None => y end) H).
Qed.

Lemma cls_firstn1 : forall (l : list byte) n,
  firstn 1 (skipn n l) = match nth_error l n with Some x => [x] | None => [] end.
Proof.
  intros l n. revert l. induction n as [|n IH]; intros [|x l]; cbn; try reflexivity. apply IH.
Qed.

Lemma cls_at8_ne : forall (l : list byte) n,
  DSpec.at8 l n = match nth_error l n with Some x => bv_unsigned x | None => 0 end.
Proof.
  intros l n. revert l. unfold DSpec.at8, DSpec.bz. induction n as [|n IH]; intros [|x l]; cbn; try reflexivity.
  apply IH.
Qed.

Lemma cls_u_at8 : forall (l : list byte) k j, 0 <= k -> 0 <= j ->
  TW.u_at l (k + j) 1 = DSpec.at8 (skipn (Z.to_nat k) l) (Z.to_nat j).
Proof.
  intros l k j Hk Hj. unfold TW.u_at, TW.sub. rewrite cls_firstn1, cls_at8_ne.
  replace (Z.to_nat (k + j)) with (Z.to_nat k + Z.to_nat j)%nat by lia.
  rewrite <- nth_skipn.
  destruct (nth_error (skipn (Z.to_nat k) l) (Z.to_nat j)); cbn;
    [rewrite Z.shiftl_0_l, Z.lor_0_r; reflexivity | reflexivity].
Qed.

Lemma cls_beq : forall l r, TC.beq_bytes l r = true -> l = r.
Proof.
  intros l r H. unfold TC.beq_bytes in H.
  destruct (list_eq_dec Z.eq_dec (TW.zs l) (TW.zs r)) as [E|E]; [|discriminate H].
  clear H. unfold TW.zs in E. revert r E. induction l as [|a l IH]; intros [|b r] E; cbn in E; try discriminate.
  - reflexivity.
  - injection E as E1 E2. f_equal; [apply bv_eq; exact E1 | apply IH; exact E2].
Qed.

(* ---- 1. the model's shape ---- *)

Lemma cls_exit : forall fuel Bc body len pos dispc B' disp',
  TC.latest_sent_loop fuel Bc body len pos dispc = Some (B', disp') -> len <= pos -> B' = Bc /\ disp' = dispc.
Proof.
  intros [|fuel] Bc body len pos dispc B' disp' H Hp; [discriminate H|].
  cbn [TC.latest_sent_loop] in H. rewrite (proj2 (Z.ltb_ge pos len) Hp) in H. cbv beta iota in H.
  destruct (cls_pair_inv _ _ _ _ H) as [E1 E2]. split; [exact (eq_sym E1) | exact (eq_sym E2)].
Qed.

Lemma cls_qrm : forall Bc s B2, TC.q_remove_m Bc s = Some (B2, tt) ->
  exists B1 k, TC.q_remove_loop (S (Z.to_nat TC.CMDS_MAX)) Bc s (TW.g_nq Bc) 0 0 = Some (B1, k)
               /\ B2 = TW.set_g_nq B1 k.
Proof.
  intros Bc s B2 H. unfold TC.q_remove_m in H.
  destruct (TC.q_remove_loop (S (Z.to_nat TC.CMDS_MAX)) Bc s (TW.g_nq Bc) 0 0) as [[B1 k]|] eqn:E;
    [|discriminate H].
  cbv beta iota in H. destruct (cls_pair_inv _ _ _ _ H) as [E1 _]. subst B2.
  exists B1, k. split; [first [exact E | reflexivity] | reflexivity].
Qed.

Lemma cls_q_step : forall fuel Bc s nq i k Bf kf,
  TC.q_remove_loop fuel Bc s nq i k = Some (Bf, kf) -> i < nq ->
  exists fuel', fuel = S fuel' /\ i < TC.CMDS_MAX /\
    (if TW.Q_at Bc i =? s then TC.q_remove_loop fuel' Bc s nq (i + 1) k = Some (Bf, kf)
     else TC.q_remove_loop fuel' (TW.set_Q_at Bc k (TW.Q_at Bc i)) s nq (i + 1) (k + 1) = Some (Bf, kf)).
Proof.
  intros [|fuel] Bc s nq i k Bf kf H Hi; [discriminate H|]. cbn [TC.q_remove_loop] in H.
  rewrite (proj2 (Z.ltb_lt _ _) Hi) in H.
  destruct (TC.CMDS_MAX <=? i) eqn:C; [discriminate H|]. apply Z.leb_gt in C.
  exists fuel. split; [reflexivity|]. split; [exact C|]. destruct (TW.Q_at Bc i =? s); exact H.
Qed.

Lemma cls_q_exit : forall fuel Bc s nq i k Bf kf,
  TC.q_remove_loop fuel Bc s nq i k = Some (Bf, kf) -> nq <= i -> Bf = Bc /\ kf = k.
Proof.
  intros [|fuel] Bc s nq i k Bf kf H Hi; [discriminate H|]. cbn [TC.q_remove_loop] in H.
  rewrite (proj2 (Z.ltb_ge _ _) Hi) in H. cbv beta iota in H.
  destruct (cls_pair_inv _ _ _ _ H) as [E1 E2]. split; [exact (eq_sym E1) | exact (eq_sym E2)].
Qed.

Lemma cls_q_nqle : forall fuel Bc s nq i k Bf kf,
  TC.q_remove_loop fuel Bc s nq i k = Some (Bf, kf) -> i <= TC.CMDS_MAX -> nq <= TC.CMDS_MAX.
Proof.
  induction fuel as [|fuel IH]; intros Bc s nq i k Bf kf H Hi; [discriminate H|].
  cbn [TC.q_remove_loop] in H.
  destruct (Z.ltb_spec i nq) as [L|L]; [|lia].
  destruct (TC.CMDS_MAX <=? i) eqn:C; [discriminate H|]. apply Z.leb_gt in C.
  destruct (TW.Q_at Bc i =? s).
  - exact (IH Bc s nq (i + 1) k Bf kf H ltac:(lia)).
  - exact (IH (TW.set_Q_at Bc k (TW.Q_at Bc i)) s nq (i + 1) (k + 1) Bf kf H ltac:(lia)).
Qed.

Lemma cls_round : forall fuel Bc body len pos dispc B' disp',
  TC.latest_sent_loop (S fuel) Bc body len pos dispc = Some (B', disp') ->
  0 <= pos < len -> Z.of_nat (length body) = len ->
  exists s B2,
    3 <= len - pos /\
    TW.u_at body pos 1 = TC.TAG /\
    s = Z.lor (Z.shiftl (TW.u_at body (pos + 2) 1) 7) (TW.u_at body (pos + 1) 1) /\
    0 <= s < TC.CMDS_MAX /\ s < TW.g_ncmd Bc /\
    TW.Cmd_st Bc s = TC.PENDING /\
    TW.Cmd_len Bc s <= len - pos /\
    TW.sub body pos (Z.to_nat (TW.Cmd_len Bc s)) = TW.sub Bc (TW.A_Cmd_bytes s) (Z.to_nat (TW.Cmd_len Bc s)) /\
    TC.q_remove_m (TW.set_Cmd_st Bc s TC.SENT) s = Some (B2, tt) /\
    TC.latest_sent_loop fuel B2 body len (pos + TW.Cmd_len Bc s)
      (Z.lor dispc (TW.Cmd_display B2 s)) = Some (B', disp').
Proof.
  intros fuel Bc body len pos dispc B' disp' H Hpos Hlen.
  cbn [TC.latest_sent_loop] in H. rewrite (proj2 (Z.ltb_lt pos len) ltac:(lia)) in H.
  unfold TC.tagged_of_m in H.
  destruct (Z.ltb_spec (len - pos) 3) as [H3|H3]; cbv beta iota in H; [discriminate H|].
  destruct (Nat.ltb_spec (length (skipn (Z.to_nat pos) body)) 1) as [H1|H1]; cbv beta iota in H; [discriminate H|].
  destruct (Z.eqb_spec (DSpec.at8 (skipn (Z.to_nat pos) body) 0) TC.TAG) as [HT|HT];
    cbn [negb] in H; cbv beta iota in H; [|discriminate H].
  destruct (Nat.ltb_spec (length (skipn (Z.to_nat pos) body)) 3) as [H4|H4]; cbv beta iota in H; [discriminate H|].
  set (sv := Z.lor (DSpec.at8 (skipn (Z.to_nat pos) body) 1)
                   (Z.shiftl (DSpec.at8 (skipn (Z.to_nat pos) body) 2) 7)) in *.
  destruct (Z.ltb_spec sv (TW.g_ncmd Bc)) as [Hs1|Hs1]; cbv beta iota in H; [|discriminate H].
  destruct (Z.leb_spec TC.CMDS_MAX sv) as [Hs2|Hs2]; cbv beta iota in H; [discriminate H|].
  destruct (negb (TW.Cmd_st Bc sv =? TC.PENDING) || (len - pos <? TW.Cmd_len Bc sv)
            || negb (TC.beq_bytes (firstn (Z.to_nat (TW.Cmd_len Bc sv)) (skipn (Z.to_nat pos) body))
                                  (TW.sub Bc (TW.A_Cmd_bytes sv) (Z.to_nat (TW.Cmd_len Bc sv))))) eqn:EC;
    cbv beta iota in H; [discriminate H|].
  apply orb_false_iff in EC. destruct EC as [EC1 EC3]. apply orb_false_iff in EC1. destruct EC1 as [EC1 EC2].
  apply negb_false_iff in EC1. apply Z.eqb_eq in EC1.
  apply Z.ltb_ge in EC2. apply negb_false_iff in EC3. apply cls_beq in EC3.
  destruct (TC.q_remove_m (TW.set_Cmd_st Bc sv TC.SENT) sv) as [[B2 []]|] eqn:EQ; cbv beta iota in H;
    [|discriminate H].
  exists sv, B2.
  assert (A0 : TW.u_at body pos 1 = DSpec.at8 (skipn (Z.to_nat pos) body) 0).
  { replace pos with (pos + 0) at 1 by lia. apply cls_u_at8; lia. }
  assert (A1 : TW.u_at body (pos + 1) 1 = DSpec.at8 (skipn (Z.to_nat pos) body) 1).
  { rewrite (cls_u_at8 body pos 1) by lia. reflexivity. }
  assert (A2 : TW.u_at body (pos + 2) 1 = DSpec.at8 (skipn (Z.to_nat pos) body) 2).
  { rewrite (cls_u_at8 body pos 2) by lia. reflexivity. }
  assert (SN : 0 <= sv).
  { unfold sv. rewrite <- A1, <- A2. apply Z.lor_nonneg. split.
    - exact (proj1 (u_at_range body (pos + 1) 1)).
    - apply Z.shiftl_nonneg. exact (proj1 (u_at_range body (pos + 2) 1)). }
  split; [lia|]. split; [rewrite A0; exact HT|].
  split; [unfold sv; rewrite A1, A2; apply Z.lor_comm|].
  split; [lia|]. split; [exact Hs1|]. split; [exact EC1|]. split; [exact EC2|].
  split; [unfold TW.sub; exact EC3|]. split; [exact EQ | exact H].
Qed.

Lemma cls_start : forall B body len B' disp,
  TC.check_latest_sent_m B body len = Some (B', disp) ->
  TC.latest_sent_loop (S (Z.to_nat len)) B body len 0 0 = Some (B', disp).
Proof. intros B body len B' disp H. unfold TC.check_latest_sent_m in H. exact H. Qed.

(* ---- 2. value ranges ---- *)

Lemma cls_cmd_len_range : forall B s, 0 <= TW.Cmd_len B s < 256.
Proof.
  intros B s. unfold TW.Cmd_len. pose proof (u_at_range B (TW.A_Cmd_len s) 1) as R.
  change (2 ^ (8 * Z.of_nat 1)) with 256 in R. exact R.
Qed.

Lemma cls_q_at_range : forall B i, 0 <= TW.Q_at B i < 2 ^ 32.
Proof.
  intros B i. unfold TW.Q_at. pose proof (u_at_range B (TW.OFF_g_q + 4 * i) 4) as R.
  change (8 * Z.of_nat 4) with 32 in R. exact R.
Qed.

Lemma cls_g_nq_range : forall B, 0 <= TW.g_nq B < 2 ^ 32.
Proof.
  intros B. unfold TW.g_nq. pose proof (u_at_range B TW.OFF_g_nq 4) as R.
  change (8 * Z.of_nat 4) with 32 in R. exact R.
Qed.

Lemma cls_g_ncmd_range : forall B, 0 <= TW.g_ncmd B < 2 ^ 32.
Proof.
  intros B. unfold TW.g_ncmd. pose proof (u_at_range B TW.OFF_g_ncmd 4) as R.
  change (8 * Z.of_nat 4) with 32 in R. exact R.
Qed.

Lemma cls_cmd_st_range : forall B s, - 2 ^ 31 <= TW.Cmd_st B s < 2 ^ 31.
Proof. intros B s. pose proof (s32_range B (TW.A_Cmd_st s)) as R. unfold TW.Cmd_st. lia. Qed.

Lemma cls_cmd_display_range : forall B s, - 2 ^ 31 <= TW.Cmd_display B s < 2 ^ 31.
Proof. intros B s. pose proof (s32_range B (TW.A_Cmd_display s)) as R. unfold TW.Cmd_display. lia. Qed.

(* ---- 3. lengths and field reads after the three stores ---- *)

Lemma cls_len_set_st : forall B s v, Z.of_nat (length B) = TW.W_LEN -> 0 <= s < TC.CMDS_MAX ->
  Z.of_nat (length (TW.set_Cmd_st B s v)) = TW.W_LEN.
Proof. intros B s v HL Hs. unfold TW.set_Cmd_st. rewrite length_upd_put by cls_lia. exact HL. Qed.

Lemma cls_len_set_q : forall B k v, Z.of_nat (length B) = TW.W_LEN -> 0 <= k < TC.CMDS_MAX ->
  Z.of_nat (length (TW.set_Q_at B k v)) = TW.W_LEN.
Proof. intros B k v HL Hk. unfold TW.set_Q_at. rewrite length_upd_put by cls_lia. exact HL. Qed.

Lemma cls_len_set_nq : forall B v, Z.of_nat (length B) = TW.W_LEN ->
  Z.of_nat (length (TW.set_g_nq B v)) = TW.W_LEN.
Proof. intros B v HL. unfold TW.set_g_nq. rewrite length_upd_put by cls_lia. exact HL. Qed.

(* the reads of g_cmd[j] for any j >= 0 (also past the payload): the invariants quantify up to g_ncmd *)
Lemma cls_st_set_st_ne0 : forall B s v j, Z.of_nat (length B) = TW.W_LEN ->
  0 <= s < TC.CMDS_MAX -> 0 <= j -> j <> s ->
  TW.Cmd_st (TW.set_Cmd_st B s v) j = TW.Cmd_st B j.
Proof. intros B s v j HL Hs Hj Hne. unfold TW.Cmd_st, TW.set_Cmd_st. apply s32_at_upd_out; cls_lia. Qed.

Lemma cls_len_set_st0 : forall B s v j, Z.of_nat (length B) = TW.W_LEN ->
  0 <= s < TC.CMDS_MAX -> 0 <= j -> TW.Cmd_len (TW.set_Cmd_st B s v) j = TW.Cmd_len B j.
Proof. intros B s v j HL Hs Hj. unfold TW.Cmd_len, TW.set_Cmd_st. apply u_at_upd_out; cls_lia. Qed.

Lemma cls_disp_set_st0 : forall B s v j, Z.of_nat (length B) = TW.W_LEN ->
  0 <= s < TC.CMDS_MAX -> 0 <= j -> TW.Cmd_display (TW.set_Cmd_st B s v) j = TW.Cmd_display B j.
Proof. intros B s v j HL Hs Hj. unfold TW.Cmd_display, TW.set_Cmd_st. apply s32_at_upd_out; cls_lia. Qed.

Lemma cls_st_set_nq0 : forall B v j, Z.of_nat (length B) = TW.W_LEN -> 0 <= j ->
  TW.Cmd_st (TW.set_g_nq B v) j = TW.Cmd_st B j.
Proof. intros B v j HL Hj. unfold TW.Cmd_st, TW.set_g_nq. apply s32_at_upd_out; cls_lia. Qed.

Lemma cls_len_set_nq0 : forall B v j, Z.of_nat (length B) = TW.W_LEN -> 0 <= j ->
  TW.Cmd_len (TW.set_g_nq B v) j = TW.Cmd_len B j.
Proof. intros B v j HL Hj. unfold TW.Cmd_len, TW.set_g_nq. apply u_at_upd_out; cls_lia. Qed.

Lemma cls_disp_set_nq0 : forall B v j, Z.of_nat (length B) = TW.W_LEN -> 0 <= j ->
  TW.Cmd_display (TW.set_g_nq B v) j = TW.Cmd_display B j.
Proof. intros B v j HL Hj. unfold TW.Cmd_display, TW.set_g_nq. apply s32_at_upd_out; cls_lia. Qed.

(* set_Cmd_st at s changes only Cmd_st at s *)
Lemma cls_st_set_st_eq : forall B s v, Z.of_nat (length B) = TW.W_LEN -> 0 <= s < TC.CMDS_MAX ->
  0 <= v < 2 ^ 31 -> TW.Cmd_st (TW.set_Cmd_st B s v) s = v.
Proof.
  intros B s v HL Hs Hv. unfold TW.Cmd_st, TW.set_Cmd_st. rewrite s32_at_upd_put by cls_lia.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma cls_st_set_st_ne : forall B s v j, Z.of_nat (length B) = TW.W_LEN ->
  0 <= s < TC.CMDS_MAX -> 0 <= j < TC.CMDS_MAX -> j <> s ->
  TW.Cmd_st (TW.set_Cmd_st B s v) j = TW.Cmd_st B j.
Proof. intros B s v j HL Hs Hj Hne. exact (cls_st_set_st_ne0 B s v j HL Hs (proj1 Hj) Hne). Qed.

Lemma cls_cmd_len_set_st : forall B s v j, Z.of_nat (length B) = TW.W_LEN ->
  0 <= s < TC.CMDS_MAX -> 0 <= j < TC.CMDS_MAX -> TW.Cmd_len (TW.set_Cmd_st B s v) j = TW.Cmd_len B j.
Proof. intros B s v j HL Hs Hj. exact (cls_len_set_st0 B s v j HL Hs (proj1 Hj)). Qed.

Lemma cls_cmd_display_set_st : forall B s v j, Z.of_nat (length B) = TW.W_LEN ->
  0 <= s < TC.CMDS_MAX -> 0 <= j < TC.CMDS_MAX ->
  TW.Cmd_display (TW.set_Cmd_st B s v) j = TW.Cmd_display B j.
Proof. intros B s v j HL Hs Hj. exact (cls_disp_set_st0 B s v j HL Hs (proj1 Hj)). Qed.

Lemma cls_g_ncmd_set_st : forall B s v, Z.of_nat (length B) = TW.W_LEN -> 0 <= s < TC.CMDS_MAX ->
  TW.g_ncmd (TW.set_Cmd_st B s v) = TW.g_ncmd B.
Proof. intros B s v HL Hs. unfold TW.g_ncmd, TW.set_Cmd_st. apply u_at_upd_out; cls_lia. Qed.

Lemma cls_g_nq_set_st : forall B s v, Z.of_nat (length B) = TW.W_LEN -> 0 <= s < TC.CMDS_MAX ->
  TW.g_nq (TW.set_Cmd_st B s v) = TW.g_nq B.
Proof. intros B s v HL Hs. unfold TW.g_nq, TW.set_Cmd_st. apply u_at_upd_out; cls_lia. Qed.

Lemma cls_q_at_set_st : forall B s v i, Z.of_nat (length B) = TW.W_LEN ->
  0 <= s < TC.CMDS_MAX -> 0 <= i < TC.CMDS_MAX -> TW.Q_at (TW.set_Cmd_st B s v) i = TW.Q_at B i.
Proof. intros B s v i HL Hs Hi. unfold TW.Q_at, TW.set_Cmd_st. apply u_at_upd_out; cls_lia. Qed.

(* set_Q_at at k changes only Q_at at k *)
Lemma cls_q_at_set_q_eq : forall B k v, Z.of_nat (length B) = TW.W_LEN -> 0 <= k < TC.CMDS_MAX ->
  0 <= v < 2 ^ 32 -> TW.Q_at (TW.set_Q_at B k v) k = v.
Proof.
  intros B k v HL Hk Hv. unfold TW.Q_at, TW.set_Q_at. rewrite u_at_upd_put by cls_lia.
  change (8 * Z.of_nat 4) with 32. apply Z.mod_small. exact Hv.
Qed.

Lemma cls_q_at_set_q_ne : forall B k v i, Z.of_nat (length B) = TW.W_LEN ->
  0 <= k < TC.CMDS_MAX -> 0 <= i < TC.CMDS_MAX -> i <> k -> TW.Q_at (TW.set_Q_at B k v) i = TW.Q_at B i.
Proof. intros B k v i HL Hk Hi Hne. unfold TW.Q_at, TW.set_Q_at. apply u_at_upd_out; cls_lia. Qed.

Lemma cls_cmd_set_q : forall B k v j, Z.of_nat (length B) = TW.W_LEN ->
  0 <= k < TC.CMDS_MAX -> 0 <= j < TC.CMDS_MAX ->
  TW.Cmd_st (TW.set_Q_at B k v) j = TW.Cmd_st B j /\ TW.Cmd_len (TW.set_Q_at B k v) j = TW.Cmd_len B j /\
  TW.Cmd_display (TW.set_Q_at B k v) j = TW.Cmd_display B j.
Proof.
  intros B k v j HL Hk Hj. split; [|split].
  - unfold TW.Cmd_st, TW.set_Q_at. apply s32_at_upd_out; cls_lia.
  - unfold TW.Cmd_len, TW.set_Q_at. apply u_at_upd_out; cls_lia.
  - unfold TW.Cmd_display, TW.set_Q_at. apply s32_at_upd_out; cls_lia.
Qed.

Lemma cls_g_set_q : forall B k v, Z.of_nat (length B) = TW.W_LEN -> 0 <= k < TC.CMDS_MAX ->
  TW.g_ncmd (TW.set_Q_at B k v) = TW.g_ncmd B /\ TW.g_nq (TW.set_Q_at B k v) = TW.g_nq B.
Proof.
  intros B k v HL Hk. split.
  - unfold TW.g_ncmd, TW.set_Q_at. apply u_at_upd_out; cls_lia.
  - unfold TW.g_nq, TW.set_Q_at. apply u_at_upd_out; cls_lia.
Qed.

(* set_g_nq changes only g_nq *)
Lemma cls_cmd_set_nq : forall B v j, Z.of_nat (length B) = TW.W_LEN -> 0 <= j < TC.CMDS_MAX ->
  TW.Cmd_st (TW.set_g_nq B v) j = TW.Cmd_st B j /\ TW.Cmd_len (TW.set_g_nq B v) j = TW.Cmd_len B j /\
  TW.Cmd_display (TW.set_g_nq B v) j = TW.Cmd_display B j.
Proof.
  intros B v j HL Hj.
  exact (conj (cls_st_set_nq0 B v j HL (proj1 Hj))
           (conj (cls_len_set_nq0 B v j HL (proj1 Hj)) (cls_disp_set_nq0 B v j HL (proj1 Hj)))).
Qed.

Lemma cls_q_at_set_nq : forall B v i, Z.of_nat (length B) = TW.W_LEN -> 0 <= i < TC.CMDS_MAX ->
  TW.Q_at (TW.set_g_nq B v) i = TW.Q_at B i.
Proof. intros B v i HL Hi. unfold TW.Q_at, TW.set_g_nq. apply u_at_upd_out; cls_lia. Qed.

Lemma cls_g_ncmd_set_nq : forall B v, Z.of_nat (length B) = TW.W_LEN -> TW.g_ncmd (TW.set_g_nq B v) = TW.g_ncmd B.
Proof. intros B v HL. unfold TW.g_ncmd, TW.set_g_nq. apply u_at_upd_out; cls_lia. Qed.

Lemma cls_g_nq_set_nq : forall B v, Z.of_nat (length B) = TW.W_LEN -> 0 <= v < 2 ^ 32 ->
  TW.g_nq (TW.set_g_nq B v) = v.
Proof.
  intros B v HL Hv. unfold TW.g_nq, TW.set_g_nq. rewrite u_at_upd_put by cls_lia.
  change (8 * Z.of_nat 4) with 32. apply Z.mod_small. exact Hv.
Qed.

(* n <= 28: g_cmd[j].bytes + 28 is g_cmd[j + 1].st *)
Lemma cls_sub_set_st : forall B s v j n, Z.of_nat (length B) = TW.W_LEN ->
  0 <= s < TC.CMDS_MAX -> 0 <= j < TC.CMDS_MAX -> (n <= 28)%nat ->
  TW.sub (TW.set_Cmd_st B s v) (TW.A_Cmd_bytes j) n = TW.sub B (TW.A_Cmd_bytes j) n.
Proof. intros B s v j n HL Hs Hj Hn. unfold TW.set_Cmd_st. apply sub_upd_out; cls_lia. Qed.

(* ---- 4. the PENDING-command invariant ---- *)

(* the contract's premise *)
Definition cls_inv (B : list byte) : Prop :=
  forall s, 0 <= s < TW.g_ncmd B -> TW.Cmd_st B s = TC.PENDING -> TW.Cmd_len B s <= DSpec.SPEC_CMD_MAX.

(* the form the walk carries: the commands inside g_cmd's payload, the only ones tagged_of_m returns *)
Definition cls_inv_c (B : list byte) : Prop :=
  forall s, 0 <= s < TW.g_ncmd B -> s < TC.CMDS_MAX -> TW.Cmd_st B s = TC.PENDING ->
  TW.Cmd_len B s <= DSpec.SPEC_CMD_MAX.

Lemma cls_inv_to_c : forall B, cls_inv B -> cls_inv_c B.
Proof. intros B I s Hs _ Hst. exact (I s Hs Hst). Qed.

Lemma cls_inv_set_st : forall B s, Z.of_nat (length B) = TW.W_LEN -> 0 <= s < TC.CMDS_MAX ->
  cls_inv B -> cls_inv (TW.set_Cmd_st B s TC.SENT).
Proof.
  intros B s HL Hs I s' Hs' Hst.
  rewrite (cls_g_ncmd_set_st B s TC.SENT HL Hs) in Hs'.
  destruct (Z.eq_dec s' s) as [E|Hne].
  - subst s'. rewrite (cls_st_set_st_eq B s TC.SENT HL Hs ltac:(unfold TC.SENT; lia)) in Hst.
    unfold TC.SENT, TC.PENDING in Hst. discriminate Hst.
  - rewrite (cls_st_set_st_ne0 B s TC.SENT s' HL Hs (proj1 Hs') Hne) in Hst.
    rewrite (cls_len_set_st0 B s TC.SENT s' HL Hs (proj1 Hs')).
    exact (I s' Hs' Hst).
Qed.

(* g_ncmd <= CMDS_MAX: g_cmd[1024 ..] read g_q's bytes, which the store changes *)
Lemma cls_inv_set_q : forall B k v, Z.of_nat (length B) = TW.W_LEN -> 0 <= k < TC.CMDS_MAX ->
  TW.g_ncmd B <= TC.CMDS_MAX -> cls_inv B -> cls_inv (TW.set_Q_at B k v).
Proof.
  intros B k v HL Hk HN I s' Hs' Hst.
  rewrite (proj1 (cls_g_set_q B k v HL Hk)) in Hs'.
  destruct (cls_cmd_set_q B k v s' HL Hk ltac:(lia)) as (E1 & E2 & _).
  rewrite E1 in Hst. rewrite E2. exact (I s' Hs' Hst).
Qed.

Lemma cls_inv_set_nq : forall B v, Z.of_nat (length B) = TW.W_LEN -> cls_inv B -> cls_inv (TW.set_g_nq B v).
Proof.
  intros B v HL I s' Hs' Hst.
  rewrite (cls_g_ncmd_set_nq B v HL) in Hs'.
  rewrite (cls_st_set_nq0 B v s' HL (proj1 Hs')) in Hst.
  rewrite (cls_len_set_nq0 B v s' HL (proj1 Hs')).
  exact (I s' Hs' Hst).
Qed.

Lemma cls_inv_c_set_st : forall B s, Z.of_nat (length B) = TW.W_LEN -> 0 <= s < TC.CMDS_MAX ->
  cls_inv_c B -> cls_inv_c (TW.set_Cmd_st B s TC.SENT).
Proof.
  intros B s HL Hs I s' Hs' Hc Hst.
  rewrite (cls_g_ncmd_set_st B s TC.SENT HL Hs) in Hs'.
  destruct (Z.eq_dec s' s) as [E|Hne].
  - subst s'. rewrite (cls_st_set_st_eq B s TC.SENT HL Hs ltac:(unfold TC.SENT; lia)) in Hst.
    unfold TC.SENT, TC.PENDING in Hst. discriminate Hst.
  - rewrite (cls_st_set_st_ne0 B s TC.SENT s' HL Hs (proj1 Hs') Hne) in Hst.
    rewrite (cls_len_set_st0 B s TC.SENT s' HL Hs (proj1 Hs')).
    exact (I s' Hs' Hc Hst).
Qed.

Lemma cls_inv_c_set_q : forall B k v, Z.of_nat (length B) = TW.W_LEN -> 0 <= k < TC.CMDS_MAX ->
  cls_inv_c B -> cls_inv_c (TW.set_Q_at B k v).
Proof.
  intros B k v HL Hk I s' Hs' Hc Hst.
  rewrite (proj1 (cls_g_set_q B k v HL Hk)) in Hs'.
  destruct (cls_cmd_set_q B k v s' HL Hk ltac:(lia)) as (E1 & E2 & _).
  rewrite E1 in Hst. rewrite E2. exact (I s' Hs' Hc Hst).
Qed.

Lemma cls_inv_c_set_nq : forall B v, Z.of_nat (length B) = TW.W_LEN -> cls_inv_c B -> cls_inv_c (TW.set_g_nq B v).
Proof.
  intros B v HL I s' Hs' Hc Hst.
  rewrite (cls_g_ncmd_set_nq B v HL) in Hs'.
  rewrite (cls_st_set_nq0 B v s' HL (proj1 Hs')) in Hst.
  rewrite (cls_len_set_nq0 B v s' HL (proj1 Hs')).
  exact (I s' Hs' Hc Hst).
Qed.

(* ---- 5. a whole q_remove run and a whole round, for any world predicate P the stores keep ---- *)

Lemma cls_q_loop_gen : forall (P : list byte -> Prop),
  (forall X k v, Z.of_nat (length X) = TW.W_LEN -> 0 <= k < TC.CMDS_MAX -> P X -> P (TW.set_Q_at X k v)) ->
  forall fuel B s nq i k B' k',
  TC.q_remove_loop fuel B s nq i k = Some (B', k') ->
  Z.of_nat (length B) = TW.W_LEN -> 0 <= k <= i -> 0 <= i -> P B ->
  Z.of_nat (length B') = TW.W_LEN /\ P B' /\ k <= k' /\ k' <= k + Z.max 0 (nq - i) /\
  TW.g_ncmd B' = TW.g_ncmd B /\ TW.g_nq B' = TW.g_nq B /\
  (forall j, 0 <= j < TC.CMDS_MAX -> TW.Cmd_st B' j = TW.Cmd_st B j) /\
  (forall j, 0 <= j < TC.CMDS_MAX -> TW.Cmd_len B' j = TW.Cmd_len B j) /\
  (forall j, 0 <= j < TC.CMDS_MAX -> TW.Cmd_display B' j = TW.Cmd_display B j).
Proof.
  intros P PQ fuel. induction fuel as [|fuel IH]; intros B s nq i k B' k' H HL Hk Hi HP; [discriminate H|].
  destruct (Z.ltb_spec i nq) as [L|L].
  - cbn [TC.q_remove_loop] in H. rewrite (proj2 (Z.ltb_lt _ _) L) in H.
    destruct (TC.CMDS_MAX <=? i) eqn:C; [discriminate H|]. apply Z.leb_gt in C.
    destruct (TW.Q_at B i =? s).
    + destruct (IH B s nq (i + 1) k B' k' H HL ltac:(lia) ltac:(lia) HP)
        as (L1 & P1 & K1 & K2 & G1 & G2 & S1 & S2 & S3).
      refine (conj L1 (conj P1 (conj K1 (conj _ (conj G1 (conj G2 (conj S1 (conj S2 S3)))))))). lia.
    + assert (Hk' : 0 <= k < TC.CMDS_MAX) by lia.
      pose proof (cls_len_set_q B k (TW.Q_at B i) HL Hk') as L0.
      pose proof (PQ B k (TW.Q_at B i) HL Hk' HP) as P0.
      destruct (IH (TW.set_Q_at B k (TW.Q_at B i)) s nq (i + 1) (k + 1) B' k' H L0 ltac:(lia) ltac:(lia) P0)
        as (L1 & P1 & K1 & K2 & G1 & G2 & S1 & S2 & S3).
      destruct (cls_g_set_q B k (TW.Q_at B i) HL Hk') as [GN GQ].
      refine (conj L1 (conj P1 (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))).
      * lia.
      * lia.
      * rewrite G1. exact GN.
      * rewrite G2. exact GQ.
      * intros j Hj. rewrite (S1 j Hj). exact (proj1 (cls_cmd_set_q B k (TW.Q_at B i) j HL Hk' Hj)).
      * intros j Hj. rewrite (S2 j Hj). exact (proj1 (proj2 (cls_cmd_set_q B k (TW.Q_at B i) j HL Hk' Hj))).
      * intros j Hj. rewrite (S3 j Hj). exact (proj2 (proj2 (cls_cmd_set_q B k (TW.Q_at B i) j HL Hk' Hj))).
  - destruct (cls_q_exit (S fuel) B s nq i k B' k' H L) as [E1 E2]. subst B' k'.
    refine (conj HL (conj HP (conj (Z.le_refl k) (conj _ (conj eq_refl (conj eq_refl
              (conj (fun j _ => eq_refl) (conj (fun j _ => eq_refl) (fun j _ => eq_refl))))))))).
    lia.
Qed.

Lemma cls_qrm_gen : forall (P : list byte -> Prop),
  (forall X k v, Z.of_nat (length X) = TW.W_LEN -> 0 <= k < TC.CMDS_MAX -> P X -> P (TW.set_Q_at X k v)) ->
  (forall X v, Z.of_nat (length X) = TW.W_LEN -> P X -> P (TW.set_g_nq X v)) ->
  forall B s B2, TC.q_remove_m B s = Some (B2, tt) -> Z.of_nat (length B) = TW.W_LEN -> P B ->
  Z.of_nat (length B2) = TW.W_LEN /\ P B2 /\ TW.g_ncmd B2 = TW.g_ncmd B /\
  (forall j, 0 <= j < TC.CMDS_MAX -> TW.Cmd_st B2 j = TW.Cmd_st B j) /\
  (forall j, 0 <= j < TC.CMDS_MAX -> TW.Cmd_len B2 j = TW.Cmd_len B j) /\
  (forall j, 0 <= j < TC.CMDS_MAX -> TW.Cmd_display B2 j = TW.Cmd_display B j) /\
  TW.g_nq B2 <= TC.CMDS_MAX /\ 0 <= TW.g_nq B2.
Proof.
  intros P PQ PN B s B2 H HL HP.
  destruct (cls_qrm B s B2 H) as (B1 & k & HQ & HB2). subst B2.
  pose proof (cls_q_nqle _ _ _ _ _ _ _ _ HQ ltac:(unfold TC.CMDS_MAX; lia)) as NQ.
  pose proof (cls_g_nq_range B) as RNQ.
  destruct (cls_q_loop_gen P PQ _ B s (TW.g_nq B) 0 0 B1 k HQ HL ltac:(lia) ltac:(lia) HP)
    as (L1 & P1 & K1 & K2 & G1 & G2 & S1 & S2 & S3).
  assert (Hk : 0 <= k < 2 ^ 32) by (unfold TC.CMDS_MAX in NQ; lia).
  refine (conj (cls_len_set_nq B1 k L1) (conj (PN B1 k L1 P1) (conj _ (conj _ (conj _ (conj _ _)))))).
  - rewrite (cls_g_ncmd_set_nq B1 k L1). exact G1.
  - intros j Hj. rewrite (proj1 (cls_cmd_set_nq B1 k j L1 Hj)). exact (S1 j Hj).
  - intros j Hj. rewrite (proj1 (proj2 (cls_cmd_set_nq B1 k j L1 Hj))). exact (S2 j Hj).
  - intros j Hj. rewrite (proj2 (proj2 (cls_cmd_set_nq B1 k j L1 Hj))). exact (S3 j Hj).
  - rewrite (cls_g_nq_set_nq B1 k L1 Hk). unfold TC.CMDS_MAX in NQ |- *. lia.
Qed.

Lemma cls_round_gen : forall (P : list byte -> Prop),
  (forall X k v, Z.of_nat (length X) = TW.W_LEN -> 0 <= k < TC.CMDS_MAX -> P X -> P (TW.set_Q_at X k v)) ->
  (forall X v, Z.of_nat (length X) = TW.W_LEN -> P X -> P (TW.set_g_nq X v)) ->
  (forall X s, Z.of_nat (length X) = TW.W_LEN -> 0 <= s < TC.CMDS_MAX -> P X -> P (TW.set_Cmd_st X s TC.SENT)) ->
  forall Bc s B2, Z.of_nat (length Bc) = TW.W_LEN -> P Bc ->
  0 <= s < TC.CMDS_MAX -> TC.q_remove_m (TW.set_Cmd_st Bc s TC.SENT) s = Some (B2, tt) ->
  Z.of_nat (length B2) = TW.W_LEN /\ P B2 /\ TW.g_ncmd B2 = TW.g_ncmd Bc /\
  (forall j, 0 <= j < TC.CMDS_MAX -> TW.Cmd_len B2 j = TW.Cmd_len Bc j) /\
  (forall j, 0 <= j < TC.CMDS_MAX -> j <> s -> TW.Cmd_st B2 j = TW.Cmd_st Bc j) /\
  TW.Cmd_st B2 s = TC.SENT /\
  (forall j, 0 <= j < TC.CMDS_MAX -> TW.Cmd_display B2 j = TW.Cmd_display Bc j) /\
  0 <= TW.g_nq B2 <= TC.CMDS_MAX.
Proof.
  intros P PQ PN PS Bc s B2 HL HP Hs H.
  pose proof (cls_len_set_st Bc s TC.SENT HL Hs) as L1.
  destruct (cls_qrm_gen P PQ PN _ s B2 H L1 (PS Bc s HL Hs HP)) as (L2 & P2 & G2 & S1 & S2 & S3 & N1 & N2).
  refine (conj L2 (conj P2 (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
  - rewrite G2. exact (cls_g_ncmd_set_st Bc s TC.SENT HL Hs).
  - intros j Hj. rewrite (S2 j Hj). exact (cls_cmd_len_set_st Bc s TC.SENT j HL Hs Hj).
  - intros j Hj Hne. rewrite (S1 j Hj). exact (cls_st_set_st_ne Bc s TC.SENT j HL Hs Hj Hne).
  - rewrite (S1 s Hs). apply cls_st_set_st_eq; [exact HL | exact Hs | unfold TC.SENT; lia].
  - intros j Hj. rewrite (S3 j Hj). exact (cls_cmd_display_set_st Bc s TC.SENT j HL Hs Hj).
  - lia.
Qed.

(* the walk's forms: cls_inv_c, no bound on g_ncmd *)
Lemma cls_q_loop_facts_c : forall fuel B s nq i k B' k',
  TC.q_remove_loop fuel B s nq i k = Some (B', k') ->
  Z.of_nat (length B) = TW.W_LEN -> 0 <= k <= i -> 0 <= i -> cls_inv_c B ->
  Z.of_nat (length B') = TW.W_LEN /\ cls_inv_c B' /\ k <= k' /\ k' <= k + Z.max 0 (nq - i) /\
  TW.g_ncmd B' = TW.g_ncmd B /\ TW.g_nq B' = TW.g_nq B /\
  (forall j, 0 <= j < TC.CMDS_MAX -> TW.Cmd_st B' j = TW.Cmd_st B j) /\
  (forall j, 0 <= j < TC.CMDS_MAX -> TW.Cmd_len B' j = TW.Cmd_len B j) /\
  (forall j, 0 <= j < TC.CMDS_MAX -> TW.Cmd_display B' j = TW.Cmd_display B j).
Proof.
  intros fuel B s nq i k B' k' H HL Hk Hi I.
  exact (cls_q_loop_gen cls_inv_c cls_inv_c_set_q fuel B s nq i k B' k' H HL Hk Hi I).
Qed.

Lemma cls_qrm_facts_c : forall B s B2, TC.q_remove_m B s = Some (B2, tt) ->
  Z.of_nat (length B) = TW.W_LEN -> cls_inv_c B ->
  Z.of_nat (length B2) = TW.W_LEN /\ cls_inv_c B2 /\ TW.g_ncmd B2 = TW.g_ncmd B /\
  (forall j, 0 <= j < TC.CMDS_MAX -> TW.Cmd_st B2 j = TW.Cmd_st B j) /\
  (forall j, 0 <= j < TC.CMDS_MAX -> TW.Cmd_len B2 j = TW.Cmd_len B j) /\
  (forall j, 0 <= j < TC.CMDS_MAX -> TW.Cmd_display B2 j = TW.Cmd_display B j) /\
  TW.g_nq B2 <= TC.CMDS_MAX /\ 0 <= TW.g_nq B2.
Proof.
  intros B s B2 H HL I.
  exact (cls_qrm_gen cls_inv_c cls_inv_c_set_q cls_inv_c_set_nq B s B2 H HL I).
Qed.

Lemma cls_round_inv_c : forall Bc s B2, Z.of_nat (length Bc) = TW.W_LEN -> cls_inv_c Bc ->
  0 <= s < TC.CMDS_MAX -> TC.q_remove_m (TW.set_Cmd_st Bc s TC.SENT) s = Some (B2, tt) ->
  Z.of_nat (length B2) = TW.W_LEN /\ cls_inv_c B2 /\ TW.g_ncmd B2 = TW.g_ncmd Bc /\
  (forall j, 0 <= j < TC.CMDS_MAX -> TW.Cmd_len B2 j = TW.Cmd_len Bc j) /\
  (forall j, 0 <= j < TC.CMDS_MAX -> j <> s -> TW.Cmd_st B2 j = TW.Cmd_st Bc j) /\
  TW.Cmd_st B2 s = TC.SENT /\
  (forall j, 0 <= j < TC.CMDS_MAX -> TW.Cmd_display B2 j = TW.Cmd_display Bc j) /\
  0 <= TW.g_nq B2 <= TC.CMDS_MAX.
Proof.
  intros Bc s B2 HL I Hs H.
  exact (cls_round_gen cls_inv_c cls_inv_c_set_q cls_inv_c_set_nq cls_inv_c_set_st Bc s B2 HL I Hs H).
Qed.

(* the cls_inv forms: they need g_ncmd <= CMDS_MAX (cls_inv_set_q) *)
Lemma cls_pinv_set_q : forall X k v, Z.of_nat (length X) = TW.W_LEN -> 0 <= k < TC.CMDS_MAX ->
  TW.g_ncmd X <= TC.CMDS_MAX /\ cls_inv X ->
  TW.g_ncmd (TW.set_Q_at X k v) <= TC.CMDS_MAX /\ cls_inv (TW.set_Q_at X k v).
Proof.
  intros X k v HL Hk [HN I]. rewrite (proj1 (cls_g_set_q X k v HL Hk)).
  exact (conj HN (cls_inv_set_q X k v HL Hk HN I)).
Qed.

Lemma cls_pinv_set_nq : forall X v, Z.of_nat (length X) = TW.W_LEN ->
  TW.g_ncmd X <= TC.CMDS_MAX /\ cls_inv X ->
  TW.g_ncmd (TW.set_g_nq X v) <= TC.CMDS_MAX /\ cls_inv (TW.set_g_nq X v).
Proof.
  intros X v HL [HN I]. rewrite (cls_g_ncmd_set_nq X v HL).
  exact (conj HN (cls_inv_set_nq X v HL I)).
Qed.

Lemma cls_pinv_set_st : forall X s, Z.of_nat (length X) = TW.W_LEN -> 0 <= s < TC.CMDS_MAX ->
  TW.g_ncmd X <= TC.CMDS_MAX /\ cls_inv X ->
  TW.g_ncmd (TW.set_Cmd_st X s TC.SENT) <= TC.CMDS_MAX /\ cls_inv (TW.set_Cmd_st X s TC.SENT).
Proof.
  intros X s HL Hs [HN I]. rewrite (cls_g_ncmd_set_st X s TC.SENT HL Hs).
  exact (conj HN (cls_inv_set_st X s HL Hs I)).
Qed.

Lemma cls_q_loop_facts : forall fuel B s nq i k B' k',
  TC.q_remove_loop fuel B s nq i k = Some (B', k') ->
  Z.of_nat (length B) = TW.W_LEN -> 0 <= k <= i -> 0 <= i -> TW.g_ncmd B <= TC.CMDS_MAX -> cls_inv B ->
  Z.of_nat (length B') = TW.W_LEN /\ cls_inv B' /\ k <= k' /\ k' <= k + Z.max 0 (nq - i) /\
  TW.g_ncmd B' = TW.g_ncmd B /\ TW.g_nq B' = TW.g_nq B /\
  (forall j, 0 <= j < TC.CMDS_MAX -> TW.Cmd_st B' j = TW.Cmd_st B j) /\
  (forall j, 0 <= j < TC.CMDS_MAX -> TW.Cmd_len B' j = TW.Cmd_len B j) /\
  (forall j, 0 <= j < TC.CMDS_MAX -> TW.Cmd_display B' j = TW.Cmd_display B j).
Proof.
  intros fuel B s nq i k B' k' H HL Hk Hi HN I.
  destruct (cls_q_loop_gen (fun X => TW.g_ncmd X <= TC.CMDS_MAX /\ cls_inv X) cls_pinv_set_q
              fuel B s nq i k B' k' H HL Hk Hi (conj HN I)) as (L1 & [_ I1] & R).
  exact (conj L1 (conj I1 R)).
Qed.

Lemma cls_qrm_facts : forall B s B2, TC.q_remove_m B s = Some (B2, tt) ->
  Z.of_nat (length B) = TW.W_LEN -> TW.g_ncmd B <= TC.CMDS_MAX -> cls_inv B ->
  Z.of_nat (length B2) = TW.W_LEN /\ cls_inv B2 /\ TW.g_ncmd B2 = TW.g_ncmd B /\
  (forall j, 0 <= j < TC.CMDS_MAX -> TW.Cmd_st B2 j = TW.Cmd_st B j) /\
  (forall j, 0 <= j < TC.CMDS_MAX -> TW.Cmd_len B2 j = TW.Cmd_len B j) /\
  (forall j, 0 <= j < TC.CMDS_MAX -> TW.Cmd_display B2 j = TW.Cmd_display B j) /\
  TW.g_nq B2 <= TC.CMDS_MAX /\ 0 <= TW.g_nq B2.
Proof.
  intros B s B2 H HL HN I.
  destruct (cls_qrm_gen (fun X => TW.g_ncmd X <= TC.CMDS_MAX /\ cls_inv X) cls_pinv_set_q cls_pinv_set_nq
              B s B2 H HL (conj HN I)) as (L2 & [_ I2] & R).
  exact (conj L2 (conj I2 R)).
Qed.

Lemma cls_round_inv : forall Bc s B2, Z.of_nat (length Bc) = TW.W_LEN -> TW.g_ncmd Bc <= TC.CMDS_MAX ->
  cls_inv Bc -> 0 <= s < TC.CMDS_MAX -> TC.q_remove_m (TW.set_Cmd_st Bc s TC.SENT) s = Some (B2, tt) ->
  Z.of_nat (length B2) = TW.W_LEN /\ cls_inv B2 /\ TW.g_ncmd B2 = TW.g_ncmd Bc /\
  (forall j, 0 <= j < TC.CMDS_MAX -> TW.Cmd_len B2 j = TW.Cmd_len Bc j) /\
  (forall j, 0 <= j < TC.CMDS_MAX -> j <> s -> TW.Cmd_st B2 j = TW.Cmd_st Bc j) /\
  TW.Cmd_st B2 s = TC.SENT /\
  (forall j, 0 <= j < TC.CMDS_MAX -> TW.Cmd_display B2 j = TW.Cmd_display Bc j) /\
  0 <= TW.g_nq B2 <= TC.CMDS_MAX.
Proof.
  intros Bc s B2 HL HN I Hs H.
  destruct (cls_round_gen (fun X => TW.g_ncmd X <= TC.CMDS_MAX /\ cls_inv X) cls_pinv_set_q cls_pinv_set_nq
              cls_pinv_set_st Bc s B2 HL (conj HN I) Hs H) as (L2 & [_ I2] & R).
  exact (conj L2 (conj I2 R)).
Qed.

(* ---- 6. the body slice ---- *)

Lemma cls_body_sub_len : forall (body : list byte) pos n,
  0 <= pos -> (Z.to_nat pos + n <= length body)%nat -> length (TW.sub body pos n) = n.
Proof. intros body pos n Hp Hn. unfold TW.sub. rewrite length_firstn, length_skipn. lia. Qed.
