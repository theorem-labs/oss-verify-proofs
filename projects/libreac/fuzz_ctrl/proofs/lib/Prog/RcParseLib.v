From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcLib RcParse.
Import ListNotations.
Open Scope Z_scope.

Lemma rc_ltu64 : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 ->
  bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma rc_eqb64 : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma rc_eqb_zxb : forall (b : byte) c, 0 <= c < 2^64 ->
  bv_eqb (zxb b) (Z_to_bv 64 c) = (bv_unsigned b =? c).
Proof.
  intros b c Hc. unfold zxb. pose proof (byte_range b). apply rc_eqb64; lia.
Qed.

Lemma rc_le4_small : forall k, 0 <= k < 256 ->
  le4 (Z_to_bv 64 k) = [Z_to_bv 8 k; cp_z; cp_z; cp_z].
Proof.
  intros k Hk. unfold le4. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes].
  rewrite (Z.shiftr_div_pow2 k 8) by lia. rewrite (Z.div_small k (2^8)) by (cbn; lia). reflexivity.
Qed.

Lemma rc_le2_pair : forall (lo hi : byte),
  le2 (Z_to_bv 64 (bv_unsigned hi * 256 + bv_unsigned lo)) = [lo; hi].
Proof.
  intros lo hi. pose proof (byte_range lo) as Rl. pose proof (byte_range hi) as Rh.
  unfold le2. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes].
  rewrite (Z.shiftr_div_pow2 _ 8) by lia. change (2^8) with 256.
  replace ((bv_unsigned hi * 256 + bv_unsigned lo) / 256) with (bv_unsigned hi)
    by (rewrite Z.div_add_l by lia; rewrite Z.div_small by lia; lia).
  f_equal; [|f_equal].
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
    rewrite Z.add_comm, Z.mod_add by lia. apply Z.mod_small; lia.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
    apply Z.mod_small; lia.
Qed.

Lemma rc_le1_zxb : forall b : byte, le1 (zxb b) = [b].
Proof. exact le1_zxb. Qed.

Lemma rc_beq0_true : forall o, o = 0 -> bv_eqb (Z_to_bv 64 o) (Z_to_bv 64 0) = true.
Proof. intros o ->. reflexivity. Qed.

Lemma rc_beq0_false : forall o, o <> 0 -> 0 <= o < 2^64 -> bv_eqb (Z_to_bv 64 o) (Z_to_bv 64 0) = false.
Proof. intros o H R. rewrite rc_eqb64 by lia. apply Z.eqb_neq. exact H. Qed.

Lemma rc_signed_zxb : forall b : byte, bv_signed (zxb b) = bv_unsigned b.
Proof.
  intros b. unfold zxb. pose proof (byte_range b). rewrite zb_signed. rewrite unsigned_lit by lia.
  replace (bv_unsigned b <? 2^63) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma rc_rw_split : forall m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) ->
  rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[Hwf Hb] (Ha & Hn & Hw)].
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite cells_size_app in Hn, Hw.
  split.
  - split; [split; assumption|]. split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
  - split; [split; [assumption|]|].
    + rewrite cells_bytes_length in B2 by assumption. exact B2.
    + split; [lia|]. split; [lia|]. intros i Hi.
      replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia.
      apply Hw. lia.
Qed.

Lemma rc_rw_join : forall m A B cs1 cs2,
  rw_cells segs m A cs1 -> B = A + Z.of_nat (cells_size cs1) -> rw_cells segs m B cs2 ->
  rw_cells segs m A (cs1 ++ cs2).
Proof.
  intros m A B cs1 cs2 [[W1 B1] (Ha & Hn & Hw1)] -> [[W2 B2] (Hb & Hn2 & Hw2)].
  split; [split|].
  - apply cells_wf_app. tauto.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|].
    rewrite cells_bytes_length by exact W1. exact B2.
  - rewrite cells_size_app. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.ltb_spec i (Z.of_nat (cells_size cs1))).
    + apply Hw1. lia.
    + replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia.
      apply Hw2. lia.
Qed.

Lemma rc_rw_rebytes : forall m A cs cs',
  rw_cells segs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells segs m A cs'.
Proof.
  intros m A cs cs' [[Hwf Hb] Hw] Hwf' Heq. split; [split; [exact Hwf' | rewrite Heq; exact Hb] |].
  rewrite <- (cells_bytes_length cs') by assumption. rewrite Heq. rewrite cells_bytes_length by assumption. exact Hw.
Qed.

Lemma rc_rw_flat : forall m A cs bs,
  rw_cells segs m A cs -> cells_bytes cs = bs -> rw_cells segs m A [CB (length bs) bs].
Proof.
  intros m A cs bs H E. eapply rc_rw_rebytes; [exact H| cbn; split; reflexivity|].
  cbn [cells_bytes cbytes]. rewrite app_nil_r. symmetry. exact E.
Qed.

Lemma rc_rw_cut : forall m A n1 n2 l1 l2,
  rw_cells segs m A [CB n2 (l1 ++ l2)] -> length l1 = n1 ->
  rw_cells segs m A [CB n1 l1] /\ rw_cells segs m (A + Z.of_nat n1) [CB (n2 - n1) l2].
Proof.
  intros m A n1 n2 l1 l2 H L.
  assert (W : cells_wf [CB n2 (l1 ++ l2)]) by (destruct H as [[X _] _]; exact X).
  cbn in W. destruct W as [W _]. rewrite app_length in W.
  assert (H' : rw_cells segs m A ([CB n1 l1] ++ [CB (n2 - n1) l2])).
  { eapply rc_rw_rebytes; [exact H| cbn; repeat split; lia|]. cbn [cells_bytes cbytes app].
    rewrite !app_nil_r. reflexivity. }
  apply rc_rw_split in H'. cbn [cells_size csize] in H'. rewrite Nat.add_0_r in H'. exact H'.
Qed.

Lemma rc_stk_call : forall m m' lo hi a e len bs,
  stk segs m lo hi -> munch [(a, e)] m m' -> wmono segs m m' -> rw_cells segs m' a [CB len bs] ->
  e <= a + Z.of_nat len -> stk segs m' lo hi.
Proof.
  intros m m' lo hi a e len bs (H1 & H2 & H) MU WM RW He. split; [lia|]. split; [lia|].
  intros x Hx. destruct (H x Hx) as [Hw [b Hb]]. split; [apply WM; exact Hw|].
  destruct RW as [[Wf (Ha & Hl & Hr)] _]. cbn in Wf. destruct Wf as [Wf _].
  cbn [cells_bytes cbytes] in Hl, Hr. rewrite app_nil_r in Hl, Hr.
  destruct (Z.ltb_spec x a) as [Lx|Lx]; [|destruct (Z.ltb_spec x e) as [Ux|Ux]].
  - exists b. unfold mrd in *. rewrite (MU (wa x)); [exact Hb|]. rewrite wa_unsigned by lia. cbn. lia.
  - assert (Hi : (Z.to_nat (x - a) < length bs)%nat) by lia.
    pose proof (Hr (Z.to_nat (x - a)) Hi) as R. rewrite Z2Nat.id in R by lia.
    replace (a + (x - a)) with x in R by lia. rewrite R.
    destruct (nth_error bs (Z.to_nat (x - a))) eqn:E; [eexists; reflexivity|].
    apply nth_error_None in E. lia.
  - exists b. unfold mrd in *. rewrite (MU (wa x)); [exact Hb|]. rewrite wa_unsigned by lia. cbn. lia.
Qed.

Lemma rc_c1_bytes : forall bs, cells_bytes (map C1 bs) = bs.
Proof. induction bs as [|b bs IH]; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.

Lemma rc_c1_wf : forall bs, cells_wf (map C1 bs).
Proof. induction bs as [|b bs IH]; [exact I|]. split; [exact I|exact IH]. Qed.

Lemma rc_c1_size : forall bs, cells_size (map C1 bs) = length bs.
Proof. induction bs as [|b bs IH]; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.

Lemma rc_ro_now : forall W m0 m f fr (lo len : nat) rdl,
  (forall i, In i rdl -> mrd segs m0 (wa (f + Z.of_nat i)) = nth_error fr i) ->
  (forall j, (j < len)%nat -> In (lo + j)%nat rdl) ->
  (lo + len <= length fr)%nat -> 0 <= f -> f + Z.of_nat (length fr) <= 2^64 ->
  munch W m0 m -> disjoint_from W (f + Z.of_nat lo) (Z.of_nat len) ->
  ro_cells segs m (f + Z.of_nat lo) (map C1 (map (cp_b fr) (seq lo len))).
Proof.
  intros W m0 m f fr lo len rdl Hrd Hin Hl Hf Hfe MU D.
  eapply ro_cells_transport; [| exact MU |]; cycle 1.
  { rewrite rc_c1_size, map_length, seq_length. exact D. }
  split; [apply rc_c1_wf|]. rewrite rc_c1_bytes.
  split; [lia|]. split; [rewrite map_length, seq_length; lia|].
  intros i Hi. rewrite map_length, seq_length in Hi.
  replace (f + Z.of_nat lo + Z.of_nat i) with (f + Z.of_nat (lo + i)) by lia.
  rewrite Hrd by (apply Hin; exact Hi).
  rewrite nth_error_map. rewrite (nth_error_nth' (seq lo len) 0%nat) by (rewrite seq_length; exact Hi).
  rewrite seq_nth by exact Hi. cbn [option_map].
  apply nth_error_nth'. lia.
Qed.

Lemma rc_ro_bytes : forall m A bs (k len : nat),
  ro_cells segs m A (map C1 bs) -> (k + len <= length bs)%nat ->
  bytes_at segs m (A + Z.of_nat k) (firstn len (skipn k bs)).
Proof.
  intros m A bs k len [_ H] L. rewrite rc_c1_bytes in H.
  rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite firstn_length_le in H by lia.
  rewrite <- (firstn_skipn len (skipn k bs)) in H. apply bytes_at_app in H. exact (proj1 H).
Qed.

Lemma rc_rw_cut_rep : forall m A b n k,
  rw_cells segs m A [CB n (repeat b n)] -> (k <= n)%nat ->
  rw_cells segs m A [CB k (repeat b k)] /\ rw_cells segs m (A + Z.of_nat k) [CB (n - k) (repeat b (n - k))].
Proof.
  intros m A b n k H L. apply rc_rw_cut with (l2 := repeat b (n - k)); [|apply repeat_length].
  replace (repeat b k ++ repeat b (n - k)) with (repeat b n); [exact H|].
  rewrite <- repeat_app. f_equal. lia.
Qed.

End WithSegs.

Lemma rc_memcmp_ff : forall b0 b1 b2 b3 b4 b5 : byte,
  exists v, memcmp_model [b0; b1; b2; b3; b4; b5] (repeat (Z_to_bv 8 255) 6) 6 = Some v /\
    -256 < v < 256 /\
    (v =? 0) = forallb (fun b => bv_unsigned b =? 255) [b0; b1; b2; b3; b4; b5].
Proof.
  intros. cbn [repeat memcmp_model forallb].
  change (bv_unsigned (Z_to_bv 8 255)) with 255.
  pose proof (byte_range b0). pose proof (byte_range b1). pose proof (byte_range b2).
  pose proof (byte_range b3). pose proof (byte_range b4). pose proof (byte_range b5).
  destruct (Z.eqb_spec (bv_unsigned b0) 255); [|eexists; split; [reflexivity|split; [lia|]]; cbn [andb];
    apply Z.eqb_neq; lia].
  destruct (Z.eqb_spec (bv_unsigned b1) 255); [|eexists; split; [reflexivity|split; [lia|]]; cbn [andb];
    apply Z.eqb_neq; lia].
  destruct (Z.eqb_spec (bv_unsigned b2) 255); [|eexists; split; [reflexivity|split; [lia|]]; cbn [andb];
    apply Z.eqb_neq; lia].
  destruct (Z.eqb_spec (bv_unsigned b3) 255); [|eexists; split; [reflexivity|split; [lia|]]; cbn [andb];
    apply Z.eqb_neq; lia].
  destruct (Z.eqb_spec (bv_unsigned b4) 255); [|eexists; split; [reflexivity|split; [lia|]]; cbn [andb];
    apply Z.eqb_neq; lia].
  destruct (Z.eqb_spec (bv_unsigned b5) 255); [|eexists; split; [reflexivity|split; [lia|]]; cbn [andb];
    apply Z.eqb_neq; lia].
  eexists; split; [reflexivity|]. split; [lia|]. reflexivity.
Qed.

Lemma rc_seqz : forall v, -256 < v < 256 ->
  Z.b2z (bv_unsigned (Z_to_bv 64 v) <? bv_wrap 64 1) = if v =? 0 then 1 else 0.
Proof.
  intros v Hv. rewrite unsigned_lit_wrap. change (bv_wrap 64 1) with 1.
  destruct (Z.eqb_spec v 0) as [->|E]; [reflexivity|].
  destruct (Z.ltb_spec v 0).
  - replace (v mod 2^64) with (v + 2^64) by (rewrite <- (Z.mod_add v 1 (2^64)) by lia; rewrite Z.mod_small; lia).
    replace (v + 2^64 <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
  - rewrite Z.mod_small by lia. replace (v <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Ltac rc_stk_keep segs m m' MUc WMc :=
  try match goal with
  | ST : stk segs m ?lo ?hi |- _ =>
      let ST' := fresh "ST" in
      first [ assert (ST' : stk segs m' lo hi)
                by (eapply stk_transport_disjoint; [exact ST | exact MUc | exact WMc | cbn [disjoint_from]; slia])
            | match goal with
              | RW : rw_cells segs m' ?a [CB ?len ?bs] |- _ =>
                  assert (ST' : stk segs m' lo hi)
                    by (eapply rc_stk_call; [exact ST | exact MUc | exact WMc | exact RW | lia])
              end ];
      clear ST
  end.

Ltac rc_post_call segs m :=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO;
  destruct_exs PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  destruct PO as [E [MUc [WMc PO]]];
  first [ destruct PO as [MIc PO] | rename PO into MIc ];
  subst ms';
  lazymatch type of MUc with
  | munch _ m ?m' =>
      try destruct_ands PO;
      rc_stk_keep segs m m' MUc WMc;
      transport_after_call segs m m' MUc WMc;
      clear MUc WMc;
      try match goal with H : mem_inv segs m |- _ => clear H end;
      try clear m
  end;
  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end).

Tactic Notation "rc_call" uconstr(SPEC) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ eapply SPEC | rc_post_call segs m ]
  end.

Lemma rc_zextb : forall b : byte, Z_to_bv 64 (Z.land (bv_unsigned (zxb b)) 255) = zxb b.
Proof.
  intros b. pose proof (byte_range b). unfold zxb. rewrite unsigned_lit by lia.
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia. rewrite Z.mod_small by (cbn; lia). reflexivity.
Qed.

Lemma rc_lor0 : forall x y : byte,
  bv_eqb (Z_to_bv 64 (Z.lor (bv_unsigned (zxb x)) (bv_unsigned (zxb y)))) (Z_to_bv 64 0) =
  (bv_unsigned x =? 0) && (bv_unsigned y =? 0).
Proof.
  intros x y. pose proof (byte_range x). pose proof (byte_range y). unfold zxb.
  rewrite !(unsigned_lit (bv_unsigned _)) by lia.
  assert (R : 0 <= Z.lor (bv_unsigned x) (bv_unsigned y) < 2^8) by (apply lor_lt_pow2; cbn; lia).
  rewrite rc_eqb64 by (cbn in R; lia).
  destruct (Z.eqb_spec (Z.lor (bv_unsigned x) (bv_unsigned y)) 0) as [E|E].
  - apply Z.lor_eq_0_iff in E. destruct E as [-> ->]. reflexivity.
  - symmetry. apply andb_false_iff. destruct (Z.eqb_spec (bv_unsigned x) 0) as [Ex|Ex]; [|left; reflexivity].
    right. apply Z.eqb_neq. intros Ey. apply E. rewrite Ex, Ey. reflexivity.
Qed.

Lemma rc_pack2 : forall lo hi : byte,
  Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb hi)) 8))) (bv_unsigned (zxb lo)) =
  bv_unsigned hi * 256 + bv_unsigned lo.
Proof.
  intros lo hi. pose proof (byte_range lo) as Rl. pose proof (byte_range hi) as Rh. unfold zxb.
  rewrite (unsigned_lit (bv_unsigned hi)) by lia. rewrite (unsigned_lit (bv_unsigned lo)) by lia.
  rewrite (unsigned_lit (Z.shiftl (bv_unsigned hi) 8)) by (rewrite Z.shiftl_mul_pow2 by lia; change (2^8) with 256; lia).
  rewrite Z.lor_comm, lor_shiftl8_add by lia. lia.
Qed.

Lemma rc_le2_pack : forall lo hi : byte,
  le2 (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb hi)) 8))) (bv_unsigned (zxb lo)))) =
  [lo; hi].
Proof. intros lo hi. rewrite rc_pack2. apply rc_le2_pair. Qed.

Lemma rc_pack_eqb : forall lo hi : byte, forall c, 0 <= c < 2^64 ->
  bv_eqb (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb hi)) 8))) (bv_unsigned (zxb lo))))
         (Z_to_bv 64 c) = (bv_unsigned hi * 256 + bv_unsigned lo =? c).
Proof.
  intros lo hi c Hc. rewrite rc_pack2. pose proof (byte_range lo). pose proof (byte_range hi).
  apply rc_eqb64; lia.
Qed.

Lemma rc_le4_seqz : forall v, -256 < v < 256 ->
  le4 (v_sltiu (Z_to_bv 64 v) 1) = [if v =? 0 then Z_to_bv 8 1 else cp_z; cp_z; cp_z; cp_z].
Proof.
  intros v Hv. rewrite v_sltiu_b2z, rc_seqz by exact Hv.
  rewrite rc_le4_small by (destruct (v =? 0); lia). destruct (v =? 0); reflexivity.
Qed.

Lemma cp_v_range : forall fr i, 0 <= cp_v fr i < 256.
Proof. intros fr i. apply byte_range. Qed.

Ltac zlitr := split; vm_compute; first [reflexivity | discriminate].

Ltac zfact :=
  first [ assumption
        | match goal with E : ?x = ?d |- ?x <> ?c => rewrite E; discriminate end
        | match goal with E : ?x = ?d |- ?x = ?c => rewrite E; reflexivity end ].

Ltac zdec x c :=
  first [ let H := fresh in assert (H : x = c) by zfact; rewrite (proj2 (Z.eqb_eq x c) H); clear H
        | let H := fresh in assert (H : x <> c) by zfact; rewrite (proj2 (Z.eqb_neq x c) H); clear H
        | let H := fresh "B" in destruct (Z.eqb_spec x c) as [H|H] ];
  cbn [negb]; cbv iota.

Ltac zeval :=
  repeat match goal with
  | H : ?L = ?b |- context [?L] =>
      lazymatch L with andb _ _ => idtac end; lazymatch b with true => idtac | false => idtac end; rewrite H
  end;
  repeat match goal with
  | H : ?x = ?c |- context [?x =? _] => is_Zlit c; rewrite H
  | H : ?x <> ?c |- context [?x =? ?c] => rewrite (proj2 (Z.eqb_neq x c) H)
  end;
  cbn [andb negb orb Z.eqb Pos.eqb].

Lemma rc_rw_cut_at : forall segs m A b n k A',
  rw_cells segs m A [CB n (repeat b n)] -> (k <= n)%nat -> A' = A + Z.of_nat k ->
  rw_cells segs m A [CB k (repeat b k)] /\ rw_cells segs m A' [CB (n - k) (repeat b (n - k))].
Proof. intros segs m A b n k A' H L ->. apply rc_rw_cut_rep; assumption. Qed.

Ltac rc_ojoin HO X1 :=
  lazymatch type of HO with
  | (?o = 0 /\ ?o' = _) \/ _ =>
    eapply (evt_cut _ (fun ms' => ms' = _));
    [ let Hz := fresh "Hz" in let Hq := fresh "Hq" in
      destruct HO as [[Hz Hq]|[Hz Hq]];
      [ rewrite (rc_beq0_true o Hz); cbv iota; replace X1 with o' by lia; apply evt_done; reflexivity
      | rewrite (rc_beq0_false o Hz ltac:(lia)); cbv iota; step; apply evt_done; rewrite Hq; reflexivity ]
    | let ms := fresh "ms" in let E := fresh "E" in intros ms E; subst ms ]
  end.
