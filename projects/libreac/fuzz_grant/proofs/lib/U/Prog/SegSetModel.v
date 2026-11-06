From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Arr ZBridge Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import HeadampModel SlotNeeds_c GrantSlotPlan SlotBridge.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require reac_headamp_tx_set_c.
Import ListNotations.
Open Scope Z_scope.

Lemma nat_win1 : forall a b, b <> a -> ((a <=? b)%nat && (b <? a + 1)%nat)%bool = false.
Proof.
  intros a b H. destruct (Nat.leb_spec a b); destruct (Nat.ltb_spec b (a + 1)); cbn [andb]; try reflexivity. lia.
Qed.

Ltac ncond :=
  repeat match goal with
  | |- context [((?a <=? ?b)%nat && (?b <? ?a + 1)%nat)%bool] => rewrite (nat_win1 a b) by lia
  | |- context [Nat.leb ?a ?b] =>
      first [ rewrite (proj2 (Nat.leb_le a b)) by lia | rewrite (proj2 (Nat.leb_gt a b)) by lia ]
  | |- context [Nat.ltb ?a ?b] =>
      first [ rewrite (proj2 (Nat.ltb_lt a b)) by lia | rewrite (proj2 (Nat.ltb_ge a b)) by lia ]
  | |- context [Z.eqb ?a ?b] =>
      first [ rewrite (proj2 (Z.eqb_eq a b)) by lia | rewrite (proj2 (Z.eqb_neq a b)) by lia ]
  | |- context [Z.leb ?a ?b] =>
      first [ rewrite (proj2 (Z.leb_le a b)) by lia | rewrite (proj2 (Z.leb_gt a b)) by lia ]
  | |- context [Z.ltb ?a ?b] =>
      first [ rewrite (proj2 (Z.ltb_lt a b)) by lia | rewrite (proj2 (Z.ltb_ge a b)) by lia ]
  end; cbn [andb orb negb].

Lemma nth_skipn_gen : forall {A} (l : list A) m n d, nth n (skipn m l) d = nth (m + n) l d.
Proof.
  intros A l. induction l as [|x l IH]; intros [|m] n d; cbn; try reflexivity;
    try (destruct n; reflexivity); apply IH.
Qed.

Lemma nth_firstn_lt : forall {A} (l : list A) k i d, (i < k)%nat -> nth i (firstn k l) d = nth i l d.
Proof.
  intros A l. induction l as [|x l IH]; intros [|k] [|i] d H; cbn; try reflexivity; try lia.
  apply IH. lia.
Qed.

Lemma nth_upd_bytes : forall (cs bs : list byte) k i d, (k + length bs <= length cs)%nat ->
  nth i (upd_bytes cs k bs) d =
  if ((k <=? i)%nat && (i <? k + length bs)%nat)%bool then nth (i - k) bs d else nth i cs d.
Proof.
  intros cs bs k i d H. unfold upd_bytes.
  assert (Lf : length (firstn k cs) = k) by (rewrite firstn_length; lia).
  destruct (Nat.leb_spec k i) as [H1|H1]; cbn [andb].
  - rewrite app_nth2 by lia. rewrite Lf.
    destruct (Nat.ltb_spec i (k + length bs)) as [H2|H2].
    + rewrite app_nth1 by lia. reflexivity.
    + rewrite app_nth2 by lia. rewrite nth_skipn_gen. f_equal. lia.
  - rewrite app_nth1 by lia. apply nth_firstn_lt. exact H1.
Qed.

Lemma tb_upd : forall T bs (j : nat) i, (j + length bs <= length T)%nat ->
  tb (upd_bytes T j bs) i =
  if ((j <=? Z.to_nat i)%nat && (Z.to_nat i <? j + length bs)%nat)%bool
  then bv_unsigned (nth (Z.to_nat i - j) bs (Z_to_bv 8 0)) else tb T i.
Proof. intros. unfold tb. rewrite nth_upd_bytes by assumption. destruct (_ && _)%bool; reflexivity. Qed.

Lemma upd_len : forall (T bs : list byte) k n, length T = n -> (k + length bs <= n)%nat ->
  length (upd_bytes T k bs) = n.
Proof. intros. subst n. apply upd_bytes_length. assumption. Qed.

Lemma byte_small : forall v, 0 <= v < 256 -> bv_unsigned (Z_to_bv 8 v) = v.
Proof. intros v Hv. rewrite Z_to_bv_unsigned. apply bv_wrap_small. replace (bv_modulus 8) with 256 by reflexivity. lia. Qed.

Lemma le1_small : forall v, 0 <= v < 256 -> le1 (Z_to_bv 64 v) = [Z_to_bv 8 v].
Proof.
  intros v Hv. replace (Z_to_bv 64 v) with (zxb (Z_to_bv 8 v)); [apply le1_zxb|].
  unfold zxb. rewrite byte_small by exact Hv. reflexivity.
Qed.

Lemma le4_one : le4 (Z_to_bv 64 1) = [Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0].
Proof. vm_compute. reflexivity. Qed.

Ltac zero_index :=
  repeat match goal with
  | |- context [nth (?a - ?b)%nat ?l ?d] =>
      lazymatch a with b => fail | _ => replace (a - b)%nat with 0%nat by lia end
  end.

Lemma tb_set_T : forall T c q v i, length T = 460%nat -> 0 <= c < 48 -> 0 <= q < 3 -> 0 <= v < 256 -> 0 <= i ->
  tb (reac_headamp_tx_set_c.set_T T c q v) i =
  if (432 <=? i) && (i <? 436) then (if i =? 432 then 1 else 0)
  else if i =? 288 + (3 * c + q) then 1
  else if i =? 144 + (3 * c + q) then 1
  else if i =? 3 * c + q then v
  else tb T i.
Proof.
  intros T c q v i HL Hc Hq Hv Hi. unfold reac_headamp_tx_set_c.set_T.
  rewrite (le1_small v) by lia. rewrite (le1_small 1) by lia. rewrite le4_one.
  assert (L0 : length (upd_bytes T (Z.to_nat (3 * c + q)) [Z_to_bv 8 v]) = 460%nat)
    by (apply upd_len; [exact HL | cbn [length]; lia]).
  assert (L1 : length (upd_bytes (upd_bytes T (Z.to_nat (3 * c + q)) [Z_to_bv 8 v])
                 (Z.to_nat (144 + 3 * c + q)) [Z_to_bv 8 1]) = 460%nat)
    by (apply upd_len; [exact L0 | cbn [length]; lia]).
  assert (L2 : length (upd_bytes (upd_bytes (upd_bytes T (Z.to_nat (3 * c + q)) [Z_to_bv 8 v])
                 (Z.to_nat (144 + 3 * c + q)) [Z_to_bv 8 1])
                 (Z.to_nat (288 + 3 * c + q)) [Z_to_bv 8 1]) = 460%nat)
    by (apply upd_len; [exact L1 | cbn [length]; lia]).
  repeat (rewrite tb_upd by (rewrite ?L0, ?L1, ?L2, ?HL; cbn [length]; lia)).
  cbn [length].
  destruct (Z.leb_spec 432 i); destruct (Z.ltb_spec i 436); cbn [andb]; [ | | | lia ].
  - assert (i = 432 \/ i = 433 \/ i = 434 \/ i = 435) as [E|[E|[E|E]]] by lia; subst i; vm_compute; reflexivity.
  - destruct (Z.eqb_spec i (288 + (3 * c + q)));
      [ | destruct (Z.eqb_spec i (144 + (3 * c + q))); [ | destruct (Z.eqb_spec i (3 * c + q)) ] ];
      ncond; first [ lia | reflexivity | (zero_index; cbn [nth]; apply byte_small; lia) ].
  - destruct (Z.eqb_spec i (288 + (3 * c + q)));
      [ | destruct (Z.eqb_spec i (144 + (3 * c + q))); [ | destruct (Z.eqb_spec i (3 * c + q)) ] ];
      ncond; first [ lia | reflexivity | (zero_index; cbn [nth]; apply byte_small; lia) ].
Qed.

Lemma len_set_T : forall T c q v, length T = 460%nat -> 0 <= c < 48 -> 0 <= q < 3 ->
  length (reac_headamp_tx_set_c.set_T T c q v) = 460%nat.
Proof.
  intros T c q v HL Hc Hq. unfold reac_headamp_tx_set_c.set_T.
  repeat (apply upd_len; [ | rewrite ?length_le1, ?length_le4; lia ]). exact HL.
Qed.

Lemma tb_ws_put : forall ws c q b i, length ws = 144%nat -> 0 <= c < 48 -> 0 <= q < 3 -> 0 <= b < 256 -> 0 <= i ->
  tb (ws_put ws c q b) i = if i =? 3 * c + q then b else tb ws i.
Proof.
  intros ws c q b i HL Hc Hq Hb Hi. unfold ws_put.
  rewrite tb_upd by (cbn [length]; lia). cbn [length].
  destruct (Z.eqb_spec i (3 * c + q)); ncond; [zero_index; cbn [nth]; apply byte_small; lia | reflexivity].
Qed.

Lemma len_ws_put : forall ws c q b, length ws = 144%nat -> 0 <= c < 48 -> 0 <= q < 3 ->
  length (ws_put ws c q b) = 144%nat.
Proof. intros. unfold ws_put. apply upd_len; [assumption | cbn [length]; lia]. Qed.

Lemma tb_repeat0 : forall n i, tb (repeat (Z_to_bv 8 0) n) i = 0.
Proof.
  intros n i. unfold tb. generalize (Z.to_nat i) as k. induction n as [|n IH]; intros [|k]; cbn; try reflexivity.
  apply IH.
Qed.

Lemma u32at_T0 : forall k, u32at T0 k = 0.
Proof. intros. unfold u32at, T0. rewrite !tb_repeat0. reflexivity. Qed.

Lemma s32at_T0 : forall k, s32at T0 k = 0.
Proof. intros. unfold s32at. rewrite u32at_T0. reflexivity. Qed.

Lemma I1_T0 : I1 T0.
Proof.
  unfold I1. rewrite !s32at_T0, !u32at_T0. unfold T0.
  split; [intros i _; rewrite !tb_repeat0; lia|].
  split; [intros c q _ _ H; rewrite tb_repeat0 in H; lia|].
  split; [intros i _ H; rewrite tb_repeat0 in H; lia|].
  rewrite !tb_repeat0.
  split; [split; [lia | intros (i & _ & H); rewrite tb_repeat0 in H; lia]|].
  split; [left; reflexivity|]. split; [left; reflexivity|].
  split; lia.
Qed.

Lemma Hrel_T0 : Hrel T0 Z144 Z144.
Proof. intros c q Hc Hq. unfold T0, Z144. rewrite !tb_repeat0. split; reflexivity. Qed.

Lemma legal_bound : forall q v, legal q v -> 0 <= q < 3 /\ 0 <= v < 256.
Proof. unfold legal. intros; lia. Qed.

Lemma legalb_legal : forall q v, 0 <= q -> 0 <= v -> legalb q v = true -> legal q v.
Proof.
  intros q v Hq Hv H. unfold legalb in H. unfold legal.
  apply orb_true_iff in H. destruct H as [H|H]; apply andb_true_iff in H; destruct H as [H1 H2].
  - apply Z.ltb_lt in H1. apply Z.leb_le in H2. lia.
  - apply Z.eqb_eq in H1. apply Z.leb_le in H2. lia.
Qed.

Lemma I1_set_T : forall T c q v, length T = 460%nat -> 0 <= c < 48 -> legal q v -> I1 T ->
  I1 (reac_headamp_tx_set_c.set_T T c q v).
Proof.
  intros T c q v HL Hc Hlv (I1a & I1b & I1c & I1d & I1e & I1f & I1g & I1h).
  destruct (legal_bound q v Hlv) as [Hq Hv].
  unfold I1, s32at, u32at. rewrite !tb_set_T by lia.
  unfold s32at, u32at in I1d, I1g, I1h.
  ncond.
  split.
  { intros i Hi. rewrite !tb_set_T by lia.
    destruct (Z.eqb_spec i (3 * c + q)); ncond; [lia | exact (I1a i Hi)]. }
  split.
  { intros c' q' Hc' Hq' H1. rewrite !tb_set_T in H1 |- * by lia.
    destruct (Z.eqb_spec (3 * c' + q') (3 * c + q)) as [E|E]; revert H1; ncond; intros H1.
    - assert (c' = c /\ q' = q) as [-> ->] by lia. exact Hlv.
    - exact (I1b c' q' Hc' Hq' H1). }
  split.
  { intros i Hi H1. rewrite !tb_set_T in H1 |- * by lia.
    destruct (Z.eqb_spec i (3 * c + q)) as [E|E]; revert H1; ncond; intros H1.
    - reflexivity.
    - exact (I1c i Hi H1). }
  split.
  { split; [lia|]. intros _. lia. }
  exact (conj I1e (conj I1f (conj I1g I1h))).
Qed.

Lemma Hrel_set : forall T ws st c q v, length T = 460%nat -> length ws = 144%nat -> length st = 144%nat ->
  0 <= c < 48 -> 0 <= q < 3 -> 0 <= v < 256 -> Hrel T ws st ->
  Hrel (reac_headamp_tx_set_c.set_T T c q v) (ws_put ws c q 1) (ws_put st c q v).
Proof.
  intros T ws st c q v HL Hw Hs Hc Hq Hv H c' q' Hc' Hq'.
  rewrite !tb_ws_put by lia. rewrite !tb_set_T by lia. ncond.
  destruct (Z.eqb_spec (3 * c' + q') (3 * c + q)) as [E|E].
  - ncond. split; reflexivity.
  - ncond. exact (H c' q' Hc' Hq').
Qed.

Lemma set_step_cell : forall T ws st c q v,
  set_step (T, ws, st) (c, q, v) =
  if (c <? 48) && legalb q v
  then (reac_headamp_tx_set_c.set_T T c q v, ws_put ws c q 1, ws_put st c q v) else (T, ws, st).
Proof. reflexivity. Qed.

Definition cell_rd (pl : list byte) (pos : nat) : (Z * Z * Z) * nat :=
  let '(c, p1) := rd8 pl pos in let '(q, p2) := rd8 pl p1 in let '(v, p3) := rd8 pl p2 in ((c, q, v), p3).

Lemma cells_S : forall pl pos k, cells pl pos (S k) =
  let '(x, p3) := cell_rd pl pos in let '(rest, pe) := cells pl p3 k in (x :: rest, pe).
Proof.
  intros pl pos k. unfold cell_rd. cbn [cells].
  destruct (rd8 pl pos) as [c p1]. cbv beta iota zeta.
  destruct (rd8 pl p1) as [q p2]. cbv beta iota zeta.
  destruct (rd8 pl p2) as [v p3]. cbv beta iota zeta.
  reflexivity.
Qed.

Lemma cells_snoc : forall pl k pos, cells pl pos (S k) =
  (fst (cells pl pos k) ++ [fst (cell_rd pl (snd (cells pl pos k)))], snd (cell_rd pl (snd (cells pl pos k)))).
Proof.
  intros pl k. induction k as [|k IH]; intros pos.
  - rewrite cells_S. cbn [cells fst snd app]. destruct (cell_rd pl pos) as [x p3]. reflexivity.
  - rewrite (cells_S pl pos (S k)), (cells_S pl pos k).
    destruct (cell_rd pl pos) as [x p3]. cbv beta iota zeta. rewrite IH.
    destruct (cells pl p3 k) as [rest pe]. reflexivity.
Qed.

Lemma tables_at_S : forall pl i,
  tables_at pl (S i) = set_step (tables_at pl i) (fst (cell_rd pl (snd (cells_upto pl i)))).
Proof.
  intros pl i. unfold tables_at, after_sets, cells_upto. rewrite cells_snoc. cbn [fst].
  rewrite fold_left_app. reflexivity.
Qed.

Lemma pos_S : forall pl i, snd (cells_upto pl (S i)) = snd (cell_rd pl (snd (cells_upto pl i))).
Proof. intros pl i. unfold cells_upto. rewrite cells_snoc. reflexivity. Qed.

Lemma tables_at_0 : forall pl, tables_at pl 0 = (T0, Z144, Z144).
Proof. reflexivity. Qed.

Lemma rd8_lt : forall pl pos, (pos < length pl)%nat -> rd8 pl pos = (pbz pl pos, S pos).
Proof. intros pl pos H. unfold rd8. rewrite (proj2 (Nat.ltb_lt _ _) H). reflexivity. Qed.

Lemma rd8_ge : forall pl pos, (length pl <= pos)%nat -> rd8 pl pos = (0, pos).
Proof. intros pl pos H. unfold rd8. rewrite (proj2 (Nat.ltb_ge _ _) H). reflexivity. Qed.

Lemma rd8_le : forall pl pos, (pos <= length pl)%nat -> (snd (rd8 pl pos) <= length pl)%nat.
Proof. intros pl pos H. unfold rd8. destruct (Nat.ltb_spec pos (length pl)); cbn [snd]; lia. Qed.

Lemma cell_rd_3 : forall pl pos, (pos + 3 <= length pl)%nat ->
  cell_rd pl pos = ((pbz pl pos, pbz pl (S pos), pbz pl (S (S pos))), S (S (S pos))).
Proof.
  intros pl pos H. unfold cell_rd.
  rewrite rd8_lt by lia. cbv beta iota zeta. rewrite rd8_lt by lia. cbv beta iota zeta.
  rewrite rd8_lt by lia. reflexivity.
Qed.

Lemma cell_rd_2 : forall pl pos, length pl = (pos + 2)%nat ->
  cell_rd pl pos = ((pbz pl pos, pbz pl (S pos), 0), S (S pos)).
Proof.
  intros pl pos H. unfold cell_rd.
  rewrite rd8_lt by lia. cbv beta iota zeta. rewrite rd8_lt by lia. cbv beta iota zeta.
  rewrite rd8_ge by lia. reflexivity.
Qed.

Lemma cell_rd_1 : forall pl pos, length pl = (pos + 1)%nat ->
  cell_rd pl pos = ((pbz pl pos, 0, 0), S pos).
Proof.
  intros pl pos H. unfold cell_rd.
  rewrite rd8_lt by lia. cbv beta iota zeta. rewrite rd8_ge by lia. cbv beta iota zeta.
  rewrite rd8_ge by lia. reflexivity.
Qed.

Lemma cell_rd_0 : forall pl pos, (length pl <= pos)%nat -> cell_rd pl pos = ((0, 0, 0), pos).
Proof.
  intros pl pos H. unfold cell_rd.
  rewrite rd8_ge by lia. cbv beta iota zeta. rewrite rd8_ge by lia. cbv beta iota zeta.
  rewrite rd8_ge by lia. reflexivity.
Qed.

Lemma cell_rd_le : forall pl pos, (pos <= length pl)%nat -> (snd (cell_rd pl pos) <= length pl)%nat.
Proof.
  intros pl pos H.
  destruct (Nat.le_gt_cases (pos + 3) (length pl)) as [H3|H3].
  - rewrite cell_rd_3 by lia. cbn [snd]. lia.
  - assert (length pl = pos \/ length pl = (pos + 1)%nat \/ length pl = (pos + 2)%nat) as [E|[E|E]] by lia.
    + rewrite cell_rd_0 by lia. cbn [snd]. lia.
    + rewrite cell_rd_1 by lia. cbn [snd]. lia.
    + rewrite cell_rd_2 by lia. cbn [snd]. lia.
Qed.

Lemma cells_le : forall pl k pos, (pos <= length pl)%nat -> (snd (cells pl pos k) <= length pl)%nat.
Proof.
  intros pl k. induction k as [|k IH]; intros pos H; [cbn; lia|].
  rewrite cells_snoc. cbn [snd]. apply cell_rd_le. apply IH. exact H.
Qed.

Lemma header_le : forall pl, (h_pos (header pl) <= length pl)%nat.
Proof.
  intros pl. unfold header, rd16.
  pose proof (rd8_le pl 0 ltac:(lia)) as B1. destruct (rd8 pl 0) as [a p1]. cbn [snd] in B1. cbv beta iota zeta.
  pose proof (rd8_le pl p1 B1) as B2. destruct (rd8 pl p1) as [b p2]. cbn [snd] in B2. cbv beta iota zeta.
  pose proof (rd8_le pl p2 B2) as B3. destruct (rd8 pl p2) as [c p3]. cbn [snd] in B3. cbv beta iota zeta.
  pose proof (rd8_le pl p3 B3) as B4. destruct (rd8 pl p3) as [d p4]. cbn [snd] in B4. cbv beta iota zeta.
  exact B4.
Qed.

Lemma pos_cells_le : forall pl, (pos_cells pl <= length pl)%nat.
Proof. intros pl. unfold pos_cells. apply rd8_le. apply header_le. Qed.

Lemma cells_upto_le : forall pl i, (snd (cells_upto pl i) <= length pl)%nat.
Proof. intros pl i. unfold cells_upto. apply cells_le. apply pos_cells_le. Qed.

Lemma canon_rg : forall ms, ms_svc_pending ms = None ->
  canonical_register_state ms =
  MS (mkR (rg ms 1) (rg ms 2) (rg ms 3) (rg ms 4) (rg ms 5) (rg ms 6) (rg ms 7) (rg ms 8) (rg ms 9) (rg ms 10)
          (rg ms 11) (rg ms 12) (rg ms 13) (rg ms 14) (rg ms 15) (rg ms 16) (rg ms 17) (rg ms 18) (rg ms 19)
          (rg ms 20) (rg ms 21) (rg ms 22) (rg ms 23) (rg ms 24) (rg ms 25) (rg ms 26) (rg ms 27) (rg ms 28)
          (rg ms 29) (rg ms 30) (rg ms 31))
     (ms_fregs ms) (ms_pc_val ms) (ms_fcsr ms) (ms_resv ms) (ms_mem ms) (ms_rom ms).
Proof. intros ms H. rewrite canon_MS by exact H. unfold mkR_of, rg, PropExec.getr. reflexivity. Qed.

Lemma stk_cell : forall m lo hi a (n : nat), stk rsegs m lo hi -> lo <= a -> a + Z.of_nat n <= hi ->
  exists junk, rw_cells rsegs m a [CB n junk].
Proof.
  intros m lo hi a n (H1 & H2 & H) Ha Hn.
  assert (S1 : stk rsegs m lo (a + Z.of_nat n)) by (split; [lia | split; [lia | intros; apply H; lia]]).
  destruct (stk_carve rsegs m lo (a + Z.of_nat n) n S1 ltac:(lia)) as [_ [junk FR]].
  exists junk. replace a with (a + Z.of_nat n - Z.of_nat n) by lia. exact FR.
Qed.

Lemma mem_inv_munch : forall m m' t n, mem_inv rsegs m -> munch [(t, t + n)] m m' -> wr_at rsegs m t n ->
  mem_inv rsegs m'.
Proof.
  intros m m' t n HI MU (Ht & Hn & HW) a b Hb.
  destruct (Z_lt_le_dec (bv_unsigned a) t) as [L|L];
    [| destruct (Z_lt_le_dec (bv_unsigned a) (t + n)) as [L2|L2]].
  - rewrite MU in Hb by (cbn; split; [lia | exact I]). exact (HI a b Hb).
  - assert (W : wview rsegs m (wa (t + (bv_unsigned a - t))) <> None) by (apply HW; lia).
    assert (Ea : wa (t + (bv_unsigned a - t)) = a).
    { unfold wa. replace (t + (bv_unsigned a - t)) with (bv_unsigned a) by lia. apply Z_to_bv_bv_unsigned. }
    rewrite Ea in W.
    destruct (m a) as [b'|] eqn:E.
    + exact (HI a b' E).
    + exact (wview_not_ro rsegs m a W E).
  - rewrite MU in Hb by (cbn; split; [lia | exact I]). exact (HI a b Hb).
Qed.

Lemma rw_cells_CB : forall m A bs n, length bs = n -> bytes_at rsegs m A bs -> wr_at rsegs m A (Z.of_nat n) ->
  rw_cells rsegs m A [CB n bs].
Proof. intros m A bs n <- HB HW. apply rw_cells_of_u8arr. split; assumption. Qed.

Lemma CB_bytes : forall m A bs n, rw_cells rsegs m A [CB n bs] ->
  bytes_at rsegs m A bs /\ wr_at rsegs m A (Z.of_nat n) /\ length bs = n.
Proof.
  intros m A bs n [[Hwf Hb] Hw]. cbn [cells_bytes cbytes cells_wf cell_wf cells_size csize] in Hwf, Hb, Hw.
  destruct Hwf as [Hn _]. rewrite app_nil_r in Hb. rewrite Nat.add_0_r in Hw.
  split; [exact Hb | split; [exact Hw | exact Hn]].
Qed.

Lemma rd8_range : forall pl pos, 0 <= fst (rd8 pl pos) < 256.
Proof.
  intros pl pos. unfold rd8. destruct (Nat.ltb _ _); cbn [fst]; [|lia].
  unfold pbz. pose proof (bv_unsigned_in_range 8 (nth pos pl (Z_to_bv 8 0))) as R.
  replace (bv_modulus 8) with 256 in R by reflexivity. lia.
Qed.

Definition cell_ok (x : Z * Z * Z) : Prop :=
  let '(c, q, v) := x in 0 <= c < 256 /\ 0 <= q < 256 /\ 0 <= v < 256.

Lemma cell_rd_ok : forall pl pos, cell_ok (fst (cell_rd pl pos)).
Proof.
  intros pl pos. unfold cell_rd.
  pose proof (rd8_range pl pos) as R1. destruct (rd8 pl pos) as [c p1]. cbv beta iota zeta.
  pose proof (rd8_range pl p1) as R2. destruct (rd8 pl p1) as [q p2]. cbv beta iota zeta.
  pose proof (rd8_range pl p2) as R3. destruct (rd8 pl p2) as [v p3]. cbv beta iota zeta.
  cbn [fst] in *. unfold cell_ok. lia.
Qed.

Lemma cells_ok : forall pl k pos, Forall cell_ok (fst (cells pl pos k)).
Proof.
  intros pl k. induction k as [|k IH]; intros pos; [constructor|].
  rewrite cells_snoc. cbn [fst]. apply Forall_app. split; [apply IH|].
  constructor; [apply cell_rd_ok | constructor].
Qed.

Definition tinv (s : tstate) : Prop :=
  let '(T, ws, st) := s in
  length T = 460%nat /\ length ws = 144%nat /\ length st = 144%nat /\ I1 T /\ Hrel T ws st.

Lemma tinv_step : forall s x, cell_ok x -> tinv s -> tinv (set_step s x).
Proof.
  intros [[T ws] st] [[c q] v] (Hc & Hq & Hv) (HL & Hw & Hs & HI & HH).
  rewrite set_step_cell. destruct ((c <? 48) && legalb q v) eqn:E;
    [| exact (conj HL (conj Hw (conj Hs (conj HI HH))))].
  apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.ltb_lt in E1.
  pose proof (legalb_legal q v ltac:(lia) ltac:(lia) E2) as Hl. destruct (legal_bound q v Hl) as [Hq3 _].
  split; [apply len_set_T; lia|]. split; [apply len_ws_put; lia|]. split; [apply len_ws_put; lia|].
  split; [apply I1_set_T; [exact HL | lia | exact Hl | exact HI]|].
  apply Hrel_set; try lia; exact HH.
Qed.

Lemma tinv_fold : forall cs s, Forall cell_ok cs -> tinv s -> tinv (fold_left set_step cs s).
Proof.
  induction cs as [|x cs IH]; intros s Hok H; [exact H|].
  inversion Hok as [|? ? Hx Hcs]; subst. cbn [fold_left]. apply IH; [exact Hcs | apply tinv_step; assumption].
Qed.

Lemma tinv_T0 : tinv (T0, Z144, Z144).
Proof.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact I1_T0 | exact Hrel_T0].
Qed.

Lemma tables_at_inv : forall pl i, tinv (tables_at pl i).
Proof. intros. unfold tables_at, after_sets, cells_upto. apply tinv_fold; [apply cells_ok | exact tinv_T0]. Qed.

Lemma tables_end_inv : forall pl,
  length (T_end pl) = 460%nat /\ length (ws_end pl) = 144%nat /\ length (st_end pl) = 144%nat /\
  I1 (T_end pl) /\ Hrel (T_end pl) (ws_end pl) (st_end pl).
Proof.
  intros pl. unfold T_end, ws_end, st_end, tables_end.
  pose proof (tables_at_inv pl (Z.to_nat (nset pl))) as H.
  destruct (tables_at pl (Z.to_nat (nset pl))) as [[T ws] st]. exact H.
Qed.

Lemma cells_size_map_C8 : forall l, cells_size (map C8 l) = (8 * length l)%nat.
Proof. induction l as [|a l IH]; cbn [map cells_size csize length]; [reflexivity|]. rewrite IH. lia. Qed.

Lemma saved_size : forall (sv : list word) ra, length sv = 12%nat ->
  cells_size (map C8 (rev sv ++ [ra])) = 104%nat.
Proof. intros sv ra H. rewrite cells_size_map_C8, length_app, length_rev, H. reflexivity. Qed.

Lemma wnot_lxor : forall a, 0 <= a < 2 ^ 64 -> Z.lxor a 18446744073709551615 = wnot a.
Proof. intros a Ha. unfold wnot. apply zb_lxor_ones. exact Ha. Qed.

Lemma lxor_big : forall a, 0 <= a < 2 ^ 63 -> 2 ^ 63 <= bv_unsigned (Z_to_bv 64 (Z.lxor a 18446744073709551615)).
Proof.
  intros a Ha. rewrite zb_lxor_ones by lia. rewrite inr64_unsigned_lit by (unfold inr64; lia). lia.
Qed.

Ltac brc := first [ if_true | if_false ].

Ltac zsimp_cond :=
  repeat match goal with
  | |- evt _ _ (MS _ _ (if ?C then _ else _) _ _ _ _) =>
      match C with
      | context [Z.ltb ?a ?b] => first [ rewrite (proj2 (Z.ltb_lt a b)) by lia | rewrite (proj2 (Z.ltb_ge a b)) by lia ]
      end
  end; cbn [Z.b2z]; rewrite ?Z.land_0_r, ?Z.land_0_l.

Ltac brx :=
  zsimp_cond;
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?C then _ else _) _ _ _ _) =>
      let HC := fresh "HC" in
      first [ brc | (destruct C eqn:HC; zify_cond HC; try (exfalso; lia)) ]
  end.

Definition hide (P : Prop) : Prop := P.

Ltac rg_eval :=
  unfold rg, PropExec.getr; cbn [ms_regs MS];
  repeat match goal with
  | |- context [bv_eqb ?a ?b] =>
      let v := eval vm_compute in (bv_eqb a b) in
      lazymatch v with
      | true => change (bv_eqb a b) with true
      | false => change (bv_eqb a b) with false
      end
  end; cbv beta iota; simp_regs.

Ltac fin_leaf :=
  first [ assumption | reflexivity | lia
        | (rg_eval; unfold w64; first [ reflexivity | word_eq_tac ]) ].

Ltac fin_at :=
  unfold At_set, At_unset0, At_unset, At_admit, body, common, slots, cslot, nots, cur, table, arrays;
  cbn [ms_pc_val ms_fregs ms_fcsr ms_resv ms_svc_pending ms_rom ms_mem MS];
  repeat match goal with |- _ /\ _ => split end;
  fin_leaf.
