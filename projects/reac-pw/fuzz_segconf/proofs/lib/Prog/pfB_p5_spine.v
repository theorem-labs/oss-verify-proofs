(** reac-pw/fuzz_segconf, piece P5 of reac_segconf_parse_file (the key line, reac_segconf.c:215-293): the facts the
    plain walk (lib/Prog/pf_p5.v) and the UBSan walk (lib/U/Prog/pf_p5.v) share. Build-independent: no image, no
    callee contract, no build's seg_env. It proves no function: lemmas over the spine's lists, and over memory for any
    segment list.

    - r_key's branches once the '=' and the strcasecmp results are known (the p5_rkey lemmas).
    - strchr's index (p5_strchr_some) and the bytes of the line after `*eq = 0` (p5_upd_eq).
    - trim's post read as the trimmed C string at the pointer trim returns (p5_trim_run, from L_trim).
    - unquote (R:78-86, inlined): the three outcomes of r_unquote (the p5_unq lemmas), the bytes the `v[n-1] = 0` store leaves
      (p5_unq_run) and the bytes the two `lbu` read (p5_run_byte).
    - memory: a C string inside a present stack region (p5_cstr_stk), writable bytes there (p5_stk_wr), a callee's
      stack_ok below the frame (p5_stack_ok_sub), transport of a C string or of c's block through a munch. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec pf_pieces_spec.
Import ListNotations.
Open Scope Z_scope.

(** ** Byte-valued lists *)
Definition p5b (l : list Z) : Prop := Forall (fun x => 0 <= x < 256) l.

Lemma p5_u8 : forall x, 0 <= x < 256 -> bv_unsigned (Z_to_bv 8 x) = x.
Proof.
  intros x Hx. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus.
  replace (2 ^ Z.of_N 8) with 256 by reflexivity. lia.
Qed.

Lemma p5_zs_zb : forall l, p5b l -> zs (zb l) = l.
Proof.
  unfold p5b, zs, zb. induction l as [|x l IH]; intros H; [reflexivity|].
  apply Forall_cons_iff in H as [Hx Hl]. cbn [map]. rewrite p5_u8 by exact Hx. rewrite IH by exact Hl.
  reflexivity.
Qed.

Lemma p5b_zs : forall bs, p5b (zs bs).
Proof.
  unfold p5b, zs. intros bs. apply Forall_forall. intros x Hx. apply in_map_iff in Hx as (b & <- & _).
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R.
  replace (2 ^ Z.of_N 8) with 256 in R by reflexivity. lia.
Qed.

Lemma p5b_firstn : forall n l, p5b l -> p5b (firstn n l).
Proof. intros n l H. unfold p5b in *. apply Forall_firstn'. exact H. Qed.

Lemma p5b_skipn : forall n l, p5b l -> p5b (skipn n l).
Proof. intros n l H. unfold p5b in *. apply Forall_skipn'. exact H. Qed.

Lemma p5b_nth : forall l i, p5b l -> 0 <= nth i l 0 < 256.
Proof.
  unfold p5b. induction l as [|x l IH]; intros i H; [destruct i; cbn; lia|].
  apply Forall_cons_iff in H as [Hx Hl]. destruct i as [|i]; cbn [nth]; [exact Hx | apply IH; exact Hl].
Qed.

Lemma p5_nz_zb : forall l, p5b l -> ~ In 0 l -> ~ In ZERO (zb l).
Proof.
  intros l Hb H Hin. apply H. rewrite <- (p5_zs_zb l Hb). unfold zs. apply (in_map bv_unsigned) in Hin.
  replace (bv_unsigned ZERO) with 0 in Hin by reflexivity. exact Hin.
Qed.

Lemma p5_len_zb : forall l, length (zb l) = length l.
Proof. intros l. unfold zb. apply length_map. Qed.

Lemma p5_zb_zs : forall bs, zb (zs bs) = bs.
Proof.
  unfold zb, zs. induction bs as [|b bs IH]; [reflexivity|]. cbn [map]. rewrite IH. f_equal.
  apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma p5_firstn_add : forall (l : list Z) a b, firstn (a + b) l = firstn a l ++ firstn b (skipn a l).
Proof.
  induction l as [|x l IH]; intros a b.
  - rewrite skipn_nil, !firstn_nil. reflexivity.
  - destruct a as [|a]; cbn [firstn skipn Nat.add app]; [reflexivity|]. rewrite IH. reflexivity.
Qed.

(** ** The spine: r_key's branches *)
Lemma p5_rkey_none : forall rc cur nm ln L, strchr L EQ = None ->
  r_key rc cur nm ln L = (refuse rc ln F_neither [AS L], cur, nm).
Proof. intros rc cur nm ln L H. unfold r_key. rewrite H. reflexivity. Qed.

Lemma p5_rkey_outs : forall rc nm ln L ei, strchr L EQ = Some ei ->
  r_key rc None nm ln L = (refuse rc ln F_outside [AS (r_trim (firstn ei L))], None, nm).
Proof. intros rc nm ln L ei H. unfold r_key. rewrite H. reflexivity. Qed.

Lemma p5_rkey_knock : forall rc gi nm ln L ei, strchr L EQ = Some ei ->
  strcasecmp (r_trim (firstn ei L)) S_role <> 0 -> strcasecmp (r_trim (firstn ei L)) S_model <> 0 ->
  strcasecmp (r_trim (firstn ei L)) S_ignore <> 0 -> strcasecmp (r_trim (firstn ei L)) S_knock = 0 ->
  r_key rc (Some gi) nm ln L =
    (refuse rc ln F_knock [AS nm; AS (r_unquote (r_trim (skipn (S ei) L)))], Some gi, nm).
Proof.
  intros rc gi nm ln L ei H H1 H2 H3 H4. unfold r_key. rewrite H. cbv beta iota zeta.
  apply Z.eqb_neq in H1, H2, H3. apply Z.eqb_eq in H4. rewrite H1, H2, H3, H4. reflexivity.
Qed.

Lemma p5_rkey_nokey : forall rc gi nm ln L ei, strchr L EQ = Some ei ->
  strcasecmp (r_trim (firstn ei L)) S_role <> 0 -> strcasecmp (r_trim (firstn ei L)) S_model <> 0 ->
  strcasecmp (r_trim (firstn ei L)) S_ignore <> 0 -> strcasecmp (r_trim (firstn ei L)) S_knock <> 0 ->
  r_key rc (Some gi) nm ln L = (refuse rc ln F_nokey [AS nm; AS (r_trim (firstn ei L))], Some gi, nm).
Proof.
  intros rc gi nm ln L ei H H1 H2 H3 H4. unfold r_key. rewrite H. cbv beta iota zeta.
  apply Z.eqb_neq in H1, H2, H3, H4. rewrite H1, H2, H3, H4. reflexivity.
Qed.

(** refuse keeps the table and the overflow count and adds one refusal to the count. *)
Lemma p5_refuse_rec : forall rc l f a,
  rc_seg (refuse rc l f a) = rc_seg rc /\ rc_refused (refuse rc l f a) = rc_refused rc + 1 /\
  rc_overflow (refuse rc l f a) = rc_overflow rc.
Proof.
  intros rc l f a. unfold refuse. cbv zeta.
  destruct (8 <=? Z.of_nat (length (rc_refusal rc))); [cbn [rc_seg rc_refused rc_overflow]; repeat split|].
  destruct (_ || _); cbn [rc_seg rc_refused rc_overflow]; repeat split.
Qed.

(** ** strchr(line, '=') and `*eq = 0` *)
Lemma p5_strchr_some : forall L c i, strchr L c = Some i -> (i < length L)%nat /\ nth i L 0 = c.
Proof.
  induction L as [|b L IH]; intros c i H; cbn [strchr] in H; [discriminate|].
  destruct (b =? c) eqn:E1.
  - injection H as <-. apply Z.eqb_eq in E1. cbn [length nth]. split; [lia | exact E1].
  - destruct (b =? 0); [discriminate|].
    destruct (strchr L c) as [j|] eqn:E2; cbn [option_map] in H; [|discriminate].
    injection H as <-. destruct (IH c j E2) as [H1 H2]. cbn [length nth]. split; [lia | exact H2].
Qed.

(** The line's bytes and NUL after the store of a NUL at ei: the bytes before ei and the new NUL, then the bytes
    after ei and the line's NUL. *)
Lemma p5_upd_eq : forall (L : list Z) ei, (ei < length L)%nat ->
  upd_bytes (zb L ++ [ZERO]) ei [ZERO] = (zb (firstn ei L) ++ [ZERO]) ++ (zb (skipn (S ei) L) ++ [ZERO]).
Proof.
  intros L ei H. unfold upd_bytes, zb. cbn [length].
  rewrite firstn_app, skipn_app, length_map.
  replace (ei - length L)%nat with 0%nat by lia. replace (ei + 1 - length L)%nat with 0%nat by lia.
  rewrite firstn_O, skipn_O, app_nil_r, firstn_map, skipn_map.
  replace (ei + 1)%nat with (S ei) by lia. rewrite <- !app_assoc. reflexivity.
Qed.

(** The key and value pieces of a line: no NUL, byte values. *)
Lemma p5_trim_props : forall K, L_trim -> p5b K -> ~ In 0 K ->
  p5b (r_trim K) /\ ~ In 0 (r_trim K) /\ (trim_lead K + length (r_trim K) <= length K)%nat.
Proof.
  intros K LT Hb Hn. destruct (LT K Hn) as (H1 & H2 & H3).
  split; [rewrite H2; apply p5b_firstn, p5b_skipn; exact Hb | split; [exact H3 | exact H1]].
Qed.

Lemma p5_slice_props : forall V i j, p5b V -> ~ In 0 V ->
  p5b (slice i j V) /\ ~ In 0 (slice i j V) /\ (length (slice i j V) <= length V - i)%nat.
Proof.
  intros V i j Hb Hn. unfold slice. split; [apply p5b_firstn, p5b_skipn; exact Hb|].
  split; [apply (nulfree_firstn _ _ (nulfree_skipn _ _ Hn))|].
  rewrite length_firstn, length_skipn. lia.
Qed.

(** ** trim's post as the C string at the pointer it returns (L_trim, proved by the kit) *)
Lemma p5_trim_split : forall K, L_trim -> ~ In 0 K ->
  firstn (trim_lead K + length (r_trim K)) K = firstn (trim_lead K) K ++ r_trim K.
Proof.
  intros K LT Hn. destruct (LT K Hn) as (_ & H2 & _). rewrite p5_firstn_add. rewrite <- H2. reflexivity.
Qed.

(** ** unquote (R:78-86) on the trimmed value V *)
Lemma p5_unq_short : forall V, ~ In 0 V -> (length V < 2)%nat -> r_unquote V = V.
Proof.
  intros V H1 H2. unfold r_unquote. rewrite (strlen_id V H1).
  replace ((2 <=? length V)%nat) with false by (symmetry; apply Nat.leb_gt; lia). cbn [andb].
  apply cut_nul_id. exact H1.
Qed.

Lemma p5_unq_strip : forall V q, ~ In 0 V -> (2 <= length V)%nat -> (q = DQ \/ q = SQ) ->
  nth 0 V 0 = q -> nth (length V - 1) V 0 = q -> r_unquote V = slice 1 (length V - 1) V.
Proof.
  intros V q H1 H2 Hq H3 H4. unfold r_unquote. rewrite (strlen_id V H1), H3, H4.
  replace ((2 <=? length V)%nat) with true by (symmetry; apply Nat.leb_le; lia).
  destruct Hq as [-> | ->]; reflexivity.
Qed.

Lemma p5_unq_keep : forall V, ~ In 0 V -> (2 <= length V)%nat ->
  ~ ((nth 0 V 0 = DQ /\ nth (length V - 1) V 0 = DQ) \/ (nth 0 V 0 = SQ /\ nth (length V - 1) V 0 = SQ)) ->
  r_unquote V = V.
Proof.
  intros V H1 H2 H3. unfold r_unquote. rewrite (strlen_id V H1).
  replace ((2 <=? length V)%nat) with true by (symmetry; apply Nat.leb_le; lia). cbn [andb].
  destruct (nth 0 V 0 =? DQ) eqn:E1, (nth (length V - 1) V 0 =? DQ) eqn:E2,
           (nth 0 V 0 =? SQ) eqn:E3, (nth (length V - 1) V 0 =? SQ) eqn:E4; cbn [andb orb];
    try (apply cut_nul_id; exact H1);
    exfalso; apply H3;
    repeat match goal with E : (_ =? _) = true |- _ => apply Z.eqb_eq in E end;
    tauto.
Qed.

(** ** Memory, for any segment list *)
Section Mem.
Variable segs : list Segment.

(** A C string's bytes and NUL (what strcasecmp and trim's callers read), its values bytes, no NUL in it. *)
Lemma p5_cstr_run : forall m a s, cstr_at segs m a s -> bytes_at segs m a (zb s ++ [ZERO]) /\ p5b s /\ ~ In 0 s.
Proof.
  intros m a s (bs & sl & B & Ez & Nz & _). subst s. rewrite p5_zb_zs.
  split; [|split; [apply p5b_zs | exact Nz]].
  replace (bs ++ ZERO :: sl) with ((bs ++ [ZERO]) ++ sl) in B by (rewrite <- app_assoc; reflexivity).
  apply bytes_at_app in B as [B _]. exact B.
Qed.

(** A known run, after a one-byte store at its offset k. *)
Lemma p5_store_run : forall m a bs k b, bytes_at segs m a bs -> (k < length bs)%nat ->
  bytes_at segs (write_to_mem m (wa (a + Z.of_nat k)) [b]) a (upd_bytes bs k [b]).
Proof.
  intros m a bs k b B Hk.
  pose proof (bytes_at_write_inside segs m a bs (Z.of_nat k) [b] B ltac:(lia) ltac:(cbn [length]; lia)) as W.
  rewrite Nat2Z.id in W. exact W.
Qed.

(** The `lbu` of byte i of the C string V (i <= length V - 1). *)
Lemma p5_run_byte : forall (V : list Z) i, (i < length V)%nat ->
  firstn 1 (skipn i (zb V ++ [ZERO])) = [Z_to_bv 8 (nth i V 0)].
Proof.
  unfold zb. induction V as [|x V IH]; intros i H; cbn [length] in H; [lia|].
  destruct i as [|i]; cbn [map app skipn firstn nth]; [reflexivity|]. apply IH. lia.
Qed.

Lemma p5_run_read : forall m a V i, bytes_at segs m a (zb V ++ [ZERO]) -> (i < length V)%nat ->
  ov_read_bytes segs m (wa (a + Z.of_nat i)) 1 = Some [Z_to_bv 8 (nth i V 0)].
Proof.
  intros m a V i B H. rewrite (bytes_at_ov_read segs m a _ i 1 B).
  - rewrite p5_run_byte by exact H. reflexivity.
  - rewrite length_app, p5_len_zb. cbn [length]. lia.
Qed.

(** unquote's store `v[n-1] = 0` (n = length V >= 2), then the C string at v + 1 is slice 1 (n - 1) V. *)
Lemma p5_unq_run : forall m a V, (2 <= length V)%nat -> bytes_at segs m a (zb V ++ [ZERO]) ->
  bytes_at segs (write_to_mem m (wa (a + Z.of_nat (length V - 1))) [ZERO]) (a + 1)
    (zb (slice 1 (length V - 1) V) ++ [ZERO]).
Proof.
  intros m a V H B. destruct V as [|x V']; [cbn [length] in H; lia|]. cbn [length] in H.
  assert (B1 : bytes_at segs m (a + 1) (zb V' ++ [ZERO])).
  { change (zb (x :: V') ++ [ZERO]) with ([Z_to_bv 8 x] ++ (zb V' ++ [ZERO])) in B.
    apply bytes_at_app in B as [_ B]. exact B. }
  assert (LV : (length V' - 1 < length (zb V' ++ [ZERO]))%nat)
    by (rewrite length_app, p5_len_zb; cbn [length]; lia).
  pose proof (p5_store_run m (a + 1) (zb V' ++ [ZERO]) (length V' - 1) ZERO B1 LV) as W.
  rewrite p5_upd_eq in W by lia. apply bytes_at_app in W as [W _].
  replace (a + 1 + Z.of_nat (length V' - 1)) with (a + Z.of_nat (length (x :: V') - 1)) in W
    by (cbn [length]; lia).
  unfold slice. cbn [length skipn]. replace (S (length V') - 1 - 1)%nat with (length V' - 1)%nat by lia.
  exact W.
Qed.

(** trim's post: the bytes at p are the kept prefix and a NUL, so the C string at p + trim_lead K is r_trim K. *)
Lemma p5_trim_run : forall m p K, L_trim -> ~ In 0 K ->
  bytes_at segs m p (zb (firstn (trim_lead K + length (r_trim K)) K) ++ [ZERO]) ->
  bytes_at segs m (p + Z.of_nat (trim_lead K)) (zb (r_trim K) ++ [ZERO]).
Proof.
  intros m p K LT Hn B. destruct (LT K Hn) as (H1 & _ & _).
  rewrite (p5_trim_split K LT Hn) in B. unfold zb in B. rewrite map_app, <- app_assoc in B.
  apply bytes_at_app in B as [_ B]. rewrite length_map, length_firstn in B.
  replace (Nat.min (trim_lead K) (length K)) with (trim_lead K) in B by lia. exact B.
Qed.

(** Present bytes of a stack region. *)
Lemma p5_stk_bytes : forall m lo hi a n, stk segs m lo hi -> lo <= a -> a + Z.of_nat n <= hi ->
  exists bs, length bs = n /\ bytes_at segs m a bs.
Proof.
  intros m lo hi a n ST H1 H2.
  destruct (stk_split segs m lo a hi ST ltac:(lia)) as [_ ST2].
  destruct (stk_split segs m a (a + Z.of_nat n) hi ST2 ltac:(lia)) as [ST3 _].
  destruct (stk_bytes segs m a (a + Z.of_nat n) ST3 ltac:(lia)) as (bs & L & B).
  exists bs. split; [lia | exact B].
Qed.

(** A C string whose bytes and NUL are known, inside a present stack region with 7 bytes to spare after its NUL. *)
Lemma p5_cstr_stk : forall m lo hi a s, bytes_at segs m a (zb s ++ [ZERO]) -> p5b s -> ~ In 0 s ->
  stk segs m lo hi -> lo <= a -> a + Z.of_nat (length s) + 8 <= hi -> cstr_at segs m a s.
Proof.
  intros m lo hi a s B Hb Hn ST H1 H2.
  pose proof (Z.mod_pos_bound (- (a + Z.of_nat (length s) + 1)) 8 ltac:(lia)) as MB.
  destruct (p5_stk_bytes m lo hi (a + Z.of_nat (length s) + 1)
              (Z.to_nat ((- (a + Z.of_nat (length s) + 1)) mod 8)) ST ltac:(lia) ltac:(lia)) as (sl & Lsl & Bsl).
  exists (zb s), sl. split; [|split; [apply p5_zs_zb; exact Hb | split; [exact Hn | lia]]].
  replace (zb s ++ ZERO :: sl) with ((zb s ++ [ZERO]) ++ sl) by (rewrite <- app_assoc; reflexivity).
  apply bytes_at_app. split; [exact B|].
  rewrite length_app, p5_len_zb. cbn [length].
  replace (a + Z.of_nat (length s + 1)) with (a + Z.of_nat (length s) + 1) by lia. exact Bsl.
Qed.

(** Writable bytes of a stack region. *)
Lemma p5_stk_wr : forall m lo hi a n, stk segs m lo hi -> lo <= a -> 0 <= n -> a + n <= hi -> wr_at segs m a n.
Proof.
  intros m lo hi a n (S0 & S1 & S) H1 H2 H3. split; [lia|]. split; [lia|].
  intros i Hi. destruct (S (a + i) ltac:(lia)) as [W _]. exact W.
Qed.

(** A callee's stack below the frame: the caller's stack_ok at hi gives the callee's at sp. *)
Lemma p5_stack_ok_sub : forall m lo hi D sp d, stack_ok segs m lo hi D -> 0 <= d -> lo + d <= sp -> sp <= hi ->
  (hi - sp) mod 16 = 0 -> stack_ok segs m lo sp d.
Proof.
  intros m lo hi D sp d (ST & H1 & H2 & H3) H0 Hd Hsp Hm.
  assert (LS : lo <= sp <= hi) by lia.
  destruct (stk_split segs m lo sp hi ST LS) as [ST1 _].
  split; [exact ST1|]. split; [lia|]. split; [Z.div_mod_to_equations; lia|].
  intros a Ha. apply H3. lia.
Qed.

Lemma p5_disjoint_sub : forall W a n a' n',
  disjoint_from W a n -> a <= a' -> a' + n' <= a + n -> disjoint_from W a' n'.
Proof.
  induction W as [|[l h] W IH]; cbn [disjoint_from]; intros a n a' n' D H1 H2; [exact I|].
  destruct D as [D1 D2]. split; [lia | exact (IH a n a' n' D2 H1 H2)].
Qed.

Lemma p5_rconf_munch : forall W m m' c rc,
  rconf_at segs m c rc -> munch W m m' -> disjoint_from W c SEG_C_SIZE -> rconf_at segs m' c rc.
Proof.
  intros W m m' c rc (bs & B & E) MU D. exists bs. split; [|exact E].
  eapply bytes_at_transport; [exact B | exact MU |]. destruct E as [L _]. rewrite L. exact D.
Qed.

(** A write apart from [a, a + length s + 8) keeps the C string at a. *)
Lemma p5_cstr_munch : forall W m m' a s,
  cstr_at segs m a s -> munch W m m' -> disjoint_from W a (Z.of_nat (length s) + 8) -> cstr_at segs m' a s.
Proof.
  intros W m m' a s (bs & sl & B & Ez & N & S) MU D.
  pose proof (Z.mod_pos_bound (- (a + Z.of_nat (length s) + 1)) 8 ltac:(lia)) as MB.
  pose (k := Z.to_nat ((- (a + Z.of_nat (length s) + 1)) mod 8)).
  assert (Hk : Z.of_nat k = (- (a + Z.of_nat (length s) + 1)) mod 8) by (unfold k; lia).
  clearbody k.
  assert (Lbs : length bs = length s) by (rewrite <- Ez; unfold zs; symmetry; apply length_map).
  assert (Lk : length (firstn k sl) = k) by (rewrite length_firstn; lia).
  exists bs, (firstn k sl). split; [|split; [exact Ez|split; [exact N|rewrite Lk; lia]]].
  rewrite <- (firstn_skipn k sl) in B.
  replace (bs ++ ZERO :: firstn k sl ++ skipn k sl) with ((bs ++ ZERO :: firstn k sl) ++ skipn k sl) in B
    by (rewrite <- app_assoc; reflexivity).
  apply bytes_at_app in B as [B _].
  eapply bytes_at_transport; [exact B | exact MU |].
  eapply p5_disjoint_sub; [exact D | lia |].
  rewrite length_app; cbn [length]. rewrite Lk, Lbs. lia.
Qed.

End Mem.
