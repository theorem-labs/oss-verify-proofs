(** reac-pw/fuzz_segconf: the build-independent part of the kit of the pieces P4, P5, P6 of
    reac_segconf_parse_file (family F3, lib/Prog/reac_segconf_parse_file_pieces_c.v and its UBSan twin). Both builds
    Require it (lib/Prog/pfB_kit.v, lib/U/Prog/pfB_kit.v); it Requires no image, no seg_env and no *_c.v of a build,
    and every memory lemma here is stated for any segment list.

    What it holds:
    - the line account: L_next_holds, L_cstr_skipn_holds (pf_pieces_spec.v's L_next, L_cstr_skipn) and the counters'
      room after one line (pfb_cnt_next);
    - memory over any segment list: a C string kept by a munch apart from its span (pfb_cstr_at_munch_span, and the
      length + 8 form pfb_cstr_at_munch), rconf_at kept by a munch apart from the block (pfb_rconf_at_munch), the
      decision of [outside] (pfb_outside_dec, pfb_not_outside), a stack region kept present by wmono alone
      (pfb_stk_wmono: a writable byte that no segment backs is in the memory itself), find_segment's result
      (pfb_find_segment_in), the read of a saved word (pfb_saved_read). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import StrFun SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec pf_pieces_spec.
Import ListNotations.
Open Scope Z_scope.

(** ** Lists *)
Lemma pfb_in_skipn : forall {A} n (l : list A) x, In x (skipn n l) -> In x l.
Proof.
  intros A n. induction n as [|n IH]; intros l x H; [exact H|].
  destruct l as [|y l]; [destruct H|]. right. exact (IH l x H).
Qed.

Lemma pfb_in_firstn : forall {A} n (l : list A) x, In x (firstn n l) -> In x l.
Proof.
  intros A n. induction n as [|n IH]; intros l x H; [destruct H|].
  destruct l as [|y l]; [destruct H|]. destruct H as [H|H]; [left; exact H | right; exact (IH l x H)].
Qed.

Lemma pfb_skipn_map : forall {A B} (f : A -> B) n l, skipn n (map f l) = map f (skipn n l).
Proof.
  intros A B f n. induction n as [|n IH]; intros l; [reflexivity|].
  destruct l as [|x l]; [reflexivity|]. cbn [map skipn]. apply IH.
Qed.

Lemma pfb_skipn_suffix : forall {A} (pre q : list A), skipn (length (pre ++ q) - length q) (pre ++ q) = q.
Proof.
  intros A pre q. rewrite length_app. replace (length pre + length q - length q)%nat with (length pre) by lia.
  induction pre as [|x pre IH]; [reflexivity|]. cbn [length skipn app]. exact IH.
Qed.

Lemma pfb_skipn_eq : forall {A} (s pre q : list A), s = pre ++ q -> skipn (length s - length q) s = q.
Proof. intros A s pre q E. subst s. apply pfb_skipn_suffix. Qed.

(** ** The line account *)
(** break_nl cuts at the first '\n' (which it drops), or takes the whole rest. *)
Lemma pfb_break_nl_cases : forall p,
  p = fst (break_nl p) ++ NL :: snd (break_nl p) \/ (fst (break_nl p) = p /\ snd (break_nl p) = []).
Proof.
  induction p as [|b r IH]; [right; split; reflexivity|].
  cbn [break_nl]. destruct (Z.eqb_spec b NL) as [E|E].
  - left. cbn [fst snd app]. rewrite E. reflexivity.
  - revert IH. destruct (break_nl r) as [l q]. cbn [fst snd]. intros [IH|[IH1 IH2]].
    + left. rewrite IH. reflexivity.
    + right. subst. split; reflexivity.
Qed.

Lemma pfb_break_nl_len : forall p,
  (length (fst (break_nl p)) + length (snd (break_nl p)) +
     (if (length (fst (break_nl p)) <? length p)%nat then 1 else 0) = length p)%nat /\
  (exists pre, p = pre ++ snd (break_nl p)) /\
  (p <> [] -> (length (snd (break_nl p)) < length p)%nat).
Proof.
  intros p. destruct (pfb_break_nl_cases p) as [E|[E1 E2]].
  - assert (L : length p = (length (fst (break_nl p)) + S (length (snd (break_nl p))))%nat).
    { rewrite E at 1. rewrite length_app. reflexivity. }
    split; [destruct (Nat.ltb_spec (length (fst (break_nl p))) (length p)); lia|].
    split; [|intros _; lia].
    exists (fst (break_nl p) ++ [NL]). rewrite <- app_assoc. exact E.
  - rewrite E2. cbn [length]. rewrite E1.
    split; [destruct (Nat.ltb_spec (length p) (length p)); lia|].
    split; [exists p; rewrite app_nil_r; reflexivity|].
    intros H. destruct p as [|z p]; [exfalso; apply H; reflexivity | cbn; lia].
Qed.

Lemma L_next_holds : L_next.
Proof.
  intros s o Ho. unfold pf_next, pf_line.
  pose proof (length_skipn o s) as Lp.
  pose proof (pfb_break_nl_len (skipn o s)) as (L & (pre & E) & LT).
  assert (NE : skipn o s <> []) by (intros H; rewrite H in Lp; cbn in Lp; lia).
  specialize (LT NE).
  split; [|split; [lia|split; [lia|]]].
  - apply (pfb_skipn_eq s (firstn o s ++ pre)). rewrite <- app_assoc, <- E. symmetry. apply firstn_skipn.
  - revert L. destruct (Nat.ltb_spec (length (fst (break_nl (skipn o s)))) (length (skipn o s)));
    destruct (Nat.ltb_spec (o + length (fst (break_nl (skipn o s))))%nat (length s)); intros L; lia.
Qed.

(** The counters' room after one line: the line takes at least one byte, and adds at most one refusal and one
    overflow. *)
Lemma pfb_cnt_next : forall (rc rc' : rconf) (s : list Z) (o : nat),
  (o < length s)%nat -> pf_cnt rc (length (skipn o s)) ->
  rc_refused rc' <= rc_refused rc + 1 -> rc_overflow rc' <= rc_overflow rc + 1 ->
  pf_cnt rc' (length (skipn (pf_next s o) s)).
Proof.
  intros rc rc' s o Ho [C1 C2] R1 R2.
  destruct (L_next_holds s o Ho) as (_ & N1 & N2 & _).
  rewrite length_skipn in *. unfold pf_cnt. lia.
Qed.

(** The rest of the text from a line start is a C string with the text's slack. *)
Lemma L_cstr_skipn_holds : L_cstr_skipn.
Proof.
  intros segs m t s o (bs & sl & B & Ez & N & Sl) Ho.
  assert (Lbs : length bs = length s) by (rewrite <- Ez; unfold zs; symmetry; apply length_map).
  exists (skipn o bs), sl.
  split; [|split; [|split]].
  - rewrite <- (firstn_skipn o bs) in B. rewrite <- app_assoc in B.
    apply bytes_at_app in B as [_ B]. rewrite length_firstn, Nat.min_l in B by lia. exact B.
  - rewrite <- Ez. unfold zs. symmetry. apply pfb_skipn_map.
  - intros H. apply N. exact (pfb_in_skipn o s 0 H).
  - rewrite length_skipn.
    replace (t + Z.of_nat o + Z.of_nat (length s - o) + 1) with (t + Z.of_nat (length s) + 1) by lia. exact Sl.
Qed.

Lemma pfb_find_segment_in : forall segs a n seg, find_segment segs a n = Some seg ->
  In seg segs /\ Z.of_N (seg_base seg) <= a /\ a + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg).
Proof.
  induction segs as [|s sl IH]; intros a n seg E; cbn in E; [discriminate|].
  match type of E with context [if ?c then _ else _] => destruct c eqn:C end.
  - injection E as <-. apply andb_true_iff in C as [C1 C2]. apply Z.leb_le in C1. apply Z.leb_le in C2.
    split; [left; reflexivity | lia].
  - destruct (IH a n seg E) as (H1 & H2 & H3). split; [right; exact H1 | lia].
Qed.

(** ** Memory, for any segment list *)
Section PfbMem.
Variable segs : list Segment.

Lemma pfb_disjoint_from_sub : forall W a n a' n',
  disjoint_from W a n -> a <= a' -> a' + n' <= a + n -> disjoint_from W a' n'.
Proof.
  induction W as [|[l h] W IH]; cbn [disjoint_from]; intros a n a' n' D H1 H2; [exact I|].
  destruct D as [D1 D2]. split; [lia | exact (IH a n a' n' D2 H1 H2)].
Qed.

Lemma pfb_rconf_at_munch : forall W m m' c rc,
  rconf_at segs m c rc -> munch W m m' -> disjoint_from W c SEG_C_SIZE -> rconf_at segs m' c rc.
Proof.
  intros W m m' c rc (bs & B & E) MU D. exists bs. split; [|exact E].
  eapply bytes_at_transport; [exact B | exact MU |]. destruct E as [L _]. rewrite L. exact D.
Qed.

(** A C string is kept by a munch apart from its span (its bytes, its NUL and the slack to the next 8-byte
    boundary: seg_spec.cstr_span). *)
Lemma pfb_cstr_at_munch_span : forall W m m' a s,
  cstr_at segs m a s -> munch W m m' -> disjoint_from W a (cstr_span a s) -> cstr_at segs m' a s.
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
  eapply pfb_disjoint_from_sub; [exact D | lia |].
  unfold cstr_span. rewrite length_app; cbn [length]. rewrite Lk, Lbs. lia.
Qed.

Lemma pfb_cstr_span_le : forall a s, 0 < cstr_span a s <= Z.of_nat (length s) + 8.
Proof.
  intros a s. unfold cstr_span. pose proof (Z.mod_pos_bound (- (a + Z.of_nat (length s) + 1)) 8 ltac:(lia)). lia.
Qed.

Lemma pfb_cstr_at_munch : forall W m m' a s,
  cstr_at segs m a s -> munch W m m' -> disjoint_from W a (Z.of_nat (length s) + 8) -> cstr_at segs m' a s.
Proof.
  intros W m m' a s H MU D. eapply pfb_cstr_at_munch_span; [exact H | exact MU |].
  pose proof (pfb_cstr_span_le a s). eapply pfb_disjoint_from_sub; [exact D | lia | lia].
Qed.

(** A C string's bytes are bytes. *)
Lemma pfb_cstr_range : forall m a s, cstr_at segs m a s -> Forall (fun x => 0 <= x < 256) s.
Proof.
  intros m a s (bs & sl & _ & Ez & _). rewrite <- Ez. unfold zs. apply Forall_map.
  apply Forall_forall. intros b _. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 8) with 256 in R. lia.
Qed.

Lemma pfb_outside_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[l h] W IH]; intros x; cbn [outside]; [left; exact I|].
  destruct (IH x) as [H|H].
  - destruct (Z_le_gt_dec l x), (Z_lt_ge_dec x h);
      first [ right; intros [H1 _]; apply H1; lia
            | left; split; [lia | exact H] ].
  - right. intros [_ H2]. exact (H H2).
Qed.

Lemma pfb_not_outside : forall W x, ~ outside W x -> exists l h, In (l, h) W /\ l <= x < h.
Proof.
  induction W as [|[l h] W IH]; intros x H; cbn [outside] in H; [exfalso; exact (H I)|].
  destruct (Z_le_gt_dec l x), (Z_lt_ge_dec x h).
  - exists l, h. split; [left; reflexivity | lia].
  - destruct (IH x) as (l' & h' & Hin & Hr); [intros O; apply H; split; [lia | exact O]|].
    exists l', h'. split; [right; exact Hin | exact Hr].
  - destruct (IH x) as (l' & h' & Hin & Hr); [intros O; apply H; split; [lia | exact O]|].
    exists l', h'. split; [right; exact Hin | exact Hr].
  - destruct (IH x) as (l' & h' & Hin & Hr); [intros O; apply H; split; [lia | exact O]|].
    exists l', h'. split; [right; exact Hin | exact Hr].
Qed.

(** A byte the writable view has, which no image byte backs (seg_rom is None there) and whose segment, if any, is
    readable, is in the memory itself. So wmono keeps a present stack region present, whatever was written. *)
Lemma pfb_wview_mem : forall m (x : word),
  (forall seg, In seg segs -> seg_readable seg = true) ->
  seg_rom segs x = None -> wview segs m x <> None -> exists b, m x = Some b.
Proof.
  intros m x RD NR Hw. destruct (m x) as [b|] eqn:E; [exists b; reflexivity|]. exfalso. apply Hw. clear Hw.
  unfold wview. rewrite E.
  unfold seg_rom, memory_read in NR. change (Z.of_N 1) with 1 in NR.
  destruct (find_segment segs (bv_unsigned x) 1) as [sg|] eqn:F; [|reflexivity].
  rewrite (RD sg (proj1 (pfb_find_segment_in _ _ _ _ F))) in NR.
  destruct (seg_writable sg); [|reflexivity].
  change (N.to_nat 1) with 1%nat in NR. cbn [segment_read_bytes] in NR.
  destruct (segment_byte_at (seg_bytes sg) (Z.to_N (bv_unsigned x - Z.of_N (seg_base sg)))) as [b|];
    [cbn in NR; discriminate NR | reflexivity].
Qed.

Lemma pfb_stk_wmono : forall m m' lo hi,
  (forall seg, In seg segs -> seg_readable seg = true) ->
  (forall a, lo <= a < hi -> seg_rom segs (wa a) = None) ->
  stk segs m lo hi -> wmono segs m m' -> stk segs m' lo hi.
Proof.
  intros m m' lo hi RD NR (H1 & H2 & H) WM. split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as [Hw _]. pose proof (WM _ Hw) as Hw'. split; [exact Hw'|].
  destruct (pfb_wview_mem m' (wa a) RD (NR a Ha) Hw') as [b Hb].
  exists b. unfold mrd. rewrite Hb. reflexivity.
Qed.

(** A byte of a present region whose image byte is None is in the memory itself. *)
Lemma pfb_mrd_some : forall m (x : word) b, mrd segs m x = Some b -> seg_rom segs x = None -> m x = Some b.
Proof. intros m x b H N. unfold mrd in H. destruct (m x); [exact H|]. congruence. Qed.

Lemma pfb_rom_none : forall (x : word), find_segment segs (bv_unsigned x) 1 = None -> seg_rom segs x = None.
Proof. intros x H. unfold seg_rom, memory_read. change (Z.of_N 1) with 1. rewrite H. reflexivity. Qed.

(** The task-memory condition of a byte that reads Some (MemNorm.task_mem's, unfolded). *)
Lemma pfb_mrd_task : forall m (x : word) b,
  (forall a b, m a = Some b -> find_segment segs (bv_unsigned a) 1 <> None \/ bv_unsigned a < TASK_SIZE) ->
  mrd segs m x = Some b -> find_segment segs (bv_unsigned x) 1 <> None \/ bv_unsigned x < TASK_SIZE.
Proof.
  intros m x b TM H. unfold mrd in H. destruct (m x) as [b'|] eqn:E; [exact (TM x b' E)|].
  left. intros Hn. rewrite (pfb_rom_none x Hn) in H. discriminate.
Qed.

(** A stack region's bytes are writable: store_ok there. *)
Lemma pfb_stk_store_ok : forall m lo hi a (n : nat), stk segs m lo hi -> lo <= a -> a + Z.of_nat n <= hi ->
  store_ok segs m (wa a) n = true.
Proof.
  intros m lo hi a n (H1 & H2 & H) Ha Hn.
  replace a with (a + 0) by lia. apply (wr_at_store_ok segs m a (Z.of_nat n) 0 n); [|lia|lia].
  split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (H (a + i) ltac:(lia))).
Qed.

(** The word at the k-th 8-byte slot of a saved list, as a load reads it. *)
Lemma pfb_concat_le8_length : forall ws, length (concat (map le8 ws)) = (8 * length ws)%nat.
Proof.
  induction ws as [|w ws IH]; [reflexivity|]. cbn [map concat length]. rewrite length_app, length_le8, IH. lia.
Qed.

Lemma pfb_saved_read : forall m a ws k, saved_at segs m a ws -> (k < length ws)%nat ->
  ov_read_bytes segs m (wa (a + 8 * Z.of_nat k)) 8 = Some (le8 (nth k ws (Z_to_bv 64 0))).
Proof.
  intros m a ws k. revert a k. induction ws as [|w ws IH]; intros a k H Hk; cbn [length] in Hk; [lia|].
  unfold saved_at in H. cbn [map concat] in H. apply bytes_at_app in H as [H0 H1]. rewrite length_le8 in H1.
  destruct k as [|k].
  - cbn [nth]. replace (a + 8 * Z.of_nat 0) with (a + Z.of_nat 0) by lia.
    rewrite (bytes_at_ov_read segs m a (le8 w) 0 8 H0) by (rewrite length_le8; lia).
    cbn [skipn]. solve [ reflexivity | f_equal; apply firstn_all2; rewrite length_le8; lia ].
  - cbn [nth]. replace (a + 8 * Z.of_nat (S k)) with (a + Z.of_nat 8 + 8 * Z.of_nat k) by lia.
    apply IH; [exact H1 | lia].
Qed.

End PfbMem.

(** ** Byte lists *)
Lemma pfb_zs_zb_range : forall l, Forall (fun x => 0 <= x < 256) l -> zs (zb l) = l.
Proof.
  unfold zs, zb. induction l as [|x l IH]; intros H; [reflexivity|].
  inversion H as [|y ys Hx Hl]; subst. cbn [map]. rewrite IH by exact Hl. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
  change (2 ^ 8) with 256. apply Z.mod_small. lia.
Qed.

Lemma pfb_firstn_cons : forall (B : list Z) n x rest, firstn (S n) B = x :: rest ->
  exists B', B = x :: B' /\ firstn n B' = rest.
Proof.
  intros B n x rest H. destruct B as [|b B']; cbn [firstn] in H; [discriminate|].
  exists B'. injection H as H1 H2. split; [rewrite H1; reflexivity | exact H2].
Qed.

(** Two prefixes of the same list that each end at their own (only) NUL are the same string. *)
Lemma pfb_prefix_nul_eq : forall (l w B : list Z), ~ In 0 l -> ~ In 0 w ->
  firstn (S (length l)) B = l ++ [0] -> firstn (S (length w)) B = w ++ [0] -> l = w.
Proof.
  induction l as [|a l IH]; intros w B Hl Hw H1 H2.
  - cbn [length app] in H1. destruct (pfb_firstn_cons B 0 0 [] H1) as (B' & EB & _).
    destruct w as [|c w]; [reflexivity|].
    cbn [length app] in H2. destruct (pfb_firstn_cons B _ c (w ++ [0]) H2) as (B'' & EB2 & _).
    exfalso. apply Hw. left. rewrite EB in EB2. injection EB2 as EB2 _. symmetry. exact EB2.
  - assert (Ha : a <> 0) by (intros E; apply Hl; left; exact E).
    cbn [length app] in H1. destruct (pfb_firstn_cons B _ a (l ++ [0]) H1) as (B' & EB & HB).
    destruct w as [|c w].
    + cbn [length app] in H2. destruct (pfb_firstn_cons B 0 0 [] H2) as (B3 & EB3 & _).
      rewrite EB in EB3. injection EB3 as E1 _. exfalso. apply Ha. exact E1.
    + cbn [length app] in H2. destruct (pfb_firstn_cons B _ c (w ++ [0]) H2) as (B'' & EB2 & HB2).
      rewrite EB in EB2. injection EB2 as E1 E2. subst c B''.
      f_equal. eapply IH; [intros H; apply Hl; right; exact H
                           | intros H; apply Hw; right; exact H | exact HB | exact HB2].
Qed.

(** ** cut_nul, takewhile / dropwhile, trim *)
Lemma pfb_cut_nul_id : forall l, ~ In 0 l -> cut_nul l = l.
Proof.
  induction l as [|x l IH]; intros H; [reflexivity|].
  cbn [cut_nul]. destruct (Z.eqb_spec x 0) as [->|Hx]; [exfalso; apply H; left; reflexivity|].
  rewrite IH; [reflexivity|]. intros Hin; apply H; right; exact Hin.
Qed.

Lemma pfb_cut_nul_nz : forall l, ~ In 0 (cut_nul l).
Proof.
  induction l as [|x l IH]; cbn [cut_nul]; [intros []|].
  destruct (Z.eqb_spec x 0) as [->|Hx]; [intros []|].
  intros [H|H]; [apply Hx; exact H | exact (IH H)].
Qed.

Lemma pfb_cut_nul_sub : forall l x, In x (cut_nul l) -> In x l.
Proof.
  induction l as [|y l IH]; cbn [cut_nul]; intros x H; [exact H|].
  destruct (Z.eqb_spec y 0) as [->|Hy]; [destruct H|].
  destruct H as [H|H]; [left; exact H | right; exact (IH x H)].
Qed.

Lemma pfb_take_drop : forall (P : Z -> bool) l, takewhile P l ++ dropwhile P l = l.
Proof.
  intros P. induction l as [|x l IH]; cbn [takewhile dropwhile]; [reflexivity|].
  destruct (P x); [cbn [app]; rewrite IH; reflexivity | reflexivity].
Qed.

Lemma pfb_dropwhile_skipn : forall (P : Z -> bool) l, dropwhile P l = skipn (length (takewhile P l)) l.
Proof.
  intros P. induction l as [|x l IH]; [reflexivity|].
  cbn [takewhile dropwhile]. destruct (P x); cbn [length skipn]; [exact IH | reflexivity].
Qed.

Lemma pfb_dropwhile_sub : forall (P : Z -> bool) l x, In x (dropwhile P l) -> In x l.
Proof.
  intros P. induction l as [|y l IH]; intros x H; [exact H|].
  cbn [dropwhile] in H. destruct (P y); [right; exact (IH x H) | exact H].
Qed.

Lemma pfb_trim_end_le : forall s e fuel, (trim_end s e fuel <= e)%nat.
Proof.
  intros s e. induction e as [|e' IH]; intros fuel; destruct fuel as [|f]; cbn [trim_end].
  - apply Nat.le_refl.
  - apply Nat.le_refl.
  - apply Nat.le_refl.
  - destruct (blank (nth e' s 0)).
    + pose proof (IH f). lia.
    + apply Nat.le_refl.
Qed.

Lemma L_trim_holds : L_trim.
Proof.
  intros l Hl. unfold trim_lead, r_trim. rewrite (pfb_cut_nul_id l Hl). cbv zeta.
  set (s1 := dropwhile blank l).
  set (k := trim_end s1 (length s1) (length s1)).
  assert (Hk : (k <= length s1)%nat) by (unfold k; apply pfb_trim_end_le).
  assert (Hs1 : s1 = skipn (length (takewhile blank l)) l) by (unfold s1; apply pfb_dropwhile_skipn).
  assert (Hlen : (length (takewhile blank l) + length s1 = length l)%nat).
  { unfold s1. rewrite <- (pfb_take_drop blank l) at 3. rewrite length_app. reflexivity. }
  assert (Hfk : length (firstn k s1) = k) by (rewrite length_firstn; lia).
  split; [rewrite Hfk; lia|].
  split; [rewrite Hfk, <- Hs1; reflexivity|].
  intros Hin. apply Hl. eapply pfb_dropwhile_sub with (P := blank).
  fold s1. eapply pfb_in_firstn. exact Hin.
Qed.

(** ** The fold loops *)
Lemma pfb_lower_nz : forall x, x <> 0 -> lower x <> 0.
Proof.
  intros x Hx. unfold lower. destruct ((65 <=? x) && (x <=? 90)) eqn:E; [|exact Hx].
  apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2. lia.
Qed.

Lemma pfb_r_low_fold : forall v li cap, r_low v li cap = map lower (firstn (cap - 1 - li) (cut_nul v)).
Proof.
  induction v as [|q r IH]; intros li cap.
  - cbn [r_low cut_nul]. destruct (cap - 1 - li)%nat; reflexivity.
  - destruct (Z.eqb_spec q 0) as [->|Hq].
    + cbn [r_low cut_nul]. rewrite Z.eqb_refl. destruct (cap - 1 - li)%nat; reflexivity.
    + cbn [r_low cut_nul]. replace (q =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hq).
      destruct (Nat.ltb_spec (li + 1) cap) as [Hlt|Hge].
      * replace (cap - 1 - li)%nat with (S (cap - 1 - S li))%nat by lia.
        cbn [firstn map]. rewrite IH. reflexivity.
      * replace (cap - 1 - li)%nat with 0%nat by lia. reflexivity.
Qed.

Lemma L_low_holds : L_low.
Proof.
  intros v cap. split.
  - rewrite pfb_r_low_fold, Nat.sub_0_r. reflexivity.
  - rewrite pfb_r_low_fold. intros Hin. apply in_map_iff in Hin as (x & Hx & Hinx).
    apply (pfb_in_firstn _ _ _) in Hinx.
    destruct (Z.eq_dec x 0) as [->|Hne]; [exact (pfb_cut_nul_nz v Hinx)|].
    exact (pfb_lower_nz x Hne Hx).
Qed.

(** ** strcmp and strcasecmp on NUL-free strings *)
Lemma pfb_strcmp_eq : forall l w, ~ In 0 l -> ~ In 0 w -> (strcmp l w = 0 <-> l = w).
Proof.
  induction l as [|a l IH]; intros w Hl Hw.
  - destruct w as [|b w]; [split; reflexivity|].
    assert (Hb : b <> 0) by (intros E; apply Hw; left; exact E).
    cbn [strcmp]. split; [intros H; exfalso; lia | intros H; discriminate H].
  - assert (Ha : a <> 0) by (intros E; apply Hl; left; exact E).
    destruct w as [|b w].
    + cbn [strcmp]. split; [intros H; exfalso; lia | intros H; discriminate H].
    + cbn [strcmp]. destruct (Z.eqb_spec a b) as [Eab|Nab].
      * subst b. replace (a =? 0) with false by (symmetry; apply Z.eqb_neq; exact Ha).
        cbn [negb andb].
        rewrite (IH w ltac:(intros H; apply Hl; right; exact H) ltac:(intros H; apply Hw; right; exact H)).
        split; [intros ->; reflexivity | intros H; congruence].
      * cbn [andb]. split; [intros H; exfalso; lia | intros H; exfalso; apply Nab; congruence].
Qed.

Lemma pfb_tolower_0 : tolower 0 = 0.
Proof. reflexivity. Qed.

Lemma pfb_tolower_nz : forall a, a <> 0 -> tolower a <> 0.
Proof.
  intros a Ha. unfold tolower. destruct ((65 <=? a) && (a <=? 90)); [|exact Ha].
  intros H. apply Z.lor_eq_0_iff in H as [_ H]. discriminate H.
Qed.

Lemma pfb_strcasecmp_map : forall l w, ~ In 0 l -> ~ In 0 w ->
  (map tolower l = map tolower w <-> strcasecmp l w = 0).
Proof.
  induction l as [|a l IH]; intros w Hl Hw.
  - destruct w as [|b w]; cbn [map strcasecmp hd0].
    + rewrite pfb_tolower_0. split; intros _; reflexivity.
    + assert (Hb : b <> 0) by (intros E; apply Hw; left; exact E).
      pose proof (pfb_tolower_nz b Hb) as Pb. rewrite pfb_tolower_0.
      split; [intros H; discriminate H | intros H; exfalso; lia].
  - assert (Ha : a <> 0) by (intros E; apply Hl; left; exact E).
    destruct w as [|b w]; cbn [map strcasecmp hd0].
    + pose proof (pfb_tolower_nz a Ha) as Pa. rewrite pfb_tolower_0.
      split; [intros H; discriminate H | intros H; exfalso; lia].
    + assert (Hb : b <> 0) by (intros E; apply Hw; left; exact E).
      destruct (IH w ltac:(intros H; apply Hl; right; exact H)
                      ltac:(intros H; apply Hw; right; exact H)) as [F1 F2].
      replace (a =? 0) with false by (symmetry; apply Z.eqb_neq; exact Ha).
      replace (b =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hb).
      cbn [negb andb].
      destruct (Z.eqb_spec (tolower a) (tolower b)) as [E|E].
      * rewrite orb_true_r. split.
        -- intros H. apply F1. congruence.
        -- intros H. rewrite E. f_equal. exact (F2 H).
      * replace (a =? b) with false
          by (symmetry; apply Z.eqb_neq; intros Eab; apply E; rewrite Eab; reflexivity).
        cbn [orb]. split.
        -- intros H. exfalso. apply E. congruence.
        -- intros H. exfalso. lia.
Qed.

(** ** O1: the bcmp and the word compare of the role branch *)
Lemma pfb_memcmp_zero : forall n (ls rs : list byte) v, memcmp_model ls rs n = Some v ->
  (v = 0 <-> firstn n (zs ls) = firstn n (zs rs)).
Proof.
  unfold zs. induction n as [|n IH]; intros ls rs v H.
  - cbn in H. injection H as <-. split; intros _; reflexivity.
  - cbn [memcmp_model] in H. destruct ls as [|a ls]; [discriminate|].
    destruct rs as [|b rs]; [discriminate|].
    cbn [map firstn]. destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [E|E].
    + specialize (IH ls rs v H). rewrite E. split.
      * intros Hv. f_equal. apply (proj1 IH Hv).
      * intros Heq. apply (proj2 IH). congruence.
    + injection H as <-. split.
      * intros Hv. exfalso. lia.
      * intros Heq. exfalso. apply E. congruence.
Qed.

Lemma O1_bcmp_lit_holds : O1_bcmp_lit.
Proof.
  intros B l w v Hl Hw Hwr HB HM.
  pose proof (pfb_memcmp_zero _ _ _ _ HM) as [F1 F2].
  assert (HZ : zs (zb (w ++ [0])) = w ++ [0]).
  { apply pfb_zs_zb_range. apply Forall_app. split; [exact Hwr | repeat constructor; lia]. }
  assert (HR : firstn (S (length w)) (zs (zb (w ++ [0]))) = w ++ [0]).
  { rewrite HZ. apply firstn_all2. rewrite length_app. cbn [length]. lia. }
  rewrite HR in F1, F2.
  rewrite (pfb_strcmp_eq l w Hl Hw).
  split.
  - intros Hv. eapply pfb_prefix_nul_eq; [exact Hl | exact Hw | exact HB | exact (F1 Hv)].
  - intros ->. apply F2. exact HB.
Qed.

Lemma pfb_firstn4_bytes : forall (B : list byte), (4 <= length B)%nat ->
  firstn 4 (zs B) = [bv_unsigned (nth 0 B ZERO); bv_unsigned (nth 1 B ZERO);
                     bv_unsigned (nth 2 B ZERO); bv_unsigned (nth 3 B ZERO)].
Proof.
  intros B H. do 4 (destruct B as [|? B]; [cbn [length] in H; lia|]). reflexivity.
Qed.

Lemma pfb_word4_lit : forall (B : list byte) (c0 c1 c2 : Z), (4 <= length B)%nat ->
  0 <= c0 < 256 -> 0 <= c1 < 256 -> 0 <= c2 < 256 ->
  (pf_word4 B = c0 + 256 * c1 + 65536 * c2 <-> firstn 4 (zs B) = [c0; c1; c2; 0]).
Proof.
  intros B c0 c1 c2 HB H0 H1 H2.
  rewrite (pfb_firstn4_bytes B HB). unfold pf_word4. cbv zeta beta.
  pose proof (bv_unsigned_in_range 8 (nth 0 B ZERO)) as R0.
  pose proof (bv_unsigned_in_range 8 (nth 1 B ZERO)) as R1.
  pose proof (bv_unsigned_in_range 8 (nth 2 B ZERO)) as R2.
  pose proof (bv_unsigned_in_range 8 (nth 3 B ZERO)) as R3.
  unfold bv_modulus in R0, R1, R2, R3. cbn [Z.of_N] in R0, R1, R2, R3.
  change (2 ^ 8) with 256 in R0, R1, R2, R3.
  destruct (Z.ltb_spec (bv_unsigned (nth 3 B ZERO)) 128) as [Hlt|Hge].
  - split.
    + intros E. assert (A0 : bv_unsigned (nth 0 B ZERO) = c0) by lia.
      assert (A1 : bv_unsigned (nth 1 B ZERO) = c1) by lia.
      assert (A2 : bv_unsigned (nth 2 B ZERO) = c2) by lia.
      assert (A3 : bv_unsigned (nth 3 B ZERO) = 0) by lia.
      rewrite A0, A1, A2, A3. reflexivity.
    + intros E. injection E as E0 E1 E2 E3. rewrite E0, E1, E2, E3. lia.
  - split.
    + intros E. exfalso. lia.
    + intros E. injection E as E0 E1 E2 E3. exfalso. lia.
Qed.

Lemma O1_word_lit_holds : O1_word_lit.
Proof.
  intros B l Hl HB4 HB.
  assert (TL : S_tap = [116; 97; 112]) by (vm_compute; reflexivity).
  assert (BL : S_box = [98; 111; 120]) by (vm_compute; reflexivity).
  assert (TN : ~ In 0 [116; 97; 112]) by (cbn [In]; intros [H|[H|[H|H]]]; try discriminate H; exact H).
  assert (BN : ~ In 0 [98; 111; 120]) by (cbn [In]; intros [H|[H|[H|H]]]; try discriminate H; exact H).
  pose proof (pfb_word4_lit B 116 97 112 HB4 ltac:(lia) ltac:(lia) ltac:(lia)) as WT.
  pose proof (pfb_word4_lit B 98 111 120 HB4 ltac:(lia) ltac:(lia) ltac:(lia)) as WB.
  replace (116 + 256 * 97 + 65536 * 112) with PF_TAP_WORD in WT by (vm_compute; reflexivity).
  replace (98 + 256 * 111 + 65536 * 120) with PF_BOX_WORD in WB by (vm_compute; reflexivity).
  split.
  - rewrite WT, (pfb_strcmp_eq l S_tap Hl ltac:(rewrite TL; exact TN)), TL. split.
    + intros E. eapply pfb_prefix_nul_eq; [exact Hl | exact TN | exact HB | exact E].
    + intros ->. exact HB.
  - rewrite WB, (pfb_strcmp_eq l S_box Hl ltac:(rewrite BL; exact BN)), BL. split.
    + intros E. eapply pfb_prefix_nul_eq; [exact Hl | exact BN | exact HB | exact E].
    + intros ->. exact HB.
Qed.

(** ** The refuse record (SegModel.refuse keeps every field but refused and refusal) *)
Lemma pfb_refuse_shape : forall rc l f a,
  rc_seg (refuse rc l f a) = rc_seg rc /\ rc_overflow (refuse rc l f a) = rc_overflow rc /\
  rc_reading (refuse rc l f a) = rc_reading rc /\ rc_gen (refuse rc l f a) = rc_gen rc /\
  rc_refused (refuse rc l f a) = rc_refused rc + 1 /\
  (length (rc_refusal (refuse rc l f a)) <= S (length (rc_refusal rc)))%nat.
Proof.
  intros rc l f a. unfold refuse. cbv zeta.
  destruct (8 <=? Z.of_nat (length (rc_refusal rc)));
    [cbn [rc_seg rc_overflow rc_reading rc_gen rc_refused rc_refusal]; repeat split; lia|].
  destruct ((snprintf_r (r_addr_fmt l) (r_addr_args rc l) <? 0) ||
            (200 <=? snprintf_r (r_addr_fmt l) (r_addr_args rc l)));
    cbn [rc_seg rc_overflow rc_reading rc_gen rc_refused rc_refusal];
    repeat split; try lia. rewrite length_app. cbn [length]. lia.
Qed.

Lemma pfb_refuse_refused : forall rc l f a, rc_refused (refuse rc l f a) = rc_refused rc + 1.
Proof. intros rc l f a. exact (proj1 (proj2 (proj2 (proj2 (proj2 (pfb_refuse_shape rc l f a)))))). Qed.

Lemma pfb_refuse_overflow : forall rc l f a, rc_overflow (refuse rc l f a) = rc_overflow rc.
Proof. intros rc l f a. exact (proj1 (proj2 (pfb_refuse_shape rc l f a))). Qed.

Lemma pfb_refuse_seg : forall rc l f a, rc_seg (refuse rc l f a) = rc_seg rc.
Proof. intros rc l f a. exact (proj1 (pfb_refuse_shape rc l f a)). Qed.

Lemma pfb_refuse_nref : forall rc l f a, (length (rc_refusal rc) <= 8)%nat ->
  (length (rc_refusal (refuse rc l f a)) <= 8)%nat.
Proof.
  intros rc l f a H. unfold refuse. cbv zeta.
  destruct (Z.leb_spec 8 (Z.of_nat (length (rc_refusal rc)))) as [E|E];
    [cbn [rc_refusal]; exact H|].
  destruct ((snprintf_r (r_addr_fmt l) (r_addr_args rc l) <? 0) ||
            (200 <=? snprintf_r (r_addr_fmt l) (r_addr_args rc l)));
    cbn [rc_refusal]; [exact H|]. rewrite length_app. cbn [length]. lia.
Qed.

(** The counters after one line that made at most one refusal and at most one overflow. *)
Lemma pfb_cnt_refuse : forall rc l f a k, pf_cnt rc (S k) -> pf_cnt (refuse rc l f a) k.
Proof.
  intros rc l f a k [C1 C2]. unfold pf_cnt.
  rewrite pfb_refuse_refused, pfb_refuse_overflow. split; lia.
Qed.
