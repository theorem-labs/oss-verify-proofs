(** m_file (UBSan build, image 1696d6c34ffd, 0x14268): the sub-piece S_MFU_KROLE of S_MF_LINE (U/Prog/mfu_cuts.v,
    family F3). From KDISP 0x145d8 to KMODEL 0x146c0 or the tail 0x146b4:
      0x145d8-0x145e4  a2 = "role" (0x10298), a1 = kl, `jal ieq` (a0 = k from KDISP); `beqz a0` to KMODEL 0x146c0
      0x145ec-0x145fc  a0 = v (0x90(sp)), a2 = low = sp + 0x48, a3 = 64, a1 = vl, `jal fold`; s5 = ln
      0x14604-0x14614  s1 = 0, s4 = m_key.role (0x10a10), s8 = m_key.words (0x21440)
      0x14618-0x1464c  the words loop: s6 = words[i], strlen(s6) = ln and bcmp(s6, low, ln) = 0 goes to 0x14730;
                       s1 -= 4, s4 += 4, s8 += 8 until s1 = -20
      0x14650-0x14668  m_refuse(c, line + 1), s8 = c + MC_N (0x28(sp)), s6 = 511, then 0x14688 s4 = 1, the tail
      0x14730-0x14778  a0 = 4 i against ~m_key.role (the wrap trap 0x14748, dead), s8 restored, s6 = 511, cur & 3
                       (the trap 0x14754, dead: cur = c + 256 gi), role = `lw 0(s4)` = i, s4 = 1,
                       g->role_set = 1 (0x14764), g->role = i (0x14768), a0 = g + 0x3c, a2 = "%s"
      0x148b0-0x148bc  a1 = 96, a3 = c->reading (0x20(sp)), `jal snprintf`, `j` the tail.
    The words loop is an induction on the words left: its invariant is SegModel.word_go of the words not yet tried,
    which at i = 0 is h_role_word (h_fold v 64). The callee calls use the kit U/Prog/mfu_kit.v (mfu_ieq,
    mfu_refuse, mfu_snprintf_file, mfu_tail, mfu_lits, mfu_words, mfu_roles) and the contracts of fold, strlen and
    bcmp directly; the two block stores use Prog/mfp_mconf.v. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP Tac ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec mfu_facts mfp_facts mfp_mconf.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import seg_env m_file_c mfu_cuts mfu_kit.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import m_refuse_c ieq_c snprintf_c fold_c strlen_c bcmp_c.
Import ListNotations.
Open Scope Z_scope.

(** ** The role words: m_key.words[i] points to the i-th of SegModel's words. *)
Definition KRL_WORDS : list (list Z) := [S_auto; S_master; S_slave; S_tap; S_box].
Definition KRL_WADDR : list Z := [0x1030e; 0x10548; 0x1075c; 0x10470; 0x10303].

(** ** Byte lists *)
Lemma krl_zs_len : forall l, length (zs l) = length l.
Proof. intros l. unfold zs. apply length_map. Qed.

Lemma krl_zs_app : forall a b, zs (a ++ b) = zs a ++ zs b.
Proof. intros a b. unfold zs. apply map_app. Qed.

Lemma krl_zs_sub : forall (bs : list byte) k n, zs (firstn n (skipn k bs)) = firstn n (skipn k (zs bs)).
Proof. intros bs k n. unfold zs. rewrite skipn_map, firstn_map. reflexivity. Qed.

Lemma krl_zs_nonul : forall l : list byte, ~ In 0 (zs l) -> ~ In (Z_to_bv 8 0) l.
Proof.
  intros l H Hin. apply H. unfold zs. apply in_map_iff. exists (Z_to_bv 8 0). split; [reflexivity | exact Hin].
Qed.

Lemma krl_bu8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hz.
Qed.

Lemma krl_zs_zb : forall l, Forall (fun x => 0 <= x < 256) l -> zs (zb l) = l.
Proof.
  induction l as [|x l IH]; intros H; [reflexivity|]. apply Forall_cons_iff in H as [Hx Hl].
  cbn [zs zb map]. unfold zs, zb in IH. rewrite krl_bu8 by exact Hx. f_equal. apply IH. exact Hl.
Qed.

Lemma krl_zs_range : forall l : list byte, Forall (fun x => 0 <= x < 256) (zs l).
Proof.
  intros l. apply Forall_forall. intros x Hx. unfold zs in Hx. apply in_map_iff in Hx as (b & <- & _).
  pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. exact R.
Qed.

Lemma krl_in_firstn : forall (A : Type) (x : A) n l, In x (firstn n l) -> In x l.
Proof. intros A x n l H. rewrite <- (firstn_skipn n l). apply in_or_app. left. exact H. Qed.

Lemma krl_in_skipn : forall (A : Type) (x : A) n l, In x (skipn n l) -> In x l.
Proof. intros A x n l H. rewrite <- (firstn_skipn n l). apply in_or_app. right. exact H. Qed.

Lemma krl_firstn_prefix : forall (l1 l2 : list Z) n, length l1 = n -> firstn n (l1 ++ l2) = l1.
Proof.
  intros l1 l2 n <-. rewrite firstn_app, firstn_all, Nat.sub_diag. cbn [firstn]. apply app_nil_r.
Qed.

Lemma krl_line_le : forall rest, (length (mf_line rest) <= length rest)%nat.
Proof.
  intros rest. destruct (mf_line_rest rest) as [[E _]|[E _]].
  - pose proof (f_equal (@length Z) E) as EL. rewrite app_length in EL. cbn [length] in EL. lia.
  - pose proof (f_equal (@length Z) E) as EL. lia.
Qed.

(** memcmp over n bytes: a difference of two bytes, 0 exactly when the first n bytes agree. *)
Lemma krl_memcmp : forall n (l r : list byte), (n <= length l)%nat -> (n <= length r)%nat ->
  exists w, memcmp_model l r n = Some w /\ -256 < w < 256 /\ (w = 0 <-> firstn n (zs l) = firstn n (zs r)).
Proof.
  induction n as [|n IH]; intros l r Hl Hr.
  - exists 0. split; [reflexivity|]. split; [lia|]. split; intros _; reflexivity.
  - destruct l as [|a l]; [cbn in Hl; lia|]. destruct r as [|b r]; [cbn in Hr; lia|].
    cbn [length] in Hl, Hr.
    pose proof (bv_unsigned_in_range 8 a) as Ra. pose proof (bv_unsigned_in_range 8 b) as Rb.
    change (bv_modulus 8) with 256 in Ra, Rb.
    cbn [memcmp_model]. unfold zs. cbn [map firstn]. fold (zs l). fold (zs r).
    destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [E|E].
    + destruct (IH l r ltac:(lia) ltac:(lia)) as (w & Ew & Rw & Iw). exists w.
      split; [exact Ew|]. split; [exact Rw|]. split; intros H.
      * apply Iw in H. rewrite H, E. reflexivity.
      * apply Iw. injection H as H1 H2. exact H2.
    + exists (bv_unsigned a - bv_unsigned b). split; [reflexivity|]. split; [lia|].
      split; [intros H; lia | intros H; injection H as H1 H2; lia].
Qed.

(** ** The words *)
Lemma krl_words_len : forall i, (i < 5)%nat -> (length (nth i KRL_WORDS []) <= 6)%nat.
Proof. intros i Hi. do 5 (destruct i as [|i]; [cbn; lia|]). lia. Qed.

Lemma krl_skipn_words : forall i, (i < 5)%nat -> skipn i KRL_WORDS = nth i KRL_WORDS [] :: skipn (S i) KRL_WORDS.
Proof. intros i Hi. do 5 (destruct i as [|i]; [reflexivity|]). lia. Qed.

Lemma krl_word_hit : forall w low,
  ((length w =? length low)%nat && leqb (firstn (length low) w) low) = true <-> w = low.
Proof.
  intros w low. split.
  - intros H. apply andb_true_iff in H as [H1 H2]. apply Nat.eqb_eq in H1. rewrite <- H1, firstn_all in H2.
    apply leqb_eq. exact H2.
  - intros <-. rewrite Nat.eqb_refl, firstn_all. cbn [andb]. apply leqb_eq. reflexivity.
Qed.

Lemma krl_inv_miss : forall i low z, (i < 5)%nat ->
  ((length (nth i KRL_WORDS []) =? length low)%nat && leqb (firstn (length low) (nth i KRL_WORDS [])) low) = false ->
  word_go (skipn i KRL_WORDS) low z = word_go (skipn (S i) KRL_WORDS) low (z + 1).
Proof. intros i low z Hi H. rewrite (krl_skipn_words i Hi). cbn [word_go]. rewrite H. reflexivity. Qed.

Lemma krl_inv_hit : forall i low z, (i < 5)%nat ->
  ((length (nth i KRL_WORDS []) =? length low)%nat && leqb (firstn (length low) (nth i KRL_WORDS [])) low) = true ->
  word_go (skipn i KRL_WORDS) low z = Some z.
Proof. intros i low z Hi H. rewrite (krl_skipn_words i Hi). cbn [word_go]. rewrite H. reflexivity. Qed.

Lemma krl_words_cstr : forall m, mem_inv rsegs m -> forall i, (i < 5)%nat ->
  cstr_at rsegs m (nth i KRL_WADDR 0) (nth i KRL_WORDS []).
Proof.
  intros m MI i Hi. destruct (mfu_lits m MI) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & L0 & L1 & L2 & L3 & L4).
  destruct i as [|[|[|[|[|i]]]]]; [exact L0 | exact L1 | exact L2 | exact L3 | exact L4 | lia].
Qed.

Lemma krl_words_cell : forall m, words_img m -> forall i, (i < 5)%nat ->
  cell8 m (M_KEY_WORDS + 8 * Z.of_nat i) (nth i KRL_WADDR 0).
Proof.
  intros m WI i Hi. destruct (mfu_words m WI) as (W0 & W1 & W2 & W3 & W4).
  destruct i as [|[|[|[|[|i]]]]]; [| | | | | lia].
  - replace (M_KEY_WORDS + 8 * Z.of_nat 0) with M_KEY_WORDS by lia. exact W0.
  - replace (M_KEY_WORDS + 8 * Z.of_nat 1) with (M_KEY_WORDS + 8) by lia. exact W1.
  - replace (M_KEY_WORDS + 8 * Z.of_nat 2) with (M_KEY_WORDS + 16) by lia. exact W2.
  - replace (M_KEY_WORDS + 8 * Z.of_nat 3) with (M_KEY_WORDS + 24) by lia. exact W3.
  - replace (M_KEY_WORDS + 8 * Z.of_nat 4) with (M_KEY_WORDS + 32) by lia. exact W4.
Qed.

(** ** Memory *)
Lemma krl_rd8 : forall m a v, cell8 m a v -> ov_read_bytes rsegs m (wa a) 8 = Some (le8 (Z_to_bv 64 v)).
Proof.
  intros m a v H. unfold cell8 in H.
  pose proof (bytes_at_ov_read rsegs m a _ 0 8 H) as R. rewrite length_le8 in R. specialize (R ltac:(lia)).
  cbn [Z.of_nat] in R. rewrite Z.add_0_r in R.
  change (skipn 0 (le8 (Z_to_bv 64 v))) with (le8 (Z_to_bv 64 v)) in R.
  rewrite firstn_all2 in R by (rewrite length_le8; lia).
  exact R.
Qed.

Lemma krl_rd4 : forall m a (w : word), bytes_at rsegs m a (le4 w) -> ov_read_bytes rsegs m (wa a) 4 = Some (le4 w).
Proof.
  intros m a w H.
  pose proof (bytes_at_ov_read rsegs m a _ 0 4 H) as R. rewrite length_le4 in R. specialize (R ltac:(lia)).
  cbn [Z.of_nat] in R. rewrite Z.add_0_r in R. change (skipn 0 (le4 w)) with (le4 w) in R.
  rewrite firstn_all2 in R by (rewrite length_le4; lia).
  exact R.
Qed.

Lemma krl_bat_sub : forall m a (l : list byte) k n, bytes_at rsegs m a l -> (k + n <= length l)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (firstn n (skipn k l)).
Proof.
  intros m a l k n H Hk.
  rewrite <- (firstn_skipn k l) in H. apply bytes_at_app in H as [_ H].
  rewrite <- (firstn_skipn n (skipn k l)) in H. apply bytes_at_app in H as [H _].
  rewrite firstn_length_le in H by lia. exact H.
Qed.

(** The bytes [o, o + len) of a C string. *)
Lemma krl_text : forall m a s o len, cstr_at rsegs m a s -> (o + len <= length s)%nat ->
  exists l, bytes_at rsegs m (a + Z.of_nat o) l /\ zs l = firstn len (skipn o s) /\ length l = len.
Proof.
  intros m a s o len (bs & sl & HB & HZ & _ & _) Hle. subst s. rewrite krl_zs_len in Hle.
  apply bytes_at_app in HB as [HB _].
  exists (firstn len (skipn o bs)). split; [apply krl_bat_sub; [exact HB | lia]|].
  split; [apply krl_zs_sub|]. rewrite firstn_length_le; [reflexivity|]. rewrite skipn_length. lia.
Qed.

Lemma krl_bytes_some : forall m a bs, bytes_at rsegs m a bs ->
  forall x, a <= x < a + Z.of_nat (length bs) -> exists b, mrd rsegs m (wa x) = Some b.
Proof.
  intros m a bs (Ha & Hl & H) x Hx. pose proof (H (Z.to_nat (x - a)) ltac:(lia)) as E.
  rewrite Z2Nat.id in E by lia. replace (a + (x - a)) with x in E by lia.
  destruct (nth_error bs (Z.to_nat (x - a))) as [b|] eqn:N; [exists b; exact E|].
  apply nth_error_None in N. lia.
Qed.

Lemma krl_outside_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[a b] W IH]; intros x; cbn [outside]; [left; exact I|].
  destruct (Z_le_dec a x) as [H1|H1]; destruct (Z_lt_dec x b) as [H2|H2]; destruct (IH x) as [H|H];
    first [ right; intros [H3 _]; apply H3; lia
          | right; intros [_ H3]; exact (H H3)
          | left; split; [lia | exact H] ].
Qed.

Lemma krl_not_out1 : forall a b x, ~ outside [(a, b)] x -> a <= x < b.
Proof.
  intros a b x H. cbn [outside] in H. destruct (Z_le_dec a x); destruct (Z_lt_dec x b);
    first [lia | exfalso; apply H; split; [lia | exact I]].
Qed.

Lemma krl_mrd_same : forall W m m' a, munch W m m' -> 0 <= a < 2^64 -> outside W a ->
  mrd rsegs m' (wa a) = mrd rsegs m (wa a).
Proof. intros W m m' a MU Ha HO. unfold mrd. rewrite MU; [reflexivity|]. rewrite wa_unsigned by lia. exact HO. Qed.

Lemma krl_disj_le : forall W a n n', disjoint_from W a n -> n' <= n -> disjoint_from W a n'.
Proof.
  induction W as [|[x y] W IH]; cbn [disjoint_from]; intros a n n' H Hle; [exact I|].
  destruct H as [H1 H2]. split; [lia | eapply IH; eassumption].
Qed.

Lemma krl_disj_sub : forall W a n a' n', disjoint_from W a n -> a <= a' -> a' + n' <= a + n ->
  disjoint_from W a' n'.
Proof.
  induction W as [|[x y] W IH]; cbn [disjoint_from]; intros a n a' n' H H1 H2; [exact I|].
  destruct H as [H3 H4]. split; [lia | eapply IH; eassumption].
Qed.

Lemma krl_saved_len : forall ws, length (concat (map le8 ws)) = (8 * length ws)%nat.
Proof.
  induction ws as [|w ws IH]; [reflexivity|]. cbn [map concat length]. rewrite app_length, length_le8, IH. lia.
Qed.

(** A C string and a block's slack keep through writes apart from the bytes a reader takes. *)
Lemma krl_cstr_tr : forall W m m' a s, cstr_at rsegs m a s -> munch W m m' ->
  disjoint_from W a (Z.of_nat (length s) + 8) -> cstr_at rsegs m' a s.
Proof.
  intros W m m' a s (bs & sl & HB & HZ & HN & HS) MU HD. unfold cstr_at.
  pose proof (Z.mod_pos_bound (- (a + Z.of_nat (length s) + 1)) 8 ltac:(lia)) as Q.
  set (q := (- (a + Z.of_nat (length s) + 1)) mod 8) in *. clearbody q.
  assert (Hj : (Z.to_nat q <= length sl)%nat) by lia.
  assert (HL : length (firstn (Z.to_nat q) sl) = Z.to_nat q) by (apply firstn_length_le; exact Hj).
  assert (Ls : length s = length bs) by (rewrite <- HZ; apply krl_zs_len).
  exists bs, (firstn (Z.to_nat q) sl). split.
  - eapply bytes_at_transport; [| exact MU |].
    + rewrite <- (firstn_skipn (Z.to_nat q) sl) in HB.
      replace (bs ++ ZERO :: firstn (Z.to_nat q) sl ++ skipn (Z.to_nat q) sl)
        with ((bs ++ ZERO :: firstn (Z.to_nat q) sl) ++ skipn (Z.to_nat q) sl) in HB
        by (rewrite <- app_assoc; reflexivity).
      apply bytes_at_app in HB as [HB _]. exact HB.
    + rewrite app_length. cbn [length]. rewrite HL. apply (krl_disj_le _ _ _ _ HD). lia.
  - split; [exact HZ|]. split; [exact HN|]. rewrite HL. lia.
Qed.

Lemma krl_slack_tr : forall W m m' a n, blk_slack rsegs m a n -> munch W m m' ->
  disjoint_from W (a + n) ((- (a + n)) mod 8) -> blk_slack rsegs m' a n.
Proof.
  intros W m m' a n (sl & HB & HS) MU HD. unfold blk_slack.
  pose proof (Z.mod_pos_bound (- (a + n)) 8 ltac:(lia)) as Q.
  set (q := (- (a + n)) mod 8) in *. clearbody q.
  assert (Hj : (Z.to_nat q <= length sl)%nat) by lia.
  assert (HL : length (firstn (Z.to_nat q) sl) = Z.to_nat q) by (apply firstn_length_le; exact Hj).
  exists (firstn (Z.to_nat q) sl). split.
  - eapply bytes_at_transport; [| exact MU |].
    + rewrite <- (firstn_skipn (Z.to_nat q) sl) in HB. apply bytes_at_app in HB as [HB _]. exact HB.
    + rewrite HL. rewrite Z2Nat.id by lia. exact HD.
  - rewrite HL. lia.
Qed.

Lemma krl_stack_some : forall m lo hi d, stack_ok rsegs m lo hi d ->
  forall x, lo <= x < hi -> exists b, m (wa x) = Some b.
Proof.
  intros m lo hi d ((_ & _ & S) & _ & _ & R) x Hx. destruct (S x Hx) as [_ (b & E)].
  unfold mrd in E. destruct (m (wa x)) as [b'|] eqn:M; [exists b'; reflexivity|].
  rewrite (R x Hx) in E. discriminate.
Qed.

(** task_mem keeps through writes into the stack region (whose bytes were already in m). *)
Lemma krl_task : forall W m m' lo hi d, MemNorm.task_mem rsegs m -> stack_ok rsegs m lo hi d -> munch W m m' ->
  (forall x, ~ outside W x -> lo <= x < hi) -> MemNorm.task_mem rsegs m'.
Proof.
  intros W m m' lo hi d T S MU HW a b E. destruct (krl_outside_dec W (bv_unsigned a)) as [O|O].
  - rewrite (MU a O) in E. exact (T a b E).
  - destruct (krl_stack_some m lo hi d S (bv_unsigned a) (HW _ O)) as (b' & E').
    unfold wa in E'. rewrite Z_to_bv_lit_self in E'. exact (T a b' E').
Qed.

Lemma krl_wr_stk : forall m lo hi a n, stk rsegs m lo hi -> lo <= a -> a + n <= hi -> 0 <= n -> wr_at rsegs m a n.
Proof.
  intros m lo hi a n (H1 & H2 & H) Ha Hn Hn0. split; [lia|]. split; [lia|].
  intros i Hi. apply (H (a + i)). lia.
Qed.

Lemma krl_stk_up : forall W m m' lo hi, stk rsegs m lo hi -> munch W m m' -> wmono rsegs m m' ->
  (forall x, lo <= x < hi -> ~ outside W x -> exists b, mrd rsegs m' (wa x) = Some b) -> stk rsegs m' lo hi.
Proof.
  intros W m m' lo hi (H1 & H2 & H) MU WM HW. split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as [Hw (b & Hb)]. split; [apply WM; exact Hw|].
  destruct (krl_outside_dec W a) as [O|O].
  - exists b. rewrite (krl_mrd_same W m m' a MU ltac:(lia) O). exact Hb.
  - exact (HW a Ha O).
Qed.

(** The loop facts keep through a callee that writes only [sp - d, sp) (ieq before KMODEL). *)
Lemma krl_loop_below : forall m m' fc sp0 sp lo c p mc cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 d,
  m_file_loop m fc sp0 sp lo c p mc cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 ->
  0 <= d -> lo <= sp - d ->
  munch [(sp - d, sp)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo sp0 ->
  m_file_loop m' fc sp0 sp lo c p mc cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
Proof.
  intros m m' fc sp0 sp lo c p mc cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 d
    (E0 & SV & C8 & C10 & C18 & C20 & C28 & C30 & Hc0 & Hc16 & NI & MC & WR & SL & AC & CU & HK & HL0 & HL1 &
     HR1 & HO1 & Hp0 & NIp & CS & AP & APc & PE & CI & WI & SO & MI0)
    Hd Hlo MU WM MI ST.
  pose proof SO as ((Hlo0 & Hhi0 & _) & Hdep & H16 & HRO).
  unfold M_FILE_FRAME in E0.
  assert (TR : forall A bs, sp <= A -> bytes_at rsegs m A bs -> bytes_at rsegs m' A bs)
    by (intros A bs HA HB; eapply bytes_at_transport; [exact HB | exact MU | cbn [disjoint_from]; split; [lia | exact I]]).
  destruct PE as (FRM & TM & (G1 & g & G2) & IMG & S63).
  change (sa_img_end SA) with 0x54088 in IMG.
  unfold m_file_loop, cell8, saved_at in *.
  split; [exact E0|].
  split; [apply TR; [unfold M_FILE_SAVE; lia | exact SV]|].
  split; [apply TR; [lia | exact C8]|]. split; [apply TR; [lia | exact C10]|].
  split; [apply TR; [lia | exact C18]|]. split; [apply TR; [lia | exact C20]|].
  split; [apply TR; [lia | exact C28]|]. split; [apply TR; [lia | exact C30]|].
  split; [exact Hc0|]. split; [exact Hc16|]. split; [exact NI|].
  split.
  { destruct MC as (bs & HB & HE). exists bs. split; [|exact HE].
    pose proof HE as HE'. unfold mconf_enc, mconf_encp in HE'. destruct HE' as (HLb & _).
    eapply bytes_at_transport; [exact HB | exact MU |]. cbn [disjoint_from]. split; [|exact I].
    unfold apart, SEG_M_SIZE in AC, HLb. lia. }
  split; [eapply wr_at_transport; [exact WR | exact WM]|].
  split.
  { eapply krl_slack_tr; [exact SL | exact MU |]. cbn [disjoint_from]. split; [|exact I].
    assert (Q : (- (c + SEG_M_SIZE)) mod 8 = 4) by (unfold SEG_M_SIZE; Z.div_mod_to_equations; lia).
    rewrite Q. unfold apart, SEG_M_SIZE in AC |- *. lia. }
  split; [exact AC|]. split; [exact CU|]. split; [exact HK|]. split; [exact HL0|]. split; [exact HL1|].
  split; [exact HR1|]. split; [exact HO1|]. split; [exact Hp0|]. split; [exact NIp|].
  split; [eapply krl_cstr_tr; [exact CS | exact MU | cbn [disjoint_from]; split; [|exact I]; unfold apart in AP; lia]|].
  split; [exact AP|]. split; [exact APc|].
  split.
  { split; [exact FRM|]. split.
    { eapply krl_task; [exact TM | exact SO | exact MU |]. intros x Hx. apply krl_not_out1 in Hx. lia. }
    split; [|split; [change (sa_img_end SA) with 0x54088; exact IMG | exact S63]].
    unfold ssp_ok. change (sa_got_guard SA) with 0x221b0 in *. change (sa_guard SA) with 0x53820 in *.
    split.
    - eapply bytes_at_transport; [exact G1 | exact MU |]. cbn [disjoint_from]. rewrite length_le8. split; [lia | exact I].
    - exists g. eapply bytes_at_transport; [exact G2 | exact MU |]. cbn [disjoint_from]. rewrite length_le8.
      split; [lia | exact I]. }
  split.
  { unfold cat_img in *. change (sa_catalogue SA) with 0x21468 in *. unfold CAT_BYTES in *.
    intros a Ha. rewrite (krl_mrd_same _ m m' a MU); [apply CI; exact Ha | lia |].
    cbn [outside]. split; [lia | exact I]. }
  split.
  { unfold words_img in *. unfold M_KEY_WORDS in *.
    intros a Ha. rewrite (krl_mrd_same _ m m' a MU); [apply WI; exact Ha | lia |].
    cbn [outside]. split; [lia | exact I]. }
  split; [|exact MI].
  split; [exact ST|]. exact (conj Hdep (conj H16 HRO)).
Qed.

(** The function's post from a later memory of the same cut. *)
Lemma krl_post_back : forall ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F m m' lo c k0 mf ms,
  mfu_post ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F m' lo c k0 mf ms ->
  munch (M_FILE_W (bv_unsigned sp0) c k0 mf) m m' -> wmono rsegs m m' ->
  mfu_post ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F m lo c k0 mf ms.
Proof.
  unfold mfu_post, ret_void_fp. intros ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F m m' lo c k0 mf ms
    (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F' & fc' & m'' &
     E & FR & FF & MU & WM & MI & TM & ST & Q) MU' WM'.
  exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, F', fc', m''.
  split; [exact E|]. split; [exact FR|]. split; [exact FF|].
  split; [eapply munch_trans; eassumption|]. split; [eapply wmono_trans; eassumption|].
  split; [exact MI|]. split; [exact TM|]. split; [exact ST | exact Q].
Qed.

Lemma krl_sx32 : forall z, 0 <= z < 2 ^ 31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. rewrite unsigned_lit by lia.
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31); lia). reflexivity.
Qed.

Lemma krl_W_upd : forall sp0 c k0 mcx i f pend, mfu_W sp0 c k0 (m_upd mcx i f) pend = mfu_W sp0 c k0 mcx pend.
Proof.
  intros. unfold mfu_W, M_FILE_W, m_upd, m_set_segs. cbn [mc_seg mc_kept]. rewrite upd_nth_length. reflexivity.
Qed.

(** role_set then role: the entry is ms_with_role with its old role_file. *)
Lemma krl_upd_role : forall mc gi r, (gi < length (mc_seg mc))%nat ->
  m_upd (m_upd mc gi (ms_set_role_set true)) gi (ms_set_role r) =
  m_upd mc gi (ms_with_role r (ms_role_file (nth gi (mc_seg mc) mseg_d))).
Proof.
  intros mc gi r H. unfold m_upd, m_set_segs. cbn [mc_seg mc_overflow mc_refused mc_kept mc_gen mc_reading].
  f_equal. revert gi H. generalize (mc_seg mc) as l.
  induction l as [|x l IH]; intros [|gi] H; cbn [length] in H; try lia.
  - reflexivity.
  - cbn [upd_nth nth]. f_equal. apply IH. lia.
Qed.

Lemma krl_len_upd : forall mc gi f, length (mc_seg (m_upd mc gi f)) = length (mc_seg mc).
Proof. intros. unfold m_upd, m_set_segs. cbn [mc_seg]. apply upd_nth_length. Qed.

(** ** The walk, from KDISP *)
Section Krole.
Hypothesis HIEQ : ieq_contract.
Hypothesis HFOLD : fold_contract.
Hypothesis HSTRLEN : strlen_contract.
Hypothesis HBCMP : bcmp_contract.
Hypothesis HSNP : snprintf_contract.
Hypothesis HREF : m_refuse_contract.
Variables (n : nat) (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (mcut : word -> option byte) (lo : Z)
  (ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word) (c p line : Z) (mc : mconf) (gi k0 : nat)
  (rest : list Z) (ok kl ov vl : nat) (k v : list Z).
Hypothesis HT : H_MF_TAIL n.
Hypothesis HKM : H_MFU_KMODEL n.
Hypothesis Hn : (length rest <= n)%nat.
Hypothesis Hr : rest <> [].
Hypothesis HL : m_file_loop mcut fc (bv_unsigned sp0) (bv_unsigned sp) lo c p mc (Some gi) line k0 rest
  ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
Hypothesis HCK : cell8 mcut (bv_unsigned sp + 0xa0) (p + Z.of_nat ok).
Hypothesis HCV : cell8 mcut (bv_unsigned sp + 0x90) (p + Z.of_nat ov).
Hypothesis HKV : mfu_kv rest ok kl ov vl k v.

Local Notation SP := (bv_unsigned sp).
Local Notation LOW := (h_fold v 64).
Local Notation POST := (mfu_post ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F mcut lo c k0
  (mf_fin (mk_disp mc gi k v (line + 1), Some gi) line rest)).
Local Notation KR0 := (Z_to_bv 64 c).
Local Notation KR2 := (Z_to_bv 64 (mf_next p rest)).
Local Notation KR3 := (Z_to_bv 64 (line + 1)).
Local Notation KR7 := (Z_to_bv 64 0x23).
Local Notation KR8 := (Z_to_bv 64 (c + MC_N)).
Local Notation KR9 := (Z_to_bv 64 BLANK_MASK).
Local Notation KR10 := (Z_to_bv 64 0x20).
Local Notation KR11 := (Z_to_bv 64 0x3b).

(** The facts of the cut the walk uses, out of m_file_loop. *)
Lemma kf : bv_unsigned sp0 = SP + 272 /\ lo + 6224 <= SP + 272 /\ 0 <= lo /\ SP + 272 <= 2^64 /\ 0x54088 <= lo /\
  SP + 272 < 2^63 /\ (SP + 272) mod 16 = 0 /\ 0 < c /\ c mod 16 = 0 /\ c + 9236 <= 2^64 /\
  apart c 9240 lo (SP + 272) /\ (gi < length (mc_seg mc))%nat /\ (length (mc_seg mc) <= 32)%nat /\
  0 <= line /\ line + Z.of_nat (length rest) <= 65535 /\ 0 < p /\ p + Z.of_nat (length rest) + 1 <= 2^64 /\
  apart p (Z.of_nat (length rest) + 8) lo (SP + 272) /\ frm0 fc /\ mem_inv rsegs mcut /\ ~ In 0 rest /\
  (forall a, lo <= a < SP + 272 -> seg_rom rsegs (wa a) = None).
Proof.
  pose proof HL as (E0 & SV & C8 & C10 & C18 & C20 & C28 & C30 & Hc0 & Hc16 & NI & MC & WR & SL & AC & CU & HK &
                    HL0 & HL1 & HR1 & HO1 & Hp0 & NIp & CS & AP & APc & PE & CI & WI & SO & MI0).
  unfold M_FILE_FRAME in E0.
  destruct SO as ((Hlo & Hhi & _) & Hdep & H16 & HRO).
  destruct PE as (FRM & _ & _ & Himg & H63).
  destruct MC as (bs & HB & HE). pose proof (bytes_at_bound _ _ _ _ HB) as BB.
  unfold mconf_enc, mconf_encp in HE. destruct HE as (HLb & Hn32 & _).
  destruct CS as (tb & sl & HT0 & HZ & HN & _). pose proof (bytes_at_bound _ _ _ _ HT0) as TB.
  assert (Lt : length tb = length rest) by (rewrite <- HZ; symmetry; apply krl_zs_len).
  rewrite app_length in TB. cbn [length] in TB. rewrite Lt in TB.
  cbn [cur_ok] in CU.
  unfold SEG_M_SIZE in *. unfold M_FILE_STACK, M_FILE_FRAME, PRINTF_K in Hdep.
  change (sa_img_end SA) with 0x54088 in Himg.
  rewrite <- E0 in Hhi, Hdep, H16, HRO, H63, AC, AP.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact H16|].
  split; [lia|]. split; [exact Hc16|]. split; [lia|].
  split; [unfold apart in *; lia|]. split; [exact CU|]. split; [exact Hn32|]. split; [lia|]. split; [lia|].
  split; [lia|]. split; [lia|]. split; [exact AP|]. split; [exact FRM|]. split; [exact MI0|]. split; [exact HN|].
  exact HRO.
Qed.

Lemma kf_kv : (ok + kl <= length rest)%nat /\ (ov + vl <= length rest)%nat.
Proof. destruct HKV as (H1 & H2 & _). pose proof (krl_line_le rest). lia. Qed.

Lemma kf_cs : cstr_at rsegs mcut p rest.
Proof. pose proof HL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CS & _). exact CS. Qed.

Lemma kf_mc : mconf_at rsegs mcut c mc.
Proof. pose proof HL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MC & _). exact MC. Qed.

Lemma kf_wr : wr_at rsegs mcut c SEG_M_SIZE.
Proof. pose proof HL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WR & _). exact WR. Qed.

Lemma kf_words : words_img mcut.
Proof.
  pose proof HL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                    _ & _ & _ & _ & WI & _). exact WI.
Qed.

Lemma kf_v : ~ In 0 v /\ Forall (fun x => 0 <= x < 256) v.
Proof.
  destruct kf_cs as (tb & sl & _ & HZ & HN & _). destruct HKV as (_ & _ & _ & Ev). split.
  - intros H. rewrite <- Ev in H. apply krl_in_firstn, krl_in_skipn in H. exact (HN H).
  - rewrite <- Ev, <- HZ. apply Forall_forall. intros x Hx. apply krl_in_firstn, krl_in_skipn in Hx.
    pose proof (krl_zs_range tb) as R. rewrite Forall_forall in R. exact (R x Hx).
Qed.

Lemma kf_low : Forall (fun x => 0 <= x < 256) (LOW ++ [0]) /\ (length LOW <= 63)%nat.
Proof.
  destruct kf_v as (NV & RV). pose proof (h_fold_props v 64 NV RV) as (_ & FR).
  split; [apply Forall_app; split; [exact FR | apply Forall_cons; [lia | apply Forall_nil]]|].
  rewrite h_fold_length. lia.
Qed.

(** The saved registers and the fixed frame cells. *)
Definition CELLS (m : word -> option byte) : Prop :=
  saved_at rsegs m (SP + M_FILE_SAVE) [e11; e10; e9; e8; e7; e6; e5; e4; e3; e2; e1; e0; ra0] /\
  cell8 m (SP + 0x8) (- 1 - c) /\ cell8 m (SP + 0x10) (c + MC_KNOCK) /\
  cell8 m (SP + 0x18) (- 1 - (c + MC_KNOCK)) /\ cell8 m (SP + 0x20) (c + MC_READING) /\
  cell8 m (SP + 0x28) (c + MC_N) /\ cell8 m (SP + 0x30) (cur_ptr c (Some gi)).

Lemma kf_cells : CELLS mcut.
Proof.
  pose proof HL as (_ & SV & C8 & C10 & C18 & C20 & C28 & C30 & _).
  exact (conj SV (conj C8 (conj C10 (conj C18 (conj C20 (conj C28 C30)))))).
Qed.

Lemma CELLS_tr : forall W m m', CELLS m -> munch W m m' -> disjoint_from W (SP + 8) 48 ->
  disjoint_from W (SP + 168) 104 -> CELLS m'.
Proof.
  intros W m m' (SV & C1 & C2 & C3 & C4 & C5 & C6) MU D1 D2.
  assert (T : forall a z, cell8 m a z -> SP + 8 <= a -> a + 8 <= SP + 56 -> cell8 m' a z).
  { intros a z H Ha1 Ha2. unfold cell8 in H |- *. eapply bytes_at_transport; [exact H | exact MU |].
    rewrite length_le8. eapply krl_disj_sub; [exact D1 | lia | lia]. }
  split; [unfold saved_at in *; eapply bytes_at_transport; [exact SV | exact MU | rewrite krl_saved_len; exact D2]|].
  split; [apply T; [exact C1 | lia | lia]|]. split; [apply T; [exact C2 | lia | lia]|].
  split; [apply T; [exact C3 | lia | lia]|]. split; [apply T; [exact C4 | lia | lia]|].
  split; [apply T; [exact C5 | lia | lia]|]. apply T; [exact C6 | lia | lia].
Qed.

(** The memory inside the role branch before the stores: ieq's frame and fold's low written since the cut. *)
Definition FM (m : word -> option byte) : Prop :=
  munch [(SP - 32, SP); (SP + 72, SP + 136)] mcut m /\ wmono rsegs mcut m /\ mem_inv rsegs m /\
  stk rsegs m lo (SP + 272) /\ bytes_at rsegs m (SP + 72) (zb (LOW ++ [0])).

Lemma FM_nil : forall m m', FM m -> munch [] m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> FM m'.
Proof.
  intros m m' (MU & WM & MI & ST & LB) MU' WM' MI'.
  split; [eapply munch_trans; [exact MU | eapply munch_weaken; [|exact MU']; intros x _; exact I]|].
  split; [eapply wmono_trans; eassumption|]. split; [exact MI'|].
  split; [eapply stk_transport_disjoint; [exact ST | exact MU' | exact WM' | exact I]|].
  eapply bytes_at_transport; [exact LB | exact MU' | exact I].
Qed.

Lemma FM_mid : forall m, FM m -> mfu_mid mcut m (bv_unsigned sp0) lo c k0 mc false.
Proof.
  intros m (MU & WM & MI & ST & _).
  pose proof kf as (Esp0 & Hst & Hlo0 & Hhi & Himg & H63 & H16 & Hc0 & Hc16 & Hce & Hca & _).
  destruct kf_mc as (bs & HB & HE).
  pose proof HE as HE'. unfold mconf_enc, mconf_encp in HE'. destruct HE' as (HLb & _). unfold SEG_M_SIZE in HLb.
  unfold apart in Hca.
  split; [|split; [exact WM|split; [exact MI|split; [rewrite Esp0; exact ST|]]]].
  - eapply munch_weaken; [|exact MU]. unfold sub_fp, mfu_W, M_FILE_W. intros x Hx. cbn [app outside] in Hx |- *.
    destruct Hx as (H1 & _). rewrite Esp0 in H1. unfold M_FILE_STACK, M_FILE_FRAME, PRINTF_K in H1.
    split; [lia|split; [lia|exact I]].
  - exists bs. split; [|exact HE]. eapply bytes_at_transport; [exact HB | exact MU |].
    cbn [disjoint_from]. rewrite HLb. split; [lia|split; [lia|exact I]].
Qed.

Lemma FM_cells : forall m, FM m -> CELLS m.
Proof.
  intros m (MU & _). apply (CELLS_tr _ mcut m kf_cells MU).
  - cbn [disjoint_from]. split; [lia | split; [lia | exact I]].
  - cbn [disjoint_from]. split; [lia | split; [lia | exact I]].
Qed.

Lemma FM_words : forall m, FM m -> words_img m.
Proof.
  intros m (MU & _). pose proof kf_words as WI.
  pose proof kf as (_ & Hst & _ & _ & Himg & _).
  unfold words_img in *. unfold M_KEY_WORDS in *. intros a Ha.
  rewrite (krl_mrd_same _ mcut m a MU); [apply WI; exact Ha | lia |].
  cbn [outside]. split; [lia | split; [lia | exact I]].
Qed.

Lemma FM_wr : forall m, FM m -> wr_at rsegs m c SEG_M_SIZE.
Proof. intros m (_ & WM & _). eapply wr_at_transport; [exact kf_wr | exact WM]. Qed.

(** mk_disp's two outcomes after the role word. *)
Lemma kd_hit : forall r, ieq k S_role = true -> h_role_word LOW = Some r ->
  mk_disp mc gi k v (line + 1) = m_upd mc gi (ms_with_role r (snprintf_s 96 F_s [AS (mc_reading mc)])).
Proof. intros r H1 H2. unfold mk_disp. rewrite H1, H2. reflexivity. Qed.

Lemma kd_miss : ieq k S_role = true -> h_role_word LOW = None -> mk_disp mc gi k v (line + 1) = m_refuse mc (line + 1) false.
Proof. intros H1 H2. unfold mk_disp. rewrite H1, H2. reflexivity. Qed.

(** A 4-byte store into entry gi of the block. *)
Lemma blk_store : forall m mcx mcx' a (w : word),
  mfu_mid mcut m (bv_unsigned sp0) lo c k0 mcx false -> wr_at rsegs m c SEG_M_SIZE -> CELLS m ->
  mfu_W (bv_unsigned sp0) c k0 mcx' false = mfu_W (bv_unsigned sp0) c k0 mcx false ->
  inside (mfu_W (bv_unsigned sp0) c k0 mcx false) a 4 -> c <= a -> a + 4 <= c + SEG_M_SIZE ->
  (forall bs, mconf_encp false mcx bs -> mconf_encp false mcx' (upd_bytes bs (Z.to_nat (a - c)) (le4 w))) ->
  mfu_mid mcut (write_to_mem m (wa a) (le4 w)) (bv_unsigned sp0) lo c k0 mcx' false /\
  wr_at rsegs (write_to_mem m (wa a) (le4 w)) c SEG_M_SIZE /\ CELLS (write_to_mem m (wa a) (le4 w)) /\
  store_ok rsegs m (wa a) 4 = true.
Proof.
  intros m mcx mcx' a w (MU & WM & MI & ST & MA) WR CL EW IN Ha1 Ha2 ENC.
  pose proof kf as (Esp0 & Hst & Hlo0 & Hhi & Himg & H63 & H16 & Hc0 & Hc16 & Hce & Hca & _).
  unfold SEG_M_SIZE in Ha2. unfold apart in Hca.
  assert (HS : store_ok rsegs m (wa a) 4 = true).
  { replace a with (c + (a - c)) by lia. apply (wr_at_store_ok rsegs m c SEG_M_SIZE (a - c) 4 WR); unfold SEG_M_SIZE; lia. }
  split; [|split; [|split; [|exact HS]]].
  - split; [rewrite EW; apply munch_write; [exact MU | lia | rewrite length_le4; lia | rewrite length_le4; exact IN]|].
    split; [apply wmono_write; exact WM|].
    split; [apply mem_inv_store; [exact MI | rewrite length_le4; exact HS]|].
    split; [apply stk_write; [exact ST | lia | rewrite length_le4; lia]|].
    apply (mconf_atp_store rsegs false false m c mcx mcx' a (le4 w));
      [exact MA | exact Ha1 | rewrite length_le4; unfold SEG_M_SIZE; lia | exact ENC].
  - apply wr_at_write. exact WR.
  - assert (MW : munch [(a, a + 4)] m (write_to_mem m (wa a) (le4 w))).
    { apply munch_write; [apply munch_refl | lia | rewrite length_le4; lia | rewrite length_le4; cbn [inside]; left; lia]. }
    apply (CELLS_tr _ _ _ CL MW); (cbn [disjoint_from]; split; [lia | exact I]).
Qed.

(** ** The miss after five words: m_refuse(c, line + 1), s8 and s6 back, s4 = 1, the tail. *)
Lemma miss : forall m (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 t3 t4 t5 t6 : word),
  FM m -> h_role_word LOW = None -> ieq k S_role = true ->
  evt rsegs POST
    (MS (mkR ra sp gp tp t0 t1 t2 KR0 s1 a0 a1 a2 a3 a4 a5 a6 a7 KR2 KR3 s4 s5 s6 KR7 s8 KR9 KR10 KR11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14650) fc None m (seg_rom rsegs)).
Proof.
  intros m ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 t3 t4 t5 t6 FMm Hrw Hieq.
  rewrite (kd_miss Hieq Hrw).
  pose proof kf as (Esp0 & Hst & Hlo0 & Hhi & Himg & H63 & H16 & Hc0 & Hc16 & Hce & Hca & Hgi & Hn32 & Hl0 & Hl1 &
                    Hp0 & Hpe & Hpa & FRM & MI0 & HN0 & HRO).
  pose proof (FM_cells m FMm) as CL. pose proof (FM_mid m FMm) as MID.
  step. step. step.
  eapply (mfu_refuse HREF) with (mcut := mcut) (fcc := fc) (mc0 := mc) (cur := Some gi) (line := line) (k0 := k0)
    (rest := rest) (ra0 := ra0) (sp0 := sp0) (e0 := e0) (e1 := e1) (e2 := e2) (e3 := e3) (e4 := e4) (e5 := e5)
    (e6 := e6) (e7 := e7) (e8 := e8) (e9 := e9) (e10 := e10) (e11 := e11) (c := c) (p := p) (lo := lo) (mc := mc)
    (pend := false).
  - exact HL.
  - exact Hr.
  - exact MID.
  - apply mf_grows_refl.
  - reflexivity.
  - exact FRM.
  - rewrite unsigned_lit by lia. reflexivity.
  - rewrite unsigned_lit by lia. reflexivity.
  - intros m' F' fc' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' MID' MU' WM' FR' FF'.
    rewrite ret_pc_even by (try lia; reflexivity).
    assert (CL' : CELLS m').
    { unfold apart in Hca. apply (CELLS_tr _ _ _ CL MU');
        unfold m_refuse_W, kept_addr, MC_KEPT, MC_KEPT_LEN, MC_NKEPT, MC_REFUSED, M_REFUSE_STACK, PRINTF_K;
        destruct (Z.of_nat (length (mc_kept mc)) <? 8) eqn:EK; cbn [app disjoint_from];
        try apply Z.ltb_lt in EK; repeat split; try exact I; lia. }
    pose proof CL' as (SV' & C08 & C10 & C18 & C20 & C28 & C30).
    pose proof (krl_rd8 _ _ _ C28) as R28.
    step. step. step. step. step.
    eapply (mfu_tail n) with (Fc := F) (fcc := fc) (mcut := mcut) (lo := lo) (ra0 := ra0) (sp0 := sp0) (e0 := e0)
      (e1 := e1) (e2 := e2) (e3 := e3) (e4 := e4) (e5 := e5) (e6 := e6) (e7 := e7) (e8 := e8) (e9 := e9) (e10 := e10)
      (e11 := e11) (c := c) (p := p) (line := line) (mc := mc) (cur := Some gi) (k0 := k0) (rest := rest)
      (mc' := m_refuse mc (line + 1) false) (cur' := Some gi).
    + exact HT.
    + exact Hn.
    + exact Hr.
    + exact HL.
    + exact MID'.
    + exact SV'.
    + exact C08.
    + exact C10.
    + exact C18.
    + exact C20.
    + exact C28.
    + exact C30.
    + apply m_refuse_grows.
    + cbn [cur_ok]. destruct (m_refuse_sizes mc (line + 1) false) as [E _]. rewrite E. exact Hgi.
    + cbn [m_refuse mc_refused]. lia.
    + cbn [m_refuse mc_overflow]. lia.
    + exact FR'.
    + exact FF'.
    + unfold m_file_regs. repeat (split; [reflexivity|]). reflexivity.
Qed.

(** ** A word matched at 0x14730: role = i, role_set and role stored, role_file = reading, the tail. *)
Lemma hit : forall i m (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 t3 t4 t5 t6 w1 w4 w8 : word),
  (i < 5)%nat -> FM m -> h_role_word LOW = Some (Z.of_nat i) -> ieq k S_role = true ->
  w1 = Z_to_bv 64 (-4 * Z.of_nat i) -> w4 = Z_to_bv 64 (M_KEY_ROLE + 4 * Z.of_nat i) ->
  evt rsegs POST
    (MS (mkR ra sp gp tp t0 t1 t2 KR0 w1 a0 a1 a2 a3 a4 a5 a6 a7 KR2 KR3 w4 s5 s6 KR7 w8 KR9 KR10 KR11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14730) fc None m (seg_rom rsegs)).
Proof.
  intros i m ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 t3 t4 t5 t6 w1 w4 w8 Hi FMm Hrw Hieq E1 E4. subst w1 w4.
  rewrite (kd_hit (Z.of_nat i) Hieq Hrw).
  pose proof kf as (Esp0 & Hst & Hlo0 & Hhi & Himg & H63 & H16 & Hc0 & Hc16 & Hce & Hca & Hgi & Hn32 & Hl0 & Hl1 &
                    Hp0 & Hpe & Hpa & FRM & MI0 & HN0 & HRO).
  pose proof (FM_cells m FMm) as CL. pose proof (FM_mid m FMm) as MID. pose proof (FM_wr m FMm) as WR.
  pose proof FMm as (MU & WM & MI & ST & LB).
  pose proof CL as (_ & _ & _ & _ & _ & C28 & C30).
  pose proof (krl_rd8 _ _ _ C28) as R28. pose proof (krl_rd8 _ _ _ C30) as R30.
  cbn [cur_ptr] in R30. unfold mseg_addr, MSEG_SIZE in R30.
  pose proof (krl_rd4 m _ _ (mfu_roles m MI i Hi)) as RR.
  unfold M_KEY_ROLE in RR |- *.
  step. step. step. step. step. step.
  step. if_cases K; [exfalso; zify_cond K; Z.div_mod_to_equations; lia|clear K].
  step. step.
  step. if_cases K; [exfalso; zify_cond K; zb_masks; Z.div_mod_to_equations; lia|clear K].
  step. rewrite (krl_sx32 (Z.of_nat i)) by lia.
  step. step.
  clear R28 R30 RR.
  (* g->role_set = 1 *)
  assert (INS1 : inside (mfu_W (bv_unsigned sp0) c k0 mc false) (c + 256 * Z.of_nat gi + 20) 4).
  { unfold mfu_W, M_FILE_W. cbn [app inside]. right. left. unfold mseg_addr, MSEG_SIZE. lia. }
  assert (ENC1 : forall bs, mconf_encp false mc bs ->
    mconf_encp false (m_upd mc gi (ms_set_role_set true))
      (upd_bytes bs (Z.to_nat (c + 256 * Z.of_nat gi + 20 - c)) (le4 (Z_to_bv 64 1)))).
  { intros bs HE. replace (Z.to_nat (c + 256 * Z.of_nat gi + 20 - c)) with (256 * gi + Z.to_nat MS_ROLE_SET)%nat
      by (unfold MS_ROLE_SET; lia).
    apply mconf_enc_seg; [exact HE | exact Hgi | rewrite length_le4; unfold MS_ROLE_SET; lia |].
    intros fb Hfb. exact (mseg_enc_role_set _ fb true Hfb). }
  destruct (blk_store m mc (m_upd mc gi (ms_set_role_set true)) (c + 256 * Z.of_nat gi + 20) (Z_to_bv 64 1)
              MID WR CL (krl_W_upd _ _ _ _ _ _ _) INS1 ltac:(lia) ltac:(unfold SEG_M_SIZE; lia) ENC1)
    as (MID1 & WR1 & CL1 & HS1).
  step.
  change (Z_to_bv 64 (c + 256 * Z.of_nat gi + 20)) with (wa (c + 256 * Z.of_nat gi + 20)).
  set (m1 := write_to_mem m (wa (c + 256 * Z.of_nat gi + 20)) (le4 (Z_to_bv 64 1))) in *. clearbody m1.
  (* g->role = i *)
  assert (INS2 : inside (mfu_W (bv_unsigned sp0) c k0 (m_upd mc gi (ms_set_role_set true)) false)
                   (c + 256 * Z.of_nat gi + 16) 4).
  { rewrite krl_W_upd. unfold mfu_W, M_FILE_W. cbn [app inside]. right. left. unfold mseg_addr, MSEG_SIZE. lia. }
  assert (ENC2 : forall bs, mconf_encp false (m_upd mc gi (ms_set_role_set true)) bs ->
    mconf_encp false (m_upd (m_upd mc gi (ms_set_role_set true)) gi (ms_set_role (Z.of_nat i)))
      (upd_bytes bs (Z.to_nat (c + 256 * Z.of_nat gi + 16 - c)) (le4 (Z_to_bv 64 (Z.of_nat i))))).
  { intros bs HE. replace (Z.to_nat (c + 256 * Z.of_nat gi + 16 - c)) with (256 * gi + Z.to_nat MS_ROLE)%nat
      by (unfold MS_ROLE; lia).
    apply mconf_enc_seg; [exact HE | rewrite krl_len_upd; exact Hgi | rewrite length_le4; unfold MS_ROLE; lia |].
    intros fb Hfb. apply mseg_enc_role; [exact Hfb | lia]. }
  destruct (blk_store m1 (m_upd mc gi (ms_set_role_set true))
              (m_upd (m_upd mc gi (ms_set_role_set true)) gi (ms_set_role (Z.of_nat i)))
              (c + 256 * Z.of_nat gi + 16) (Z_to_bv 64 (Z.of_nat i))
              MID1 WR1 CL1 (krl_W_upd _ _ _ _ _ _ _) INS2 ltac:(lia) ltac:(unfold SEG_M_SIZE; lia) ENC2)
    as (MID2 & WR2 & CL2 & HS2).
  step.
  change (Z_to_bv 64 (c + 256 * Z.of_nat gi + 16)) with (wa (c + 256 * Z.of_nat gi + 16)).
  set (m2 := write_to_mem m1 (wa (c + 256 * Z.of_nat gi + 16)) (le4 (Z_to_bv 64 (Z.of_nat i)))) in *. clearbody m2.
  rewrite (krl_upd_role mc gi (Z.of_nat i) Hgi) in MID2.
  (* snprintf(g->role_file, 96, "%s", c->reading) *)
  pose proof CL2 as (_ & _ & _ & _ & C20 & _ & _). pose proof (krl_rd8 _ _ _ C20) as R20.
  step. step. step. step. step. step. step.
  clear R20.
  eapply (mfu_snprintf_file HSNP) with (mcut := mcut) (fcc := fc) (mc0 := mc) (cur := Some gi) (line := line)
    (k0 := k0) (rest := rest) (ra0 := ra0) (sp0 := sp0) (e0 := e0) (e1 := e1) (e2 := e2) (e3 := e3) (e4 := e4)
    (e5 := e5) (e6 := e6) (e7 := e7) (e8 := e8) (e9 := e9) (e10 := e10) (e11 := e11) (c := c) (p := p) (lo := lo)
    (mcx := mc) (i := gi) (off := MS_ROLE_FILE) (upd := ms_with_role (Z.of_nat i))
    (f0 := ms_role_file (nth gi (mc_seg mc) mseg_d)).
  - exact HL.
  - exact MID2.
  - left. split; [reflexivity|]. exists (Z.of_nat i). intros f. reflexivity.
  - exact Hgi.
  - exact FRM.
  - rewrite unsigned_lit by lia. unfold mseg_addr, MSEG_SIZE, MS_ROLE_FILE. lia.
  - rewrite unsigned_lit by lia. reflexivity.
  - rewrite unsigned_lit by lia. reflexivity.
  - rewrite unsigned_lit by (unfold MC_READING; lia). reflexivity.
  - intros m3 F' fc' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' MID3 MU3 WM3 FR3 FF3.
    rewrite ret_pc_even by (try lia; reflexivity).
    assert (CL3 : CELLS m3).
    { unfold apart in Hca. apply (CELLS_tr _ _ _ CL2 MU3);
        unfold mseg_addr, MSEG_SIZE, MS_ROLE_FILE, PRINTF_K; cbn [disjoint_from]; repeat split; try exact I; lia. }
    pose proof CL3 as (SV3 & D08 & D10 & D18 & D20 & D28 & D30).
    step.
    eapply (mfu_tail n) with (Fc := F) (fcc := fc) (mcut := mcut) (lo := lo) (ra0 := ra0) (sp0 := sp0) (e0 := e0)
      (e1 := e1) (e2 := e2) (e3 := e3) (e4 := e4) (e5 := e5) (e6 := e6) (e7 := e7) (e8 := e8) (e9 := e9) (e10 := e10)
      (e11 := e11) (c := c) (p := p) (line := line) (mc := mc) (cur := Some gi) (k0 := k0) (rest := rest)
      (mc' := m_upd mc gi (ms_with_role (Z.of_nat i) (snprintf_s 96 F_s [AS (mc_reading mc)])))
      (cur' := Some gi).
    + exact HT.
    + exact Hn.
    + exact Hr.
    + exact HL.
    + exact MID3.
    + exact SV3.
    + exact D08.
    + exact D10.
    + exact D18.
    + exact D20.
    + exact D28.
    + exact D30.
    + apply m_upd_grows.
    + cbn [cur_ok]. rewrite krl_len_upd. exact Hgi.
    + cbn [m_upd m_set_segs mc_refused]. lia.
    + cbn [m_upd m_set_segs mc_overflow]. lia.
    + exact FR3.
    + exact FF3.
    + unfold m_file_regs. repeat (split; [reflexivity|]). reflexivity.
Qed.

(** ** The words loop 0x14618, word i (j words left). *)
Lemma wloop : forall j i m (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 t3 t4 t5 t6 w1 w4 w5 w8 : word),
  (i + j = 5)%nat -> (0 < j)%nat -> FM m -> ieq k S_role = true ->
  word_go (skipn i KRL_WORDS) LOW (Z.of_nat i) = h_role_word LOW ->
  w1 = Z_to_bv 64 (-4 * Z.of_nat i) -> w4 = Z_to_bv 64 (M_KEY_ROLE + 4 * Z.of_nat i) ->
  w5 = Z_to_bv 64 (Z.of_nat (length LOW)) -> w8 = Z_to_bv 64 (M_KEY_WORDS + 8 * Z.of_nat i) ->
  evt rsegs POST
    (MS (mkR ra sp gp tp t0 t1 t2 KR0 w1 a0 a1 a2 a3 a4 a5 a6 a7 KR2 KR3 w4 w5 s6 KR7 w8 KR9 KR10 KR11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14618) fc None m (seg_rom rsegs)).
Proof.
  induction j as [|j IH]; intros i m ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 t3 t4 t5 t6 w1 w4 w5 w8
    Hij Hj FMm Hieq Hinv E1 E4 E5 E8; [lia|]. subst w1 w4 w5 w8.
  assert (Hi : (i < 5)%nat) by lia.
  pose proof kf as (Esp0 & Hst & Hlo0 & Hhi & Himg & H63 & H16 & Hc0 & Hc16 & Hce & Hca & Hgi & Hn32 & Hl0 & Hl1 &
                    Hp0 & Hpe & Hpa & FRM & MI0 & HN0 & HRO).
  pose proof kf_low as (LOWR & LL).
  (* the miss of word i, from 0x1463c: the next word, or m_refuse after the fifth *)
  assert (NEXT : forall m' (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s6' t3' t4' t5' t6' : word),
    FM m' -> word_go (skipn (S i) KRL_WORDS) LOW (Z.of_nat (S i)) = h_role_word LOW ->
    evt rsegs POST
      (MS (mkR ra' sp gp tp t0' t1' t2' KR0 (Z_to_bv 64 (-4 * Z.of_nat i)) a0' a1' a2' a3' a4' a5' a6' a7' KR2 KR3
               (Z_to_bv 64 (M_KEY_ROLE + 4 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length LOW))) s6' KR7
               (Z_to_bv 64 (M_KEY_WORDS + 8 * Z.of_nat i)) KR9 KR10 KR11 t3' t4' t5' t6')
          F (Z_to_bv 64 0x1463c) fc None m' (seg_rom rsegs))).
  { intros m' ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s6' t3' t4' t5' t6' FM' Hinv'.
    step. step. step. step. step.
    if_cases K.
    - assert (Hj' : (0 < j)%nat) by (zify_cond K; Z.div_mod_to_equations; lia).
      eapply (IH (S i)); [lia | exact Hj' | exact FM' | exact Hieq | exact Hinv' | f_equal; lia | f_equal; lia |
                          reflexivity | f_equal; lia].
    - assert (Hi4 : i = 4%nat) by (zify_cond K; Z.div_mod_to_equations; lia). subst i.
      eapply miss; [exact FM' | | exact Hieq]. rewrite <- Hinv'. reflexivity. }
  pose proof FMm as (MU & WM & MI & ST & LB).
  pose proof (krl_words_cell m (FM_words m FMm) i Hi) as WC. apply krl_rd8 in WC.
  destruct (krl_words_cstr m MI i Hi) as (bsw & slw & HBW & HZW & HNW & HSW).
  pose proof (bytes_at_bound _ _ _ _ HBW) as BW. rewrite app_length in BW. cbn [length] in BW.
  assert (LW : length bsw = length (nth i KRL_WORDS [])) by (rewrite <- HZW; symmetry; apply krl_zs_len).
  pose proof (krl_words_len i Hi) as LW6.
  step. step. step.
  clear WC.
  eapply evt_cut.
  { eapply HSTRLEN with (str := bsw) (slack := slw).
    - rewrite unsigned_lit by lia. exact HBW.
    - apply krl_zs_nonul. rewrite HZW. exact HNW.
    - rewrite unsigned_lit by lia. rewrite LW. exact HSW.
    - exact MI. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> &
              MU1 & WM1 & MI1 & HB1).
  rewrite ret_pc_even by (try lia; reflexivity).
  pose proof (FM_nil m m1 FMm MU1 WM1 MI1) as FM1.
  step. if_cases K.
  - (* strlen <> ln: word i misses *)
    assert (Lne : length bsw <> length LOW) by (zify_cond K; lia).
    eapply NEXT; [exact FM1|]. rewrite <- Hinv. rewrite (krl_inv_miss i LOW (Z.of_nat i) Hi); [f_equal; lia|].
    apply andb_false_iff. left. apply Nat.eqb_neq. lia.
  - (* strlen = ln: bcmp *)
    assert (Leq : length bsw = length LOW) by (zify_cond K; lia).
    step. step. step. step.
    destruct (krl_memcmp (length LOW) (bsw ++ Z_to_bv 8 0 :: slw) (zb (LOW ++ [0]))) as (vv & EV & RV & IV).
    { rewrite app_length. cbn [length]. lia. }
    { unfold zb. rewrite length_map, app_length. cbn [length]. lia. }
    pose proof FM1 as (_ & _ & _ & _ & LB1).
    eapply evt_cut.
    { eapply HBCMP with (ls := bsw ++ Z_to_bv 8 0 :: slw) (rs := zb (LOW ++ [0])) (v := vv).
      - exact HB1.
      - rewrite unsigned_lit by lia. exact LB1.
      - rewrite unsigned_lit by lia. rewrite Nat2Z.id. exact EV.
      - exact MI1. }
    intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' &
                m2 & -> & MU2 & WM2 & MI2 & HB2 & HR2).
    rewrite ret_pc_even by (try lia; reflexivity).
    pose proof (FM_nil m1 m2 FM1 MU2 WM2 MI2) as FM2.
    assert (WEQ : nth i KRL_WORDS [] = LOW <-> vv = 0).
    { assert (W1 : firstn (length LOW) (zs (bsw ++ Z_to_bv 8 0 :: slw)) = zs bsw)
        by (rewrite krl_zs_app; apply krl_firstn_prefix; rewrite krl_zs_len; exact Leq).
      assert (W2 : firstn (length LOW) (zs (zb (LOW ++ [0]))) = LOW)
        by (rewrite (krl_zs_zb _ LOWR); apply krl_firstn_prefix; reflexivity).
      rewrite W1, W2, HZW in IV. split; intros H; [apply IV; exact H | apply IV in H; exact H]. }
    step. if_cases K2.
    + assert (V0 : vv = 0) by (zify_cond K2; Z.div_mod_to_equations; lia).
      eapply hit with (i := i); [exact Hi | exact FM2 | | exact Hieq | reflexivity | reflexivity].
      rewrite <- Hinv. apply krl_inv_hit; [exact Hi|]. apply krl_word_hit. apply WEQ. exact V0.
    + assert (V0 : vv <> 0) by (zify_cond K2; Z.div_mod_to_equations; lia).
      eapply NEXT; [exact FM2|]. rewrite <- Hinv. rewrite (krl_inv_miss i LOW (Z.of_nat i) Hi); [f_equal; lia|].
      apply not_true_iff_false. intros H. apply krl_word_hit in H. apply WEQ in H. contradiction.
Qed.

(** ** From KDISP: ieq "role", then KMODEL or fold and the words loop. *)
Lemma main : forall (ra t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 : word),
  evt rsegs POST
    (MS (mkR ra sp gp tp t0 t1 t2 KR0 s1 (Z_to_bv 64 (p + Z.of_nat ok)) a1 a2 a3 a4 a5 a6 a7 KR2 KR3 s4
             (Z_to_bv 64 (Z.of_nat vl)) (Z_to_bv 64 (Z.of_nat kl)) KR7 KR8 KR9 KR10 KR11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x145d8) fc None mcut (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6.
  pose proof kf as (Esp0 & Hst & Hlo0 & Hhi & Himg & H63 & H16 & Hc0 & Hc16 & Hce & Hca & Hgi & Hn32 & Hl0 & Hl1 &
                    Hp0 & Hpe & Hpa & FRM & MI0 & HN0 & HRO).
  pose proof kf_kv as (Hk1 & Hv1).
  pose proof HKV as (_ & _ & Ek & Ev).
  destruct (krl_text mcut p rest ok kl kf_cs ltac:(lia)) as (lk & HBk & Zk & Lk).
  destruct (krl_text mcut p rest ov vl kf_cs ltac:(lia)) as (lv & HBv & Zv & Lv).
  rewrite Ek in Zk. rewrite Ev in Zv.
  pose proof (mfu_lits mcut MI0) as (_ & LROLE & _).
  step. step. step. step.
  eapply (mfu_ieq HIEQ) with (mcut := mcut) (m := mcut) (fcc := fc) (mc0 := mc) (cur := Some gi) (line := line)
    (k0 := k0) (rest := rest) (ra0 := ra0) (sp0 := sp0) (e0 := e0) (e1 := e1) (e2 := e2) (e3 := e3) (e4 := e4)
    (e5 := e5) (e6 := e6) (e7 := e7) (e8 := e8) (e9 := e9) (e10 := e10) (e11 := e11) (c := c) (p := p) (lo := lo)
    (mc := mc) (pend := false) (l := lk) (w := S_role).
  - exact HL.
  - eapply mfu_mid_init. exact HL.
  - rewrite unsigned_lit by lia. lia.
  - rewrite unsigned_lit by lia. exact HBk.
  - rewrite unsigned_lit by lia. rewrite Lk. reflexivity.
  - rewrite unsigned_lit by lia. rewrite Lk. unfold apart in *. lia.
  - rewrite unsigned_lit by lia. lia.
  - rewrite unsigned_lit by lia. exact LROLE.
  - rewrite unsigned_lit by lia. unfold RO_LO. lia.
  - rewrite unsigned_lit by lia. change (sa_ro_end SA) with 0x1229c. change (length S_role) with 4%nat. lia.
  - intros m1 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' MID1 MU1 WM1.
    rewrite Zk. rewrite ret_pc_even by (try lia; reflexivity).
    unfold IEQ_STACK in MU1.
    pose proof MID1 as (_ & _ & MI1 & ST1 & _).
    destruct (ieq k S_role) eqn:Hieq; cbn [b2z].
    + (* "role": fold(v, vl, low, 64) *)
      step. if_false.
      assert (CV1 : cell8 m1 (SP + 0x90) (p + Z.of_nat ov)).
      { unfold cell8 in HCV |- *.
        eapply bytes_at_transport; [exact HCV | exact MU1 | cbn [disjoint_from]; split; [lia | exact I]]. }
      pose proof (krl_rd8 _ _ _ CV1) as RV.
      assert (HBv1 : bytes_at rsegs m1 (p + Z.of_nat ov) lv).
      { eapply bytes_at_transport; [exact HBv | exact MU1 |]. cbn [disjoint_from]. split; [|exact I].
        rewrite Lv. unfold apart in Hpa. lia. }
      assert (FO : fold_out lv 64 = LOW) by (unfold fold_out; rewrite Zv; reflexivity).
      pose proof kf_low as (LOWR & LL).
      step. step. step. step. step.
      clear RV.
      eapply evt_cut.
      { eapply HFOLD with (lo := lo) (l := lv). unfold fold_pre.
        rewrite (unsigned_lit (p + Z.of_nat ov)) by lia. rewrite (unsigned_lit (Z.of_nat vl)) by lia.
        rewrite (unsigned_lit (SP + 72)) by lia. change (bv_unsigned (Z_to_bv 64 64)) with 64. rewrite FO.
        split; [lia|]. split; [lia|]. split; [exact HBv1|]. split; [rewrite Lv; reflexivity|].
        split; [unfold apart in *; lia|].
        split; [eapply krl_wr_stk; [rewrite Esp0 in ST1; exact ST1 | lia | lia | lia]|].
        split; [unfold apart; lia|]. split; [unfold apart in *; lia|].
        split; [|exact MI1].
        split; [rewrite Esp0 in ST1; exact (proj1 (stk_split rsegs m1 lo SP (SP + 272) ST1 ltac:(lia)))|].
        split; [unfold FOLD_STACK; lia|]. split; [Z.div_mod_to_equations; lia|].
        intros a Ha. apply HRO. lia. }
      intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' &
                  m2 & -> & MU2 & WM2 & MI2 & ST2 & LB2).
      change (bv_unsigned (Z_to_bv 64 64)) with 64 in *. rewrite FO in *.
      rewrite (unsigned_lit (SP + 72)) in MU2, LB2 by lia.
      rewrite ret_pc_even by (try lia; reflexivity).
      assert (FM2 : FM m2).
      { split; [|split; [eapply wmono_trans; eassumption|split; [exact MI2|split; [|exact LB2]]]].
        - eapply munch_trans.
          + eapply munch_weaken; [|exact MU1]. unfold sub_fp. cbn [outside]. intros x (H1 & H2 & _).
            split; [exact H1 | exact I].
          + eapply munch_weaken; [|exact MU2]. unfold sub_fp. cbn [outside]. intros x (H1 & H2 & _).
            split; [|exact I]. lia.
        - rewrite Esp0 in ST1. eapply krl_stk_up; [exact ST1 | exact MU2 | exact WM2 |].
          intros x Hx HO. apply krl_not_out1 in HO. eapply krl_bytes_some; [exact LB2|].
          unfold zb. rewrite length_map, app_length. cbn [length]. lia. }
      step. step. step. step. step. step.
      eapply (wloop 5 0); [lia | lia | exact FM2 | exact Hieq | reflexivity | | | |];
        first [reflexivity | f_equal; lia | apply Z_to_bv_eqm; Z.div_mod_to_equations; lia].
    + (* KMODEL *)
      step. if_true.
      assert (HL1 : m_file_loop m1 fc (bv_unsigned sp0) SP lo c p mc (Some gi) line k0 rest
                      ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11).
      { eapply krl_loop_below with (d := 32); [exact HL | lia | lia | exact MU1 | exact WM1 | exact MI1 | exact ST1]. }
      pose proof HKM as HK'. unfold H_MFU_KMODEL, H_MFU_KAT in HK'.
      eapply evt_mono.
      * eapply HK' with (m := m1) (lo := lo) (ra0 := ra0) (sp0 := sp0) (e0 := e0) (e1 := e1) (e2 := e2)
          (e3 := e3) (e4 := e4) (e5 := e5) (e6 := e6) (e7 := e7) (e8 := e8) (e9 := e9) (e10 := e10) (e11 := e11)
          (c := c) (p := p) (line := line) (mc := mc) (gi := gi) (k0 := k0) (rest := rest) (ok := ok) (kl := kl)
          (ov := ov) (vl := vl) (k := k) (v := v).
        -- exact Hn.
        -- exact Hr.
        -- exact HL1.
        -- unfold mfu_lregs. repeat (split; [reflexivity|]). reflexivity.
        -- reflexivity.
        -- reflexivity.
        -- unfold cell8 in HCK |- *.
           eapply bytes_at_transport; [exact HCK | exact MU1 | cbn [disjoint_from]; split; [lia | exact I]].
        -- unfold cell8 in HCV |- *.
           eapply bytes_at_transport; [exact HCV | exact MU1 | cbn [disjoint_from]; split; [lia | exact I]].
        -- intros E. exfalso. unfold MFU_PC_KMODEL, MFU_PC_KDISP in E. lia.
        -- exact HKV.
        -- constructor; [exact Hieq | constructor].
      * intros ms' HP. eapply krl_post_back; [exact HP | | exact WM1].
        eapply munch_weaken; [|exact MU1]. unfold sub_fp, M_FILE_W. intros x Hx. cbn [outside] in Hx |- *.
        destruct Hx as (H1 & _). rewrite Esp0 in H1. unfold M_FILE_STACK, M_FILE_FRAME, PRINTF_K in H1.
        split; [lia | exact I].
Qed.

End Krole.

Theorem mfu_krole_holds : ieq_contract -> fold_contract -> strlen_contract -> bcmp_contract -> snprintf_contract ->
  m_refuse_contract -> S_MFU_KROLE.
Proof.
  intros HIEQ HFOLD HSTRLEN HBCMP HSNP HREF n HT HKM.
  unfold H_MFU_KDISP, H_MFU_KAT.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 c p line mc gi k0 rest ok kl ov vl k v
    Hn Hr HL HR Hs6 Hs5 HCK HCV Ha0 HKV _.
  specialize (Ha0 eq_refl).
  destruct HR as (E0 & E2 & E3 & E7 & E8 & E9 & E10 & E11).
  subst s0 s2 s3 s7 s8 s9 s10 s11 s6 s5 a0.
  eapply main; eassumption.
Qed.
