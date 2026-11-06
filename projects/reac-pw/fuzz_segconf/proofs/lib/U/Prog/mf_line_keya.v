(** m_file (UBSan build, image 1696d6c34ffd, 0x14268): the sub-piece S_MFU_KEYA of S_MF_LINE (family F3; the cuts are
    in U/Prog/mfu_cuts.v, the shared lemmas in U/Prog/mfu_kit.v). From the cut KEY 0x14528 (m_key inlined,
    fuzz_segconf.c:197-211) to the cut KDISP 0x145d8, or through the refusal 0x1467c-0x14688 to the tail 0x146b4.
    - 0x14528-0x14530: eq = memchr(s, '=', e - s) on the stripped line sl = [p + i, p + j) (memchr_contract; it
      writes nothing).
    - 0x14534-0x1453c: the cursor cell 0x30(sp) NULL, or no '=', refuses: 0x1467c-0x14684 m_refuse(c, line + 1)
      (mfu_refuse), 0x14688 s4 = 1, the tail (mfu_tail) with (m_refuse mc (line + 1) false, cur) (mfp_facts
      m_key_refuse).
    - 0x14540-0x14558: k = s (0xa0), ke = eq (0x98), v = eq + 1 (0x90), ve = e (0x88), into the frame cells carved
      from the stack region; the trap 0x1454c (eq = -1) is dead (eq < p + |rest| < 2^64 - 1).
    - 0x14564 / 0x14570: strip on (0xa0, 0x98) and on (0x90, 0x88) (mfu_strip): k = h_strip (firstn ei sl) and
      the value h_strip (skipn (S ei) sl) as offsets of the text left (keya_hstrip).
    - 0x14574-0x145c4: the quote pair (keya_unq, from mfp_facts h_unquote_idx); the traps 0x14588 (v = 0),
      0x145a4 (ve < 2), 0x145b4 (v = -1) are dead.
    - 0x145c8-0x145d4: s6 = kl, s5 = vl; at 0x145d8 H_MFU_KDISP with m_key mc (Some gi) sl = mk_disp (mfp_facts
      m_key_disp); its post is relative to the memory there, which differs from the cut's only in the scratch
      cells [sp + 0x88, sp + 0xa8) (keya_post).
    Along the walk the memory differs from the cut's only in those cells (memchr writes nothing, strip only its two
    cells), so every fact of m_file_loop is carried from the cut (keya_loop). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP Tac ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec mfu_facts mfp_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import seg_env m_file_c mfu_cuts mfu_kit.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import m_refuse_c strip_c memchr_c.
Import ListNotations.
Open Scope Z_scope.

(** ** Lists, bytes and words (build-independent) *)
Lemma keya_find_memchr : forall c (bs : list byte), find_byte c bs = memchr (zs bs) c.
Proof.
  intros c bs. unfold zs. induction bs as [|b r IH]; cbn [find_byte memchr map]; [reflexivity|].
  rewrite IH. destruct (bv_unsigned b =? c); [reflexivity|]. destruct (memchr (map bv_unsigned r) c); reflexivity.
Qed.

Lemma keya_fs : forall (l : list Z) a b c d, (c + d <= b)%nat ->
  firstn d (skipn c (firstn b (skipn a l))) = firstn d (skipn (a + c) l).
Proof.
  intros l a b c d H. rewrite skipn_firstn_comm, firstn_firstn, skipn_skipn.
  replace (Nat.min d (b - c)) with d by lia. rewrite (Nat.add_comm c a). reflexivity.
Qed.

Lemma keya_sf : forall (l : list Z) a b c, skipn c (firstn b (skipn a l)) = firstn (b - c) (skipn (a + c) l).
Proof. intros l a b c. rewrite skipn_firstn_comm, skipn_skipn, (Nat.add_comm c a). reflexivity. Qed.

Lemma keya_ff : forall (l : list Z) a b, (a <= b)%nat -> firstn a (firstn b l) = firstn a l.
Proof. intros l a b H. rewrite firstn_firstn. f_equal. lia. Qed.

Lemma keya_nth_firstn : forall (l : list Z) k t, (t < k)%nat -> nth t (firstn k l) 0 = nth t l 0.
Proof.
  induction l as [|x r IH]; intros [|k] [|t] H; cbn; try lia; try reflexivity. apply IH. lia.
Qed.

Lemma keya_nth_skipn : forall (l : list Z) a t, nth t (skipn a l) 0 = nth (a + t) l 0.
Proof.
  induction l as [|x r IH]; intros [|a] t; cbn [skipn Nat.add]; try (destruct t; reflexivity).
  rewrite IH. reflexivity.
Qed.

Lemma keya_zs_firstn : forall k (l : list byte), zs (firstn k l) = firstn k (zs l).
Proof. intros k l. unfold zs. rewrite firstn_map. reflexivity. Qed.

Lemma keya_zs_skipn : forall k (l : list byte), zs (skipn k l) = skipn k (zs l).
Proof. intros k l. unfold zs. rewrite skipn_map. reflexivity. Qed.

Lemma keya_zs_len : forall (l : list byte), length (zs l) = length l.
Proof. intros l. unfold zs. apply length_map. Qed.

Lemma keya_zs_nth : forall (l : list byte) k, bv_unsigned (nth k l ZERO) = nth k (zs l) 0.
Proof. intros l k. unfold zs. rewrite <- (map_nth bv_unsigned l ZERO k). reflexivity. Qed.

Lemma keya_byte_range : forall (b : byte), 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. change (bv_modulus 8) with 256 in H. exact H. Qed.

Lemma keya_signed : forall x, 0 <= x < 2 ^ 63 -> bv_signed (Z_to_bv 64 x) = x.
Proof. intros x H. rewrite zb_signed, unsigned_lit by lia. destruct (Z.ltb_spec x (2 ^ 63)); lia. Qed.

Lemma keya_bat_sub : forall m a (l : list byte) k n, bytes_at rsegs m a l -> (k + n <= length l)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (firstn n (skipn k l)).
Proof.
  intros m a l k n H Hk.
  rewrite <- (firstn_skipn k l) in H. apply bytes_at_app in H as [_ H].
  rewrite <- (firstn_skipn n (skipn k l)) in H. apply bytes_at_app in H as [H _].
  rewrite firstn_length_le in H by lia. exact H.
Qed.

Lemma keya_bat_prefix : forall m a (l : list byte) n, bytes_at rsegs m a l -> (n <= length l)%nat ->
  bytes_at rsegs m a (firstn n l).
Proof.
  intros m a l n H Hn. pose proof (keya_bat_sub m a l 0 n H ltac:(lia)) as R.
  cbn [Z.of_nat skipn] in R. rewrite Z.add_0_r in R. exact R.
Qed.

Lemma keya_cell_read : forall m a v, cell8 m a v -> ov_read_bytes rsegs m (wa a) 8 = Some (le8 (Z_to_bv 64 v)).
Proof.
  intros m a v H. unfold cell8 in H.
  assert (L8 : length (le8 (Z_to_bv 64 v)) = 8%nat) by apply length_le8.
  pose proof (bytes_at_ov_read rsegs m a (le8 (Z_to_bv 64 v)) 0 8 H ltac:(lia)) as R.
  replace (a + Z.of_nat 0) with a in R by lia. rewrite skipn_O, firstn_all2 in R by lia. exact R.
Qed.

Lemma keya_byte_read : forall m a (l : list byte) k, bytes_at rsegs m a l -> (k < length l)%nat ->
  ov_read_bytes rsegs m (wa (a + Z.of_nat k)) 1 = Some [nth k l ZERO].
Proof.
  intros m a l k H Hk. rewrite (bytes_at_ov_read rsegs m a l k 1 H) by lia. f_equal.
  clear H. revert k Hk. induction l as [|x r IH]; intros [|k] Hk; cbn in Hk |- *; try lia; [reflexivity|].
  apply IH. lia.
Qed.

(** The four 8-byte scratch cells [S + 0x88, S + 0xa8) of m_file's frame. *)
Lemma keya_rc4 : forall m S (w0 w1 w2 w3 : word),
  rw_cells rsegs m (S + 136) [C8 w0; C8 w1; C8 w2; C8 w3] <->
  wr_at rsegs m (S + 136) 32 /\ bytes_at rsegs m (S + 136) (le8 w0) /\ bytes_at rsegs m (S + 144) (le8 w1) /\
  bytes_at rsegs m (S + 152) (le8 w2) /\ bytes_at rsegs m (S + 160) (le8 w3).
Proof.
  intros m S w0 w1 w2 w3. unfold rw_cells, cells_at.
  change (cells_bytes [C8 w0; C8 w1; C8 w2; C8 w3]) with (le8 w0 ++ le8 w1 ++ le8 w2 ++ le8 w3 ++ []).
  change (Z.of_nat (cells_size [C8 w0; C8 w1; C8 w2; C8 w3])) with 32.
  rewrite app_nil_r, !bytes_at_app, !length_le8.
  replace (S + 136 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) with (S + 160) by lia.
  replace (S + 136 + Z.of_nat 8 + Z.of_nat 8) with (S + 152) by lia.
  replace (S + 136 + Z.of_nat 8) with (S + 144) by lia.
  assert (WF : cells_wf [C8 w0; C8 w1; C8 w2; C8 w3]) by (cbn; tauto).
  tauto.
Qed.

(** The stripped bytes of a window [a, a + w) of l, as a window of l. *)
Lemma keya_hstrip : forall (l : list Z) a w, (a + w <= length l)%nat ->
  (strip_lead (firstn w (skipn a l)) + strip_trail (firstn w (skipn a l)) <= w)%nat /\
  h_strip (firstn w (skipn a l)) =
  firstn (w - strip_lead (firstn w (skipn a l)) - strip_trail (firstn w (skipn a l)))
         (skipn (a + strip_lead (firstn w (skipn a l))) l).
Proof.
  intros l a w H.
  assert (Lu : length (firstn w (skipn a l)) = w)
    by (rewrite firstn_length_le; [reflexivity | rewrite length_skipn; lia]).
  pose proof (strip_le (firstn w (skipn a l))) as S. rewrite Lu in S.
  split; [exact S|].
  rewrite <- strip_mid, Lu. apply keya_fs. lia.
Qed.

(** One pair of quotes on a window [X, X + w) of l (SegModel.h_unquote by mfp_facts' h_unquote_idx). *)
Lemma keya_unq : forall (l : list Z) X w, (X + w <= length l)%nat ->
  h_unquote (firstn w (skipn X l)) =
  if (2 <=? w)%nat && ((nth X l 0 =? 34) || (nth X l 0 =? 39)) && (nth (X + (w - 1)) l 0 =? nth X l 0)
  then firstn (w - 2) (skipn (X + 1) l) else firstn w (skipn X l).
Proof.
  intros l X w H. rewrite h_unquote_idx.
  assert (Lv : length (firstn w (skipn X l)) = w)
    by (rewrite firstn_length_le; [reflexivity | rewrite length_skipn; lia]).
  rewrite Lv. destruct w as [|w']; [reflexivity|].
  rewrite (keya_nth_firstn (skipn X l) (S w') 0) by lia.
  rewrite (keya_nth_firstn (skipn X l) (S w') (S w' - 1)) by lia.
  rewrite !keya_nth_skipn, Nat.add_0_r.
  match goal with |- (if ?b then _ else _) = (if ?b then _ else _) => destruct b eqn:EC end; [|reflexivity].
  apply andb_true_iff in EC as [[E2 _]%andb_true_iff _]. apply Nat.leb_le in E2.
  unfold slice. replace (S w' - 1 - 1)%nat with (S w' - 2)%nat by lia. apply keya_fs. lia.
Qed.

(** The 31 facts of m_file_loop, named. *)
Ltac kloop L :=
  destruct L as (L_sp & L_sv & L_c8 & L_c10 & L_c18 & L_c20 & L_c28 & L_c30 & L_c0 & L_c16 & L_cni & L_mca & L_wr &
                 L_sl & L_apc & L_cur & L_k0 & L_l0 & L_l1 & L_ref & L_ovf & L_p0 & L_pni & L_cs & L_app & L_appc &
                 L_pe & L_cat & L_wi & L_so & L_mi).

(** A branch condition on 64-bit words in the Z terms of the walk. *)
Ltac kcond K :=
  unfold bv_eqb, bv_ltu, bv_lts, bv_leu in K; fold_lit_ux_in K;
  repeat (rewrite unsigned_lit in K by lia); repeat (rewrite keya_signed in K by lia);
  zify_bool K.

Ltac kdis := cbn [disjoint_from]; rewrite ?length_le8; repeat split; lia.

(** ** The walk from KEY *)
Section KeyA.
Variables (n : nat) (ra gp tp : word) (F : bvmap 5 word) (fc : bv 32) (mcut : word -> option byte) (lo : Z)
  (ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word) (c p line : Z) (mc : mconf) (cur : option nat)
  (k0 : nat) (rest : list Z) (i j : nat) (Sp : Z) (bsr : list byte).
Hypothesis HMC : memchr_contract.
Hypothesis HSC : strip_contract.
Hypothesis HRC : m_refuse_contract.
Hypothesis HT : H_MF_TAIL n.
Hypothesis HKD : H_MFU_KDISP n.
Hypothesis Hlen : (length rest <= n)%nat.
Hypothesis Hne : rest <> [].
Hypothesis LOOP : m_file_loop mcut fc (bv_unsigned sp0) Sp lo c p mc cur line k0 rest
  ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
Hypothesis HSp : 0 <= Sp < 2 ^ 64.
Hypothesis Hij : (i < j)%nat.
Hypothesis Hj : (j <= length (mf_line rest))%nat.
Hypothesis Hsl : slice i j (mf_line rest) = h_strip (h_cut_comment (mf_line rest)).
(** The text left: its bytes (before the NUL) at p. *)
Hypothesis HBR : bytes_at rsegs mcut p bsr.
Hypothesis HZR : zs bsr = rest.
Hypothesis HPB : p + Z.of_nat (length rest) < 2 ^ 64.

Local Abbreviation SL := (h_strip (h_cut_comment (mf_line rest))).
Local Abbreviation KPOST mk cu := (mfu_post ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F mcut lo c k0
  (mf_fin (mk, cu) line rest)).
(** What the walk writes before KDISP: the scratch cells 0x88 .. 0xa8 of the frame. *)
Local Abbreviation FW := [(Sp + 136, Sp + 168)].

(** *** Facts of the cut *)
Lemma kf_sp0 : bv_unsigned sp0 = Sp + 272.
Proof. pose proof LOOP as L. unfold m_file_loop in L. kloop L. unfold M_FILE_FRAME in L_sp. lia. Qed.

Lemma kf_lo : 0 <= lo /\ lo + 5952 <= Sp /\ Sp + 272 < 2 ^ 63 /\ 344200 <= lo.
Proof.
  pose proof kf_sp0 as E0. pose proof LOOP as L. unfold m_file_loop in L. kloop L.
  destruct L_pe as (_ & _ & _ & HI & HS). destruct L_so as ((Hlo & _ & _) & HD & _ & _).
  unfold M_FILE_STACK, M_FILE_FRAME, PRINTF_K in HD. change (sa_img_end SA) with 344200 in HI. lia.
Qed.

Lemma kf_c : 0 < c /\ c mod 16 = 0 /\ c + 9236 <= 2 ^ 64 /\ (length (mc_seg mc) <= 32)%nat.
Proof.
  pose proof LOOP as L. unfold m_file_loop in L. kloop L.
  destruct L_mca as (bs & B & EN). pose proof (bytes_at_bound _ _ _ _ B) as BB.
  destruct EN as (LB & LS & _). unfold SEG_M_SIZE in LB. lia.
Qed.

Lemma kf_p : 0 < p /\ apart p (Z.of_nat (length rest) + 8) lo (bv_unsigned sp0).
Proof.
  pose proof LOOP as L. unfold m_file_loop in L. kloop L. pose proof (bytes_at_bound _ _ _ _ HBR) as BB.
  split; [lia | exact L_app].
Qed.

Lemma kf_apc : apart c (SEG_M_SIZE + 4) lo (bv_unsigned sp0).
Proof. pose proof LOOP as L. unfold m_file_loop in L. kloop L. exact L_apc. Qed.

Lemma kf_line : 0 <= line /\ line + Z.of_nat (length rest) <= 65535.
Proof. pose proof LOOP as L. unfold m_file_loop in L. kloop L. split; assumption. Qed.

Lemma kf_frm : frm0 fc.
Proof. pose proof LOOP as L. unfold m_file_loop in L. kloop L. exact (proj1 L_pe). Qed.

Lemma kf_cur : cur_ok mc cur.
Proof. pose proof LOOP as L. unfold m_file_loop in L. kloop L. exact L_cur. Qed.

Lemma kf_stk : stk rsegs mcut lo (bv_unsigned sp0).
Proof. pose proof LOOP as L. unfold m_file_loop in L. kloop L. exact (proj1 L_so). Qed.

Lemma kf_mi : mem_inv rsegs mcut.
Proof. pose proof LOOP as L. unfold m_file_loop in L. kloop L. exact L_mi. Qed.

Lemma kf_loopw : m_file_loop mcut fc (bv_unsigned sp0) (bv_unsigned (Z_to_bv 64 Sp)) lo c p mc cur line k0 rest
  ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
Proof. rewrite unsigned_lit by exact HSp. exact LOOP. Qed.

Lemma kf_len : (length (mf_line rest) <= length rest)%nat.
Proof.
  destruct (mf_line_rest rest) as [[E _]|[E _]].
  - assert (L : length rest = length (mf_line rest ++ NL :: mf_rest rest)) by (f_equal; exact E).
    rewrite length_app in L. cbn [length] in L. lia.
  - assert (L : length rest = length (mf_line rest)) by (f_equal; exact E). lia.
Qed.

Lemma kf_bsr : length bsr = length rest.
Proof. rewrite <- HZR. symmetry. apply keya_zs_len. Qed.

(** The stripped line as a window of the text left. *)
Lemma kf_SL : SL = firstn (j - i) (skipn i rest).
Proof. rewrite <- Hsl. rewrite mf_line_firstn by lia. f_equal. lia. Qed.

(** *** The memory along the walk *)
Lemma keya_kd : forall a len, (a + len <= Sp + 136 \/ Sp + 168 <= a) -> disjoint_from FW a len.
Proof. intros a len H. cbn [disjoint_from]. split; [lia | exact I]. Qed.

(** Every fact of m_file_loop is carried from the cut to a memory that differs only in the scratch cells. *)
Lemma keya_loop : forall m, munch FW mcut m -> wmono rsegs mcut m -> mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp0) ->
  m_file_loop m fc (bv_unsigned sp0) Sp lo c p mc cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
Proof.
  intros m MU WM MI ST.
  pose proof kf_sp0 as E0. pose proof kf_lo as (Hlo0 & Hlo1 & Hlo2 & Hlo3).
  assert (TR : forall a bs, bytes_at rsegs mcut a bs -> a + Z.of_nat (length bs) <= Sp + 136 \/ Sp + 168 <= a ->
                 bytes_at rsegs m a bs)
    by (intros a bs B H; eapply bytes_at_transport; [exact B | exact MU | apply keya_kd; exact H]).
  assert (TRo : forall a, 0 <= a < Sp + 136 -> mrd rsegs m (wa a) = mrd rsegs mcut (wa a)).
  { intros a Ha. unfold mrd. rewrite (MU (wa a)); [reflexivity|].
    rewrite wa_unsigned by lia. cbn [outside]. split; [lia | exact I]. }
  pose proof LOOP as L. unfold m_file_loop in L |- *. kloop L. unfold cell8 in *.
  split; [exact L_sp|].
  split; [unfold saved_at in *; apply TR; [exact L_sv | right; unfold M_FILE_SAVE; lia]|].
  split; [apply TR; [exact L_c8 | left; rewrite length_le8; lia]|].
  split; [apply TR; [exact L_c10 | left; rewrite length_le8; lia]|].
  split; [apply TR; [exact L_c18 | left; rewrite length_le8; lia]|].
  split; [apply TR; [exact L_c20 | left; rewrite length_le8; lia]|].
  split; [apply TR; [exact L_c28 | left; rewrite length_le8; lia]|].
  split; [apply TR; [exact L_c30 | left; rewrite length_le8; lia]|].
  split; [exact L_c0|]. split; [exact L_c16|]. split; [exact L_cni|].
  split.
  { destruct L_mca as (bs & B & EN). exists bs. split; [|exact EN].
    apply TR; [exact B|]. destruct EN as (LB & _). rewrite LB.
    unfold apart in L_apc. rewrite E0 in L_apc. unfold SEG_M_SIZE in *. lia. }
  split; [eapply wr_at_transport; [exact L_wr | exact WM]|].
  split.
  { destruct L_sl as (sl & B & Hm).
    assert (M4 : (- (c + SEG_M_SIZE)) mod 8 = 4).
    { unfold SEG_M_SIZE. symmetry. apply Z.mod_unique with (q := - (2 * (c / 16)) - 1155); [left; lia|].
      pose proof (Z.div_mod c 16 ltac:(lia)) as D. rewrite L_c16 in D. lia. }
    rewrite M4 in Hm. exists (firstn 4 sl).
    assert (L4 : length (firstn 4 sl) = 4%nat) by (apply firstn_length_le; lia).
    rewrite M4, L4. split; [|lia].
    apply TR; [apply keya_bat_prefix; [exact B | lia]|]. rewrite L4.
    unfold apart in L_apc. rewrite E0 in L_apc. unfold SEG_M_SIZE in *. lia. }
  split; [exact L_apc|]. split; [exact L_cur|]. split; [exact L_k0|]. split; [exact L_l0|].
  split; [exact L_l1|]. split; [exact L_ref|]. split; [exact L_ovf|]. split; [exact L_p0|].
  split; [exact L_pni|].
  split.
  { destruct L_cs as (bs & sk & B & Hz & Hn & Hm).
    assert (Lbs : length bs = length rest) by (rewrite <- Hz; symmetry; apply keya_zs_len).
    pose proof (Z.mod_pos_bound (- (p + Z.of_nat (length rest) + 1)) 8 ltac:(lia)) as MB.
    set (q := (- (p + Z.of_nat (length rest) + 1)) mod 8) in *.
    exists bs, (firstn (Z.to_nat q) sk).
    assert (Lq : length (firstn (Z.to_nat q) sk) = Z.to_nat q) by (apply firstn_length_le; lia).
    unfold apart in L_app. rewrite E0 in L_app.
    apply bytes_at_app in B as [B1 B2]. change (ZERO :: sk) with ([ZERO] ++ sk) in B2.
    apply bytes_at_app in B2 as [B2 B3].
    split; [|split; [exact Hz | split; [exact Hn | rewrite Lq; lia]]].
    apply bytes_at_app. split; [apply TR; [exact B1 | rewrite Lbs; lia]|].
    change (ZERO :: firstn (Z.to_nat q) sk) with ([ZERO] ++ firstn (Z.to_nat q) sk).
    apply bytes_at_app. split; [apply TR; [exact B2 | cbn [length]; rewrite Lbs; lia]|].
    apply TR; [apply keya_bat_prefix; [exact B3 | lia]|]. rewrite Lq. cbn [length]. rewrite Lbs. lia. }
  split; [exact L_app|]. split; [exact L_appc|].
  split.
  { unfold printf_env, ssp_ok in *. destruct L_pe as (FR & TM & SS & HI & HS).
    split; [exact FR|]. split.
    - intros x b Hx.
      destruct (Z_lt_le_dec (bv_unsigned x) (Sp + 136)) as [Hx1|Hx1].
      { rewrite (MU x) in Hx by (cbn [outside]; split; [lia | exact I]). exact (TM x b Hx). }
      destruct (Z_lt_le_dec (bv_unsigned x) (Sp + 168)) as [Hx2|Hx2].
      2: { rewrite (MU x) in Hx by (cbn [outside]; split; [lia | exact I]). exact (TM x b Hx). }
      destruct L_so as ((_ & _ & STa) & _).
      destruct (STa (bv_unsigned x) ltac:(lia)) as [Wv _].
      unfold wa in Wv. rewrite Z_to_bv_bv_unsigned in Wv. unfold wview in Wv. revert Wv.
      destruct (mcut x) as [b0|] eqn:Eb; intros Wv; [exact (TM x b0 Eb)|].
      left. revert Wv. destruct (find_segment rsegs (bv_unsigned x) 1) as [s|] eqn:Ef; intros Wv.
      + discriminate.
      + exfalso. apply Wv. reflexivity.
    - split; [|split; [exact HI | exact HS]].
      destruct SS as (G1 & g & G2). split.
      + apply TR; [exact G1|]. rewrite length_le8. left. change (sa_got_guard SA) with 139696. lia.
      + exists g. apply TR; [exact G2|]. rewrite length_le8. left. change (sa_guard SA) with 342048. lia. }
  split.
  { intros a Ha. rewrite TRo by (change (sa_catalogue SA) with 136296 in Ha; unfold CAT_BYTES in Ha; lia).
    exact (L_cat a Ha). }
  split.
  { intros a Ha. rewrite TRo by (unfold M_KEY_WORDS in Ha; lia). exact (L_wi a Ha). }
  split; [destruct L_so as (_ & D1 & D2 & D3); exact (conj ST (conj D1 (conj D2 D3)))|].
  exact MI.
Qed.

Lemma keya_mid : forall m, munch FW mcut m -> wmono rsegs mcut m -> mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp0) -> mfu_mid mcut m (bv_unsigned sp0) lo c k0 mc false.
Proof.
  intros m MU WM MI ST. pose proof (keya_loop m MU WM MI ST) as L. pose proof kf_sp0 as E0.
  unfold m_file_loop in L. kloop L.
  unfold mfu_mid. refine (conj _ (conj WM (conj MI (conj ST L_mca)))).
  eapply munch_weaken; [|exact MU]. intros x Hx. unfold mfu_W, M_FILE_W in Hx. cbn [app outside] in Hx.
  destruct Hx as [Hx _]. cbn [outside]. split; [|exact I].
  unfold M_FILE_STACK, M_FILE_FRAME, PRINTF_K in Hx. lia.
Qed.

Lemma keya_text : forall m, munch FW mcut m -> bytes_at rsegs m p bsr.
Proof.
  intros m MU. pose proof kf_sp0 as E0. pose proof kf_lo as (_ & Hlo1 & _ & _). pose proof kf_p as (_ & AP).
  eapply bytes_at_transport; [exact HBR | exact MU | apply keya_kd]. rewrite kf_bsr.
  unfold apart in AP. lia.
Qed.

Lemma keya_c30 : forall m, munch FW mcut m ->
  ov_read_bytes rsegs m (wa (Sp + 48)) 8 = Some (le8 (Z_to_bv 64 (cur_ptr c cur))).
Proof.
  intros m MU. apply keya_cell_read. pose proof LOOP as L. unfold m_file_loop in L. kloop L. unfold cell8 in *.
  eapply bytes_at_transport; [exact L_c30 | exact MU | apply keya_kd]. rewrite length_le8. lia.
Qed.

(** The post of a later cut, relative to its memory, is the post from the KEY cut's memory. *)
Lemma keya_post : forall m mf ms, munch FW mcut m -> wmono rsegs mcut m ->
  mfu_post ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F m lo c k0 mf ms ->
  mfu_post ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F mcut lo c k0 mf ms.
Proof.
  intros m mf ms MU WM H. pose proof kf_sp0 as E0. unfold mfu_post, ret_void_fp in *.
  destruct H as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & F' & fc' & m' &
                 EQ & FR & HF & MU' & WM' & R).
  exists y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, F', fc', m'.
  refine (conj EQ (conj FR (conj HF (conj _ (conj _ R))))).
  - eapply munch_trans; [|exact MU']. eapply munch_weaken; [|exact MU].
    intros x Hx. unfold M_FILE_W in Hx. cbn [outside] in Hx. destruct Hx as [Hx _]. cbn [outside].
    split; [|exact I]. unfold M_FILE_STACK, M_FILE_FRAME, PRINTF_K in Hx. lia.
  - eapply wmono_trans; eassumption.
Qed.

(** m_refuse's writes miss the frame of m_file above its sp. *)
Lemma keya_rW_disj : forall a len, Sp <= a -> a + len <= Sp + 272 -> 0 <= len ->
  disjoint_from (m_refuse_W Sp c mc) a len.
Proof.
  intros a len H1 H2 H3.
  pose proof kf_c as (Hc0 & _ & Hc1 & _). pose proof kf_apc as AP. pose proof kf_sp0 as E0.
  pose proof kf_lo as (_ & Hlo1 & _ & _).
  unfold apart, SEG_M_SIZE in AP. rewrite E0 in AP.
  unfold m_refuse_W, kept_addr, MC_KEPT, MC_KEPT_LEN, MC_NKEPT, MC_REFUSED, M_REFUSE_STACK, PRINTF_K.
  destruct (Z.ltb_spec (Z.of_nat (length (mc_kept mc))) 8) as [Hk|Hk]; cbn [app disjoint_from]; repeat split; lia.
Qed.

Lemma keya_mres :
  memchr_res (bv_unsigned (Z_to_bv 64 (p + Z.of_nat i))) (bv_unsigned (Z_to_bv 64 61) mod 256)
    (bv_unsigned (Z_to_bv 64 (Z.of_nat (j - i)))) (firstn (j - i) (skipn i bsr)) =
  match memchr SL EQ with Some e => p + Z.of_nat i + Z.of_nat e | None => 0 end.
Proof.
  pose proof kf_p as (Hp0 & _). pose proof kf_len as HL. pose proof kf_bsr as Lb.
  rewrite !unsigned_lit by lia. change (61 mod 256) with 61. unfold memchr_res.
  rewrite firstn_all2 by (rewrite firstn_length_le; [lia | rewrite length_skipn; lia]).
  rewrite keya_find_memchr, keya_zs_firstn, keya_zs_skipn, HZR, <- kf_SL. reflexivity.
Qed.

(** *** The refusal 0x1467c-0x14688 and the tail *)
Lemma keya_refuse : forall m1 (ra' t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 t3 t4 t5 t6 : word),
  munch FW mcut m1 -> wmono rsegs mcut m1 -> mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp0) ->
  evt rsegs (KPOST (m_refuse mc (line + 1) false) cur)
    (MS (mkR ra' (Z_to_bv 64 Sp) gp tp t0 t1 t2 (Z_to_bv 64 c) s1 a0 a1 a2 a3 a4 a5 a6 a7
           (Z_to_bv 64 (mf_next p rest)) (Z_to_bv 64 (line + 1)) s4 s5 (Z_to_bv 64 0x1ff) (Z_to_bv 64 0x23)
           (Z_to_bv 64 (c + MC_N)) (Z_to_bv 64 BLANK_MASK) (Z_to_bv 64 0x20) (Z_to_bv 64 0x3b) t3 t4 t5 t6)
        F (Z_to_bv 64 0x1467c) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 ra' t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 t3 t4 t5 t6 MU WM MI ST.
  pose proof (keya_loop m1 MU WM MI ST) as L1. pose proof (keya_mid m1 MU WM MI ST) as MID.
  pose proof kf_c as (Hc0 & _ & Hc1 & _). pose proof kf_line as (Hl0 & Hl1). pose proof kf_frm as FRM.
  pose proof kf_loopw as LOOPw.
  step. step. step.
  eapply (mfu_refuse HRC); [exact LOOPw | exact Hne | exact MID | apply mf_grows_refl | reflexivity | exact FRM
                            | apply unsigned_lit; lia | apply unsigned_lit; lia | ].
  intros m' F' fc' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 MID' MUr WMr FRM' HF'.
  rewrite (ret_pc_even 0x14688) by (first [lia | reflexivity]).
  rewrite unsigned_lit in MUr by exact HSp.
  unfold m_file_loop in L1. kloop L1. unfold cell8 in *. unfold saved_at in L_sv.
  assert (TR : forall a bs, bytes_at rsegs m1 a bs -> Sp <= a -> a + Z.of_nat (length bs) <= Sp + 272 ->
                 bytes_at rsegs m' a bs)
    by (intros a bs B H1 H2; eapply bytes_at_transport; [exact B | exact MUr | apply keya_rW_disj; lia]).
  assert (LS : length (concat (map le8 [e11; e10; e9; e8; e7; e6; e5; e4; e3; e2; e1; e0; ra0])) = 104%nat)
    by (cbn [map concat]; rewrite ?length_app, ?length_le8; reflexivity).
  step. step.
  eapply (mfu_tail n) with (fcc := fc) (p := p) (mc := mc) (cur := cur).
  1: exact HT.
  1: exact Hlen.
  1: exact Hne.
  1: exact LOOPw.
  1: exact MID'.
  1: rewrite unsigned_lit by exact HSp; unfold saved_at; apply TR; [exact L_sv | unfold M_FILE_SAVE; lia |];
     rewrite LS; unfold M_FILE_SAVE; lia.
  1-6: unfold cell8; rewrite unsigned_lit by exact HSp; apply TR; [eassumption | lia | rewrite length_le8; lia].
  1: apply m_refuse_grows.
  1: pose proof kf_cur as CO; unfold cur_ok in CO |- *; exact CO.
  1: unfold m_refuse; cbn; lia.
  1: unfold m_refuse; cbn; lia.
  1: exact FRM'.
  1: exact HF'.
  unfold m_file_regs. repeat split.
Qed.

(** *** 0x145c8-0x145d4 and the cut KDISP *)
Lemma keya_kdisp : forall m gi e (ok kl ov vl : nat)
    (ra' t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 t3 t4 t5 t6 w88 w90 w98 wa0 : word),
  cur = Some gi -> memchr SL EQ = Some e ->
  firstn kl (skipn ok rest) = h_strip (firstn e SL) -> (ok + kl <= length (mf_line rest))%nat ->
  firstn vl (skipn ov rest) = h_unquote (h_strip (skipn (S e) SL)) -> (ov + vl <= length (mf_line rest))%nat ->
  munch FW mcut m -> wmono rsegs mcut m -> mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp0) ->
  rw_cells rsegs m (Sp + 136) [C8 w88; C8 w90; C8 w98; C8 wa0] ->
  w90 = Z_to_bv 64 (p + Z.of_nat ov) -> w98 = Z_to_bv 64 (p + Z.of_nat ok + Z.of_nat kl) ->
  wa0 = Z_to_bv 64 (p + Z.of_nat ok) ->
  a1 = Z_to_bv 64 (p + Z.of_nat ov + Z.of_nat vl) -> a2 = Z_to_bv 64 (p + Z.of_nat ov) ->
  evt rsegs (KPOST (m_key mc cur SL (line + 1)) cur)
    (MS (mkR ra' (Z_to_bv 64 Sp) gp tp t0 t1 t2 (Z_to_bv 64 c) s1 a0 a1 a2 a3 a4 a5 a6 a7
           (Z_to_bv 64 (mf_next p rest)) (Z_to_bv 64 (line + 1)) s4 s5 s6 (Z_to_bv 64 0x23)
           (Z_to_bv 64 (c + MC_N)) (Z_to_bv 64 BLANK_MASK) (Z_to_bv 64 0x20) (Z_to_bv 64 0x3b) t3 t4 t5 t6)
        F (Z_to_bv 64 0x145c8) fc None m (seg_rom rsegs)).
Proof.
  intros m gi e ok kl ov vl ra' t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 t3 t4 t5 t6 w88 w90 w98 wa0
    Ec Em Hk Hkb Hv Hvb MU WM MI ST RC E90 E98 Ea0 Ea1 Ea2.
  subst w90 w98 wa0 a1 a2.
  pose proof kf_p as (Hp0 & _). pose proof kf_len as HL. pose proof HPB as Hpb.
  pose proof (proj1 (keya_rc4 _ _ _ _ _ _) RC) as (_ & _ & C90 & _ & Ca0).
  step. step. step. step.
  rewrite Ec, (m_key_disp mc gi SL (line + 1) e Em).
  unfold H_MFU_KDISP, H_MFU_KAT in HKD.
  eapply evt_mono.
  { eapply HKD with (gi := gi) (ok := ok) (kl := kl) (ov := ov) (vl := vl) (k := h_strip (firstn e SL))
      (v := h_unquote (h_strip (skipn (S e) SL))) (rest := rest) (p := p) (c := c) (line := line) (mc := mc)
      (k0 := k0) (lo := lo) (ra0 := ra0) (sp0 := sp0) (e0 := e0) (e1 := e1) (e2 := e2) (e3 := e3) (e4 := e4)
      (e5 := e5) (e6 := e6) (e7 := e7) (e8 := e8) (e9 := e9) (e10 := e10) (e11 := e11) (F := F) (fc := fc) (m := m).
    1: exact Hlen.
    1: exact Hne.
    1: rewrite unsigned_lit by exact HSp; rewrite <- Ec; apply keya_loop; assumption.
    1: unfold mfu_lregs; repeat split.
    1-2: rewrite !unsigned_lit by lia; f_equal; lia.
    1: rewrite unsigned_lit by exact HSp; exact Ca0.
    1: rewrite unsigned_lit by exact HSp; exact C90.
    1: intros _; reflexivity.
    1: unfold mfu_kv; exact (conj Hkb (conj Hvb (conj Hk Hv))).
    constructor. }
  intros ms' H. exact (keya_post m _ ms' MU WM H).
Qed.

(** *** The quote pair 0x14574-0x145c4 *)
(** 0x145a0: the first byte of the value is a quote, w >= 2. *)
Lemma keya_q2 : forall m gi e (ok kl X w : nat)
    (ra' t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 t3 t4 t5 t6 w88 w90 w98 wa0 : word),
  cur = Some gi -> memchr SL EQ = Some e ->
  firstn kl (skipn ok rest) = h_strip (firstn e SL) -> (ok + kl <= length (mf_line rest))%nat ->
  firstn w (skipn X rest) = h_strip (skipn (S e) SL) -> (X + w <= length (mf_line rest))%nat -> (2 <= w)%nat ->
  (nth X rest 0 = 34 \/ nth X rest 0 = 39) ->
  munch FW mcut m -> wmono rsegs mcut m -> mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp0) ->
  rw_cells rsegs m (Sp + 136) [C8 w88; C8 w90; C8 w98; C8 wa0] ->
  w88 = Z_to_bv 64 (p + Z.of_nat X + Z.of_nat w) -> w90 = Z_to_bv 64 (p + Z.of_nat X) ->
  w98 = Z_to_bv 64 (p + Z.of_nat ok + Z.of_nat kl) -> wa0 = Z_to_bv 64 (p + Z.of_nat ok) ->
  a0 = Z_to_bv 64 (nth X rest 0) -> a1 = Z_to_bv 64 (p + Z.of_nat X + Z.of_nat w) -> a2 = Z_to_bv 64 (p + Z.of_nat X) ->
  evt rsegs (KPOST (m_key mc cur SL (line + 1)) cur)
    (MS (mkR ra' (Z_to_bv 64 Sp) gp tp t0 t1 t2 (Z_to_bv 64 c) s1 a0 a1 a2 a3 a4 a5 a6 a7
           (Z_to_bv 64 (mf_next p rest)) (Z_to_bv 64 (line + 1)) s4 s5 s6 (Z_to_bv 64 0x23)
           (Z_to_bv 64 (c + MC_N)) (Z_to_bv 64 BLANK_MASK) (Z_to_bv 64 0x20) (Z_to_bv 64 0x3b) t3 t4 t5 t6)
        F (Z_to_bv 64 0x145a0) fc None m (seg_rom rsegs)).
Proof.
  intros m gi e ok kl X w ra' t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 t3 t4 t5 t6 w88 w90 w98 wa0
    Ec Em Hk Hkb Hw Hwb Kw Hq MU WM MI ST RC E88 E90 E98 Ea0 Eq0 Eq1 Eq2.
  subst w88 w90 w98 wa0 a0 a1 a2.
  pose proof kf_p as (Hp0 & _). pose proof kf_len as HL. pose proof HPB as Hpb. pose proof kf_bsr as Lb.
  assert (Hq0 : 0 <= nth X rest 0 < 256) by (destruct Hq as [E|E]; rewrite E; lia).
  assert (Hql : 0 <= nth (X + (w - 1)) rest 0 < 256)
    by (rewrite <- HZR, <- keya_zs_nth; apply keya_byte_range).
  assert (R2 : ov_read_bytes rsegs m (wa (p + Z.of_nat (X + (w - 1)))) 1 = Some [nth (X + (w - 1)) bsr ZERO])
    by (apply keya_byte_read; [exact (keya_text m MU) | lia]).
  step. step. if_cases K4; [exfalso; kcond K4; lia|].
  step.
  assert (Eql : zxb (nth (X + (w - 1)) bsr ZERO) = Z_to_bv 64 (nth (X + (w - 1)) rest 0))
    by (unfold zxb; f_equal; rewrite keya_zs_nth, HZR; reflexivity).
  rewrite Eql. clear R2 Eql.
  step. if_cases K5.
  - kcond K5.
    eapply (keya_kdisp _ gi e ok kl X w).
    1: exact Ec.
    1: exact Em.
    1: exact Hk.
    1: exact Hkb.
    1: rewrite <- Hw, keya_unq by lia;
       replace ((2 <=? w)%nat) with true by (symmetry; apply Nat.leb_le; lia);
       replace ((nth X rest 0 =? 34) || (nth X rest 0 =? 39)) with true
         by (destruct Hq as [E|E]; rewrite E; reflexivity);
       replace (nth (X + (w - 1)) rest 0 =? nth X rest 0) with false by (symmetry; apply Z.eqb_neq; lia);
       reflexivity.
    1: exact Hwb.
    1-5: eassumption.
    all: first [reflexivity | f_equal; lia].
  - kcond K5.
    step. step. if_cases K6; [exfalso; kcond K6; lia|].
    step. step. step. step.
    eapply (keya_kdisp _ gi e ok kl (X + 1) (w - 2)).
    1: exact Ec.
    1: exact Em.
    1: exact Hk.
    1: exact Hkb.
    1: rewrite <- Hw, keya_unq by lia;
       replace ((2 <=? w)%nat) with true by (symmetry; apply Nat.leb_le; lia);
       replace ((nth X rest 0 =? 34) || (nth X rest 0 =? 39)) with true
         by (destruct Hq as [E|E]; rewrite E; reflexivity);
       replace (nth (X + (w - 1)) rest 0 =? nth X rest 0) with true by (symmetry; apply Z.eqb_eq; lia);
       reflexivity.
    1: lia.
    1-5: eassumption.
    all: first [reflexivity | f_equal; lia].
Qed.

(** 0x14574: the value [X, X + w) and the key [ok, ok + kl) in the cells. *)
Lemma keya_quote : forall m gi e (ok kl X w : nat)
    (ra' t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 t3 t4 t5 t6 w88 w90 w98 wa0 : word),
  cur = Some gi -> memchr SL EQ = Some e ->
  firstn kl (skipn ok rest) = h_strip (firstn e SL) -> (ok + kl <= length (mf_line rest))%nat ->
  firstn w (skipn X rest) = h_strip (skipn (S e) SL) -> (X + w <= length (mf_line rest))%nat ->
  munch FW mcut m -> wmono rsegs mcut m -> mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp0) ->
  rw_cells rsegs m (Sp + 136) [C8 w88; C8 w90; C8 w98; C8 wa0] ->
  w88 = Z_to_bv 64 (p + Z.of_nat X + Z.of_nat w) -> w90 = Z_to_bv 64 (p + Z.of_nat X) ->
  w98 = Z_to_bv 64 (p + Z.of_nat ok + Z.of_nat kl) -> wa0 = Z_to_bv 64 (p + Z.of_nat ok) ->
  evt rsegs (KPOST (m_key mc cur SL (line + 1)) cur)
    (MS (mkR ra' (Z_to_bv 64 Sp) gp tp t0 t1 t2 (Z_to_bv 64 c) s1 a0 a1 a2 a3 a4 a5 a6 a7
           (Z_to_bv 64 (mf_next p rest)) (Z_to_bv 64 (line + 1)) s4 s5 s6 (Z_to_bv 64 0x23)
           (Z_to_bv 64 (c + MC_N)) (Z_to_bv 64 BLANK_MASK) (Z_to_bv 64 0x20) (Z_to_bv 64 0x3b) t3 t4 t5 t6)
        F (Z_to_bv 64 0x14574) fc None m (seg_rom rsegs)).
Proof.
  intros m gi e ok kl X w ra' t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 t3 t4 t5 t6 w88 w90 w98 wa0
    Ec Em Hk Hkb Hw Hwb MU WM MI ST RC E88 E90 E98 Ea0.
  subst w88 w90 w98 wa0.
  pose proof kf_p as (Hp0 & _). pose proof kf_len as HL. pose proof HPB as Hpb. pose proof kf_bsr as Lb.
  pose proof kf_line as (Hl0 & Hl1).
  step. step. step. step. step.
  if_cases K.
  - kcond K.
    eapply (keya_kdisp _ gi e ok kl X w).
    1: exact Ec.
    1: exact Em.
    1: exact Hk.
    1: exact Hkb.
    1: rewrite <- Hw, keya_unq by lia;
       replace ((2 <=? w)%nat) with false by (symmetry; apply Nat.leb_gt; lia); reflexivity.
    1: exact Hwb.
    1-5: eassumption.
    all: first [reflexivity | f_equal; lia].
  - kcond K.
    step. if_cases K1; [exfalso; kcond K1; lia|].
    assert (R1 : ov_read_bytes rsegs m (wa (p + Z.of_nat X)) 1 = Some [nth X bsr ZERO])
      by (apply keya_byte_read; [exact (keya_text m MU) | lia]).
    step.
    assert (Eq0 : zxb (nth X bsr ZERO) = Z_to_bv 64 (nth X rest 0))
      by (unfold zxb; f_equal; rewrite keya_zs_nth, HZR; reflexivity).
    rewrite Eq0. clear R1 Eq0.
    assert (Hq : 0 <= nth X rest 0 < 256) by (rewrite <- HZR, <- keya_zs_nth; apply keya_byte_range).
    step. step. if_cases K2.
    + kcond K2.
      eapply (keya_q2 _ gi e ok kl X w); try eassumption; try lia; try reflexivity.
    + kcond K2. step. step. if_cases K3.
      * kcond K3.
        eapply (keya_kdisp _ gi e ok kl X w).
        1: exact Ec.
        1: exact Em.
        1: exact Hk.
        1: exact Hkb.
        1: rewrite <- Hw, keya_unq by lia;
           replace ((2 <=? w)%nat) with true by (symmetry; apply Nat.leb_le; lia);
           replace (nth X rest 0 =? 34) with false by (symmetry; apply Z.eqb_neq; lia);
           replace (nth X rest 0 =? 39) with false by (symmetry; apply Z.eqb_neq; lia);
           reflexivity.
        1: exact Hwb.
        1-5: eassumption.
        all: first [reflexivity | f_equal; lia].
      * kcond K3.
        eapply (keya_q2 _ gi e ok kl X w); try eassumption; try lia; try reflexivity.
Qed.

(** *** From KEY *)
Lemma keya_main : forall (t0 t1 t2 s1 a0 a1 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  evt rsegs (KPOST (m_key mc cur SL (line + 1)) cur)
    (MS (mkR ra (Z_to_bv 64 Sp) gp tp t0 t1 t2 (Z_to_bv 64 c) s1 a0 a1 (Z_to_bv 64 (Z.of_nat (j - i))) a3 a4 a5 a6
           a7 (Z_to_bv 64 (mf_next p rest)) (Z_to_bv 64 (line + 1)) (Z_to_bv 64 (p + Z.of_nat j))
           (Z_to_bv 64 (p + Z.of_nat i)) (Z_to_bv 64 0x1ff) (Z_to_bv 64 0x23) (Z_to_bv 64 (c + MC_N))
           (Z_to_bv 64 BLANK_MASK) (Z_to_bv 64 0x20) (Z_to_bv 64 0x3b) t3 t4 t5 t6)
        F (Z_to_bv 64 MFU_PC_KEY) fc None mcut (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 s1 a0 a1 a3 a4 a5 a6 a7 t3 t4 t5 t6.
  pose proof kf_sp0 as E0. pose proof kf_lo as (Hlo0 & Hlo1 & Hlo2 & Hlo3).
  pose proof kf_p as (Hp0 & AP). pose proof kf_len as HL. pose proof kf_bsr as Lb. pose proof kf_SL as HSL.
  pose proof kf_c as (Hc0 & Hc16 & Hc1 & Hns). pose proof kf_line as (Hl0 & Hl1). pose proof HPB as Hpb.
  pose proof kf_stk as ST0. pose proof kf_mi as MI0. pose proof kf_loopw as LOOPw.
  assert (Lbuf : length (firstn (j - i) (skipn i bsr)) = (j - i)%nat)
    by (rewrite firstn_length_le; [reflexivity | rewrite length_skipn; lia]).
  unfold MFU_PC_KEY.
  step. step. step.
  eapply evt_cut.
  { eapply HMC with (buf := firstn (j - i) (skipn i bsr)).
    - rewrite unsigned_lit by lia. apply keya_bat_sub; [exact HBR | lia].
    - rewrite !unsigned_lit by lia. unfold memchr_ok. rewrite firstn_all2 by lia.
      destruct (find_byte _ _); lia.
    - exact MI0. }
  intros ms' (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m1 & -> & MU1 & WM1 & MI1 & _).
  rewrite keya_mres.
  rewrite (ret_pc_even 0x14534) by (first [lia | reflexivity]).
  assert (ST1 : stk rsegs m1 lo (bv_unsigned sp0))
    by (eapply stk_transport_disjoint; [exact ST0 | exact MU1 | exact WM1 | exact I]).
  assert (MU : munch FW mcut m1) by (eapply munch_weaken; [|exact MU1]; intros x _; exact I).
  clear MU1.
  pose proof (keya_c30 m1 MU) as R30.
  assert (CASE : cur = None \/ exists gi, cur = Some gi)
    by (destruct cur as [g|]; [right; exists g; reflexivity | left; reflexivity]).
  destruct CASE as [Ec | [gi Ec]].
  - (* cur = NULL: refuse *)
    rewrite Ec in R30. cbn [cur_ptr] in R30.
    step. step. if_cases K; [|exfalso; vm_compute in K; discriminate K].
    rewrite (m_key_refuse mc cur SL (line + 1) (or_intror Ec)).
    eapply keya_refuse; eassumption.
  - rewrite Ec in R30. cbn [cur_ptr] in R30. unfold mseg_addr, MSEG_SIZE in R30.
    assert (Hgi : (gi < 32)%nat) by (pose proof kf_cur as CO; rewrite Ec in CO; cbn [cur_ok] in CO; lia).
    step. step. if_cases K; [exfalso; kcond K; lia|].
    destruct (memchr SL EQ) as [e|] eqn:Em; cbv beta iota.
    2:{ (* no '=': refuse *)
      step. if_cases K2; [|exfalso; vm_compute in K2; discriminate K2].
      rewrite (m_key_refuse mc cur SL (line + 1) (or_introl Em)).
      eapply keya_refuse; eassumption. }
    pose proof (memchr_some SL EQ e Em) as (He & _ & _).
    assert (LSL : length SL = (j - i)%nat)
      by (rewrite HSL, firstn_length_le; [reflexivity | rewrite length_skipn; lia]).
    rewrite LSL in He.
    step. if_cases K2; [exfalso; kcond K2; lia|].
    (* the scratch cells [sp + 0x88, sp + 0xa8) *)
    destruct (stk_split rsegs m1 lo (Sp + 168) (bv_unsigned sp0) ST1 ltac:(lia)) as [STa _].
    destruct (stk_carve rsegs m1 lo (Sp + 168) 32 STa ltac:(lia)) as [_ [junk RC]]. clear STa.
    replace (Sp + 168 - Z.of_nat 32) with (Sp + 136) in RC by lia.
    clear R30.
    step. step. step. step. if_cases K3; [exfalso; kcond K3; lia|].
    step. step. step. step. step. step.
    pose proof (proj1 (keya_rc4 _ _ _ _ _ _) RC) as (W4 & C88 & C90 & C98 & Ca0).
    (* strip(&k, &ke) 0x14564 *)
    assert (Zk : zs (firstn e (skipn i bsr)) = firstn e (skipn i rest))
      by (rewrite keya_zs_firstn, keya_zs_skipn, HZR; reflexivity).
    eapply (mfu_strip HSC) with (mcut := mcut) (fcc := fc) (mc0 := mc) (cur := cur) (k0 := k0) (rest := rest)
      (mc := mc) (pend := false) (ox := 160) (oy := 152) (sv := p + Z.of_nat i)
      (ev := p + Z.of_nat i + Z.of_nat e) (l := firstn e (skipn i bsr)).
    1: exact LOOPw.
    1: apply keya_mid; assumption.
    1-7: first [lia | reflexivity].
    1: rewrite unsigned_lit by exact HSp; exact Ca0.
    1: rewrite unsigned_lit by exact HSp; exact C98.
    1-2: rewrite !unsigned_lit by lia; lia.
    1: apply keya_bat_sub; [apply keya_text; assumption | lia].
    1: rewrite firstn_length_le by (rewrite length_skipn; lia); lia.
    1-2: lia.
    1: unfold apart in AP |- *; lia.
    intros m5 z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 MID5 MUs WMs CA CB.
    rewrite (ret_pc_even 0x14568) by (first [lia | reflexivity]).
    destruct MID5 as (_ & WM5 & MI5 & ST5 & _).
    rewrite unsigned_lit in MUs, CA, CB by exact HSp. rewrite Zk in CA, CB. unfold cell8 in CA, CB.
    assert (MU5 : munch FW mcut m5).
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MUs].
      intros x [Hx _]. cbn [outside]. split; [lia | split; [lia | exact I]]. }
    assert (C90' : bytes_at rsegs m5 (Sp + 144) (le8 (Z_to_bv 64 (p + Z.of_nat i + Z.of_nat e + 1))))
      by (eapply bytes_at_transport; [exact C90 | exact MUs | kdis]).
    assert (C88' : bytes_at rsegs m5 (Sp + 136) (le8 (Z_to_bv 64 (p + Z.of_nat j))))
      by (eapply bytes_at_transport; [exact C88 | exact MUs | kdis]).
    assert (W5 : wr_at rsegs m5 (Sp + 136) 32) by (eapply wr_at_transport; [exact W4 | exact WMs]).
    clear RC W4 C88 C90 C98 Ca0.
    (* strip(&v, &ve) 0x14570 *)
    step. step. step.
    assert (Zv : zs (firstn (j - i - S e) (skipn (i + S e) bsr)) = firstn (j - i - S e) (skipn (i + S e) rest))
      by (rewrite keya_zs_firstn, keya_zs_skipn, HZR; reflexivity).
    eapply (mfu_strip HSC) with (mcut := mcut) (fcc := fc) (mc0 := mc) (cur := cur) (k0 := k0) (rest := rest)
      (mc := mc) (pend := false) (ox := 144) (oy := 136) (sv := p + Z.of_nat i + Z.of_nat e + 1)
      (ev := p + Z.of_nat j) (l := firstn (j - i - S e) (skipn (i + S e) bsr)).
    1: exact LOOPw.
    1: apply keya_mid; assumption.
    1-7: first [lia | reflexivity].
    1: rewrite unsigned_lit by exact HSp; exact C90'.
    1: rewrite unsigned_lit by exact HSp; exact C88'.
    1-2: rewrite !unsigned_lit by lia; lia.
    1: replace (p + Z.of_nat i + Z.of_nat e + 1) with (p + Z.of_nat (i + S e)) by lia;
       apply keya_bat_sub; [apply keya_text; assumption | lia].
    1: rewrite firstn_length_le by (rewrite length_skipn; lia); lia.
    1-2: lia.
    1: unfold apart in AP |- *; lia.
    intros m6 z0' z1' z2' z3' z4' z5' z6' z7' z8' z9' z10' z11' z12' z13' z14' MID6 MUs2 WMs2 CA2 CB2.
    rewrite (ret_pc_even 0x14574) by (first [lia | reflexivity]).
    destruct MID6 as (_ & WM6 & MI6 & ST6 & _).
    rewrite unsigned_lit in MUs2, CA2, CB2 by exact HSp. rewrite Zv in CA2, CB2. unfold cell8 in CA2, CB2.
    assert (MU6 : munch FW mcut m6).
    { eapply munch_trans; [exact MU5|]. eapply munch_weaken; [|exact MUs2].
      intros x [Hx _]. cbn [outside]. split; [lia | split; [lia | exact I]]. }
    assert (CA' : bytes_at rsegs m6 (Sp + 160)
                    (le8 (Z_to_bv 64 (p + Z.of_nat i + Z.of_nat (strip_lead (firstn e (skipn i rest)))))))
      by (eapply bytes_at_transport; [exact CA | exact MUs2 | kdis]).
    assert (CB' : bytes_at rsegs m6 (Sp + 152)
                    (le8 (Z_to_bv 64 (p + Z.of_nat i + Z.of_nat e - Z.of_nat (strip_trail (firstn e (skipn i rest)))))))
      by (eapply bytes_at_transport; [exact CB | exact MUs2 | kdis]).
    assert (W6 : wr_at rsegs m6 (Sp + 136) 32) by (eapply wr_at_transport; [exact W5 | exact WMs2]).
    destruct (keya_hstrip rest i e ltac:(lia)) as (S1 & HS1).
    destruct (keya_hstrip rest (i + S e) (j - i - S e) ltac:(lia)) as (S2 & HS2).
    eapply (keya_quote _ gi e (i + strip_lead (firstn e (skipn i rest)))
              (e - strip_lead (firstn e (skipn i rest)) - strip_trail (firstn e (skipn i rest)))
              (i + S e + strip_lead (firstn (j - i - S e) (skipn (i + S e) rest)))
              (j - i - S e - strip_lead (firstn (j - i - S e) (skipn (i + S e) rest))
                 - strip_trail (firstn (j - i - S e) (skipn (i + S e) rest)))).
    1: exact Ec.
    1: exact Em.
    1: rewrite HSL, keya_ff by lia; symmetry; exact HS1.
    1: lia.
    1: rewrite HSL, keya_sf; symmetry; exact HS2.
    1: lia.
    1-4: assumption.
    1: apply (proj2 (keya_rc4 _ _ _ _ _ _)); exact (conj W6 (conj CB2 (conj CA2 (conj CB' CA')))).
    all: f_equal; lia.
Qed.
End KeyA.

Theorem mfu_keya_holds : memchr_contract -> strip_contract -> m_refuse_contract -> S_MFU_KEYA.
Proof.
  intros HMC HSC HRC n HT HKD. unfold H_MFU_KEY.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 c p line mc cur k0 rest i j
    Hlen Hne LOOP REGS E6 Hl512 Hij Hj Hsl Hnb E5 E4 E2.
  destruct REGS as (E0 & E2' & E3 & E7 & E8 & E9 & E10 & E11).
  subst s0 s2 s3 s7 s8 s9 s10 s11 s6 s5 s4 a2.
  pose proof LOOP as L. unfold m_file_loop in L. kloop L.
  destruct L_cs as (bsr & slack & HB & HZ & _ & _).
  pose proof (bytes_at_bound _ _ _ _ HB) as HBB. rewrite length_app in HBB. cbn [length] in HBB.
  assert (Lb : length bsr = length rest) by (rewrite <- HZ; symmetry; apply keya_zs_len).
  apply bytes_at_app in HB as [HB _].
  pose proof (bv_unsigned_in_range 64 sp) as Hsp. change (bv_modulus 64) with (2 ^ 64) in Hsp.
  rewrite <- (Z_to_bv_bv_unsigned sp).
  eapply keya_main with (n := n) (bsr := bsr); first [eassumption | lia].
Qed.
