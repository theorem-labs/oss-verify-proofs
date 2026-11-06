(** Piece P2 of reac_segconf_parse_file, the line driver (plain build, image 3776ca44d75c): proof of S_P2
    (Prog/reac_segconf_parse_file_pieces_c.v) from the contracts of strchr, strlen, memcpy and trim. Written new.

    Code (plain binary):
      HEAD 0x14dc4  s7 = p; nl = strchr(p, '\n') (0x14dd0); nl ? (len = nl - p, p' = nl + 1)
                    : (len = strlen(p) (0x14df0), p' = p + len); lineno++ (`addiw` 0x14e00);
                    `bltu len, s9 = 512` (0x14e04) else LONG 0x14e08.
      0x14e48       memcpy(buf = sp + 0x158, p, len) (0x14e58); buf[len] = 0 (0x14e64);
      0x14e68       the inlined strip_comment loop (s5 = buf + k, a0 = -k, no comment start before k): the NUL ends it,
                    or a mark ('#', ';') at k = 0 or after ' ' / '\t' gets buf[k] = 0 (0x14e9c);
      0x14ea0       trim(buf) (0x14ea4); *lp == 0 -> TAIL 0x154b4, '[' -> HDR 0x14ebc, else KEY 0x14ee0.
      TAIL 0x154b4  `lbu *p`; non-zero -> HEAD (pred n), else `j` DONE 0x1550c.
    Every exit cut is instantiated at o, ln and d ++ [pf_line s o]; the line's step is SegModel.r_line
    (pfA_facts.r_lines_skipn_step, r_line_short), and the callee posts are weakened back to the head's memory with
    the function's write list (pinv_move, pf_ret_weaken). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Tac Bytes ZBridge FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel SegBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec seg_env pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import strchr_c strlen_c memcpy_c trim_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import refuse_c reac_segconf_parse_file_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import reac_segconf_parse_file_pieces_c.
Import ListNotations.
Open Scope Z_scope.

(** ** Byte lists *)
Lemma p2_zb8 : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof. intros. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma p2_zb_zs : forall bs, zb (zs bs) = bs.
Proof. unfold zb, zs. induction bs as [|b bs IH]; cbn; [reflexivity|]. rewrite p2_zb8, IH. reflexivity. Qed.

Lemma p2_len_zs : forall bs, length (zs bs) = length bs.
Proof. intros. unfold zs. apply length_map. Qed.

Lemma p2_zs_range : forall bs i, 0 <= nth i (zs bs) 0 < 256.
Proof.
  unfold zs. induction bs as [|b bs IH]; intros [|i]; cbn; try lia; [|apply IH].
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. lia.
Qed.

Lemma p2_u8 : forall x, 0 <= x < 256 -> bv_unsigned (Z_to_bv 8 x) = x.
Proof.
  intros x Hx. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus.
  replace (2 ^ Z.of_N 8) with 256 by reflexivity. lia.
Qed.

Lemma p2_byte_at : forall bs sl i, (i <= length bs)%nat ->
  nth_error (bs ++ ZERO :: sl) i = Some (Z_to_bv 8 (nth i (zs bs) 0)).
Proof.
  intros bs sl i Hi. destruct (Nat.lt_ge_cases i (length bs)) as [Hl|Hg].
  - rewrite nth_error_app1 by exact Hl. unfold zs.
    rewrite (nth_indep _ 0 (bv_unsigned ZERO)) by (rewrite length_map; exact Hl).
    rewrite map_nth, p2_zb8. apply nth_error_nth'. exact Hl.
  - assert (i = length bs) as -> by lia. rewrite nth_error_app2, Nat.sub_diag by lia. cbn.
    rewrite nth_overflow by (rewrite p2_len_zs; lia). reflexivity.
Qed.

Lemma p2_zs_firstn : forall bs k, zs (firstn k bs) = firstn k (zs bs).
Proof. intros. unfold zs. rewrite firstn_map. reflexivity. Qed.

Lemma p2_zb_firstn : forall bs k, zb (firstn k (zs bs)) = firstn k bs.
Proof. intros bs k. unfold zb. rewrite <- firstn_map. fold (zb (zs bs)). rewrite p2_zb_zs. reflexivity. Qed.

Lemma p2_firstn_add : forall {A} (a b : nat) (l : list A), firstn (a + b) l = firstn a l ++ firstn b (skipn a l).
Proof.
  intros A a. induction a as [|a IH]; intros b l; [reflexivity|].
  destruct l as [|x l]; cbn; [destruct b; reflexivity|]. rewrite IH. reflexivity.
Qed.

Lemma p2_hd0_nth : forall l, nth 0 l 0 = hd0 l.
Proof. intros [|x l]; reflexivity. Qed.

Lemma p2_upd_prefix : forall (bs sl : list byte) k, (k <= length bs)%nat ->
  upd_bytes (bs ++ ZERO :: sl) k [ZERO] = (firstn k bs ++ [ZERO]) ++ skipn (k + 1) (bs ++ ZERO :: sl).
Proof.
  intros bs sl k H. unfold upd_bytes. rewrite firstn_app. replace (k - length bs)%nat with 0%nat by lia.
  rewrite firstn_O, app_nil_r. cbn [length]. rewrite <- app_assoc. reflexivity.
Qed.

Lemma p2_bytes_at_prefix : forall m a l1 l2, bytes_at rsegs m a (l1 ++ l2) -> bytes_at rsegs m a l1.
Proof. intros m a l1 l2 H. apply bytes_at_app in H. tauto. Qed.

Lemma p2_len_cm8 : forall ws, length (concat (map le8 ws)) = (8 * length ws)%nat.
Proof. induction ws as [|w ws IH]; [reflexivity|]. cbn [map concat length]. rewrite length_app, length_le8, IH. lia. Qed.

(** `addiw s3, s3, 1` (0x14e00): lineno + 1 stays below 2^31. *)
Lemma p2_swrap1 : forall x, 0 <= x < 2 ^ 31 - 1 -> bv_swrap 32 (x + 1) = x + 1.
Proof.
  intros x Hx. apply bv_swrap_small. replace (bv_half_modulus 32) with 2147483648 by reflexivity. lia.
Qed.

(** ** Memory *)
Lemma p2_disjoint_from_sub : forall W a n a' n',
  disjoint_from W a n -> a <= a' -> a' + n' <= a + n -> disjoint_from W a' n'.
Proof.
  induction W as [|[l h] W IH]; cbn [disjoint_from]; intros a n a' n' D H1 H2; [exact I|].
  destruct D as [D1 D2]. split; [lia | exact (IH a n a' n' D2 H1 H2)].
Qed.

Lemma p2_rconf_at_munch : forall W m m' c rc,
  rconf_at rsegs m c rc -> munch W m m' -> disjoint_from W c SEG_C_SIZE -> rconf_at rsegs m' c rc.
Proof.
  intros W m m' c rc (bs & B & E) MU D. exists bs. split; [|exact E].
  eapply bytes_at_transport; [exact B | exact MU |]. destruct E as [L _]. rewrite L. exact D.
Qed.

Lemma p2_cstr_at_munch : forall W m m' a s,
  cstr_at rsegs m a s -> munch W m m' -> disjoint_from W a (Z.of_nat (length s) + 8) -> cstr_at rsegs m' a s.
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
  eapply p2_disjoint_from_sub; [exact D | lia |].
  rewrite length_app; cbn [length]. rewrite Lk, Lbs. lia.
Qed.

(** Every byte of a present stack region is a task byte (MemNorm.task_mem's condition). *)
Lemma p2_stk_task : forall m lo hi, MemNorm.task_mem rsegs m -> stk rsegs m lo hi ->
  forall x : word, lo <= bv_unsigned x < hi ->
  find_segment rsegs (bv_unsigned x) 1 <> None \/ bv_unsigned x < TASK_SIZE.
Proof.
  intros m lo hi T (_ & _ & S) x Hx. destruct (S _ Hx) as [_ [b Hb]].
  replace (wa (bv_unsigned x)) with x in Hb by (unfold wa; symmetry; apply Z_to_bv_bv_unsigned).
  unfold mrd in Hb. destruct (m x) as [b'|] eqn:E.
  - exact (T x b' E).
  - left. intros Nf. rewrite (MemNorm.seg_rom_unmapped rsegs x Nf) in Hb. discriminate.
Qed.

Ltac sa_num := cbn [SA SEG_PLAIN SEG_UBSAN sa_img_end sa_img_top sa_guard sa_got_guard sa_catalogue] in *.

Lemma p2_ssp_ok_munch : forall W m m', ssp_ok m -> munch W m m' -> disjoint_from W 0 (sa_img_end SA) -> ssp_ok m'.
Proof.
  intros W m m' (G1 & g & G2) MU D. split; [|exists g].
  - eapply bytes_at_transport; [exact G1 | exact MU |]. rewrite length_le8.
    eapply p2_disjoint_from_sub; [exact D | sa_num; lia | sa_num; lia].
  - eapply bytes_at_transport; [exact G2 | exact MU |]. rewrite length_le8.
    eapply p2_disjoint_from_sub; [exact D | sa_num; lia | sa_num; lia].
Qed.

Lemma p2_cat_img_munch : forall W m m', cat_img rsegs m (sa_catalogue SA) -> munch W m m' ->
  disjoint_from W 0 (sa_img_end SA) -> cat_img rsegs m' (sa_catalogue SA).
Proof.
  intros W m m' CAT MU D a Ha. rewrite <- (CAT a Ha). unfold mrd.
  sa_num. unfold CAT_BYTES in Ha.
  assert (Q : m' (wa a) = m (wa a)).
  { apply MU. rewrite wa_unsigned by lia. eapply disjoint_outside; [exact D | lia]. }
  rewrite Q. reflexivity.
Qed.

Lemma p2_outside_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[l h] W IH]; intros x; cbn [outside]; [left; exact I|].
  destruct (IH x) as [H|H].
  - destruct (Z_le_gt_dec l x) as [A|A]; destruct (Z_lt_ge_dec x h) as [B|B].
    + right. intros [C _]. apply C. lia.
    + left. split; [lia | exact H].
    + left. split; [lia | exact H].
    + left. split; [lia | exact H].
  - right. intros [_ C]. exact (H C).
Qed.

(** The writes a step of P2 makes: the 32 bytes of a callee's frame below sp, or bytes of buf. *)
Definition okW (Sp : Z) (W : list ivl) : Prop :=
  Forall (fun iv => (Sp - 32 <= fst iv /\ snd iv <= Sp) \/ (Sp + 344 <= fst iv /\ snd iv <= Sp + 856)) W.

Lemma okW_disj : forall Sp W A n, okW Sp W ->
  (A + n <= Sp - 32 \/ Sp <= A) -> (A + n <= Sp + 344 \/ Sp + 856 <= A) -> disjoint_from W A n.
Proof.
  intros Sp W A n H. induction H as [|[l h] W Hiv HW IH]; intros D1 D2; cbn [disjoint_from]; [exact I|].
  split; [|exact (IH D1 D2)]. cbn [fst snd] in Hiv. lia.
Qed.

Lemma okW_in : forall Sp W x, okW Sp W -> ~ outside W x -> (Sp - 32 <= x < Sp) \/ (Sp + 344 <= x < Sp + 856).
Proof.
  intros Sp W x H. induction H as [|[l h] W Hiv HW IH]; cbn [outside]; intros Ho; [exfalso; exact (Ho I)|].
  cbn [fst snd] in Hiv.
  destruct (Z_le_gt_dec l x); destruct (Z_lt_ge_dec x h).
  - lia.
  - apply IH. intros Hx. apply Ho. split; [lia | exact Hx].
  - apply IH. intros Hx. apply Ho. split; [lia | exact Hx].
  - apply IH. intros Hx. apply Ho. split; [lia | exact Hx].
Qed.

Lemma p2_task_mem_move : forall W m m' lo hi Sp, MemNorm.task_mem rsegs m -> stk rsegs m lo hi -> munch W m m' ->
  okW Sp W -> lo <= Sp - 32 -> Sp + 856 <= hi -> MemNorm.task_mem rsegs m'.
Proof.
  intros W m m' lo hi Sp T ST MU OK L H a b E.
  destruct (p2_outside_dec W (bv_unsigned a)) as [O|O].
  - rewrite (MU a O) in E. exact (T a b E).
  - pose proof (okW_in Sp W _ OK O) as IN. apply (p2_stk_task m lo hi T ST). lia.
Qed.

(** The function's write list (pf_ret). *)
Definition WF (Sp c : Z) : list ivl :=
  (Sp + PARSE_FILE_FRAME - PARSE_FILE_STACK, Sp + PARSE_FILE_FRAME) :: RC_PARSE_W c.

Lemma okW_sub_WF : forall Sp c W, okW Sp W -> sub_fp W (WF Sp c).
Proof.
  intros Sp c W H x Hx. unfold WF in Hx. cbn [outside] in Hx. destruct Hx as [Hx _].
  destruct (p2_outside_dec W x) as [O|O]; [exact O|]. exfalso. apply Hx.
  pose proof (okW_in Sp W x H O). unfold PARSE_FILE_STACK, PARSE_FILE_FRAME, REFUSE_STACK, PRINTF_K. lia.
Qed.

Lemma p2_stk_bytes_upd : forall m m' A B bs, stk rsegs m A B -> wmono rsegs m m' -> bytes_at rsegs m' A bs ->
  B = A + Z.of_nat (length bs) -> stk rsegs m' A B.
Proof.
  intros m m' A B bs (H1 & H2 & H) WM (Ba & Bl & BY) EB. split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as [Hw _]. split; [apply WM; exact Hw|].
  pose proof (BY (Z.to_nat (a - A)) ltac:(lia)) as R. replace (A + Z.of_nat (Z.to_nat (a - A))) with a in R by lia.
  rewrite R. destruct (nth_error bs (Z.to_nat (a - A))) eqn:E; [eexists; reflexivity|].
  apply nth_error_None in E. lia.
Qed.

Lemma p2_wr_of_stk : forall m lo hi a n, stk rsegs m lo hi -> lo <= a -> a + n <= hi -> 0 <= n -> wr_at rsegs m a n.
Proof.
  intros m lo hi a n (H1 & H2 & H) L1 L2 L3. split; [lia|]. split; [lia|].
  intros i Hi. destruct (H (a + i) ltac:(lia)) as [W _]. exact W.
Qed.

(** A C string in the frame: its slack is the frame bytes after its NUL. *)
Lemma p2_cstr_of_frame : forall m a bs a1 a2, bytes_at rsegs m a (bs ++ [ZERO]) -> stk rsegs m a1 a2 ->
  a1 <= a + Z.of_nat (length bs) + 1 -> a + Z.of_nat (length bs) + 8 <= a2 -> ~ In 0 (zs bs) ->
  cstr_at rsegs m a (zs bs).
Proof.
  intros m a bs a1 a2 B ST L1 L2 NZ.
  destruct (stk_split rsegs m a1 (a + Z.of_nat (length bs) + 1) a2 ST ltac:(lia)) as [_ ST2].
  destruct (stk_split rsegs m (a + Z.of_nat (length bs) + 1) (a + Z.of_nat (length bs) + 8) a2 ST2 ltac:(lia))
    as [ST3 _].
  destruct (stk_bytes rsegs m _ _ ST3 ltac:(lia)) as (sl & Lsl & Bsl).
  exists bs, sl. split.
  - replace (bs ++ ZERO :: sl) with ((bs ++ [ZERO]) ++ sl) by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app. split; [exact B|]. rewrite length_app. cbn [length].
    replace (a + Z.of_nat (length bs + 1)) with (a + Z.of_nat (length bs) + 1) by lia. exact Bsl.
  - split; [reflexivity|]. split; [exact NZ|].
    rewrite p2_len_zs, Lsl. pose proof (Z.mod_pos_bound (- (a + Z.of_nat (length bs) + 1)) 8 ltac:(lia)). lia.
Qed.

Lemma p2_read_byte : forall m a bs k, bytes_at rsegs m a (bs ++ [ZERO]) -> (k <= length bs)%nat ->
  ov_read_bytes rsegs m (Z_to_bv 64 (a + Z.of_nat k)) 1 = Some [Z_to_bv 8 (nth k (zs bs) 0)].
Proof.
  intros m a bs k B Hk. eapply (u8ro_read rsegs m a (bs ++ [ZERO]) (Z.of_nat k)); [exact B | | lia | reflexivity].
  rewrite Nat2Z.id. apply p2_byte_at. exact Hk.
Qed.

Lemma p2_slack_cut : forall m a bs sl,
  bytes_at rsegs m a (bs ++ ZERO :: sl) -> (- (a + Z.of_nat (length bs) + 1)) mod 8 <= Z.of_nat (length sl) ->
  exists sl', bytes_at rsegs m a (bs ++ ZERO :: sl') /\ (length sl' <= 7)%nat /\
    (- (a + Z.of_nat (length bs) + 1)) mod 8 <= Z.of_nat (length sl').
Proof.
  intros m a bs sl H Hk. set (k := Z.to_nat ((- (a + Z.of_nat (length bs) + 1)) mod 8)).
  assert (Hk8 : 0 <= (- (a + Z.of_nat (length bs) + 1)) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
  exists (firstn k sl). split; [|split].
  - apply (p2_bytes_at_prefix m a _ (skipn k sl)). rewrite <- app_assoc. cbn [app]. rewrite firstn_skipn. exact H.
  - rewrite length_firstn. lia.
  - rewrite length_firstn. lia.
Qed.

Lemma p2_bytes_store_end : forall m a bs, bytes_at rsegs m a bs -> a + Z.of_nat (length bs) + 1 <= 2 ^ 64 ->
  bytes_at rsegs (write_to_mem m (wa (a + Z.of_nat (length bs))) [ZERO]) a (bs ++ [ZERO]).
Proof.
  intros m a bs B L. pose proof (bytes_at_bound _ _ _ _ B) as BB.
  apply bytes_at_app. split.
  - eapply bytes_at_write_other; [exact B | lia | cbn [length]; lia | cbn [length]; lia].
  - apply bytes_at_write_same; [lia | cbn [length]; lia].
Qed.

Lemma p2_bytes_store_cut : forall m a bs k, bytes_at rsegs m a (bs ++ [ZERO]) -> (k <= length bs)%nat ->
  bytes_at rsegs (write_to_mem m (wa (a + Z.of_nat k)) [ZERO]) a (firstn k bs ++ [ZERO]).
Proof.
  intros m a bs k B Hk.
  pose proof (bytes_at_write_inside rsegs m a (bs ++ [ZERO]) (Z.of_nat k) [ZERO] B ltac:(lia)
    ltac:(rewrite Nat2Z.id, length_app; cbn [length]; lia)) as NW.
  rewrite Nat2Z.id, p2_upd_prefix in NW by exact Hk. apply p2_bytes_at_prefix in NW. exact NW.
Qed.

Lemma p2_saved_hd : forall m a w ws, saved_at rsegs m a (w :: ws) -> bytes_at rsegs m a (le8 w).
Proof. intros m a w ws H. unfold saved_at in H. cbn [map concat] in H. apply bytes_at_app in H. tauto. Qed.

Lemma p2_saved_tl : forall m a w ws, saved_at rsegs m a (w :: ws) -> saved_at rsegs m (a + 8) ws.
Proof.
  intros m a w ws H. unfold saved_at in *. cbn [map concat] in H. apply bytes_at_app in H as [_ H].
  rewrite length_le8 in H. exact H.
Qed.

(** ** The loop state in the memory of a cut *)
Definition pinv (m0 m : word -> option byte) (fc : bv 32) (Sp lo : Z) (v : pf_sv) (c t : Z) (s : list Z) (o : nat)
    (rc : rconf) (cur : option nat) (nm : list Z) : Prop :=
  pf_env m fc Sp lo c v /\ pf_text m Sp lo c t s /\ pf_spill m Sp c /\
  cstr_at rsegs m (t + Z.of_nat o) (skipn o s) /\ pf_state m Sp c rc cur nm (length (skipn o s)) /\
  munch (WF Sp c) m0 m /\ wmono rsegs m0 m.

(** A step that writes only okW bytes keeps it. *)
Lemma pinv_move : forall m0 m m' fc Sp lo v c t s o rc cur nm W,
  pinv m0 m fc Sp lo v c t s o rc cur nm -> (o <= length s)%nat ->
  munch W m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (Sp + PARSE_FILE_FRAME) -> okW Sp W ->
  pinv m0 m' fc Sp lo v c t s o rc cur nm.
Proof.
  intros m0 m m' fc Sp lo v c t s o rc cur nm W (ENV & TXT & SPL & CS & ST & MU0 & WM0) Ho MU WM MI STK' OK.
  destruct ENV as (C0 & C16 & APc & BNI & PE & CAT & SO & MIo & SV).
  destruct PE as (FRM & TM & SSP & IL & SPH).
  destruct SO as (STK & DEP & AL & NR).
  destruct TXT as (T0 & TCS & TL & APt & APtc).
  destruct ST as (RC & CO & (f & NMB & NME) & CNT).
  assert (LO0 : 0 <= lo) by (destruct STK as [? _]; lia).
  unfold PARSE_FILE_STACK, PARSE_FILE_FRAME, REFUSE_STACK, PRINTF_K in DEP, STK, STK', SPH, APc, APt.
  unfold apart in APc, APt.
  assert (D0 : disjoint_from W 0 (sa_img_end SA)) by (apply (okW_disj Sp); [exact OK | lia | lia]).
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
  - unfold pf_env. split; [exact C0|]. split; [exact C16|]. split; [exact APc|]. split; [exact BNI|].
    split.
    { split; [exact FRM|]. split.
      - eapply p2_task_mem_move; [exact TM | exact STK | exact MU | exact OK | lia | lia].
      - split; [eapply p2_ssp_ok_munch; [exact SSP | exact MU | exact D0]|]. split; [exact IL | exact SPH]. }
    split; [eapply p2_cat_img_munch; [exact CAT | exact MU | exact D0]|].
    split; [split; [exact STK'|]; split; [exact DEP|]; split; [exact AL | exact NR]|].
    split; [exact MI|].
    unfold saved_at in *. eapply bytes_at_transport; [exact SV | exact MU |].
    rewrite p2_len_cm8. cbn [sv_list length]. apply (okW_disj Sp); [exact OK | unfold PF_SAVE; lia | unfold PF_SAVE; lia].
  - unfold pf_text. split; [exact T0|]. split; [|split; [exact TL | split; [exact APt | exact APtc]]].
    eapply p2_cstr_at_munch; [exact TCS | exact MU |]. apply (okW_disj Sp); [exact OK | lia | lia].
  - unfold pf_spill, saved_at in *. eapply bytes_at_transport; [exact SPL | exact MU |].
    rewrite p2_len_cm8. cbn [length]. apply (okW_disj Sp); [exact OK | lia | lia].
  - eapply p2_cstr_at_munch; [exact CS | exact MU |]. rewrite pfa_len_skipn.
    apply (okW_disj Sp); [exact OK | lia | lia].
  - unfold pf_state. split.
    { eapply p2_rconf_at_munch; [exact RC | exact MU |].
      apply (okW_disj Sp); [exact OK | unfold SEG_C_SIZE in *; lia | unfold SEG_C_SIZE in *; lia]. }
    split; [exact CO|]. split; [|exact CNT].
    exists f. split; [|exact NME]. eapply bytes_at_transport; [exact NMB | exact MU |].
    destruct NME as [Lf _]. rewrite Lf.
    apply (okW_disj Sp); [exact OK | unfold PF_NAMEBUF; lia | unfold PF_NAMEBUF; lia].
  - eapply munch_trans; [exact MU0 | eapply munch_weaken; [apply okW_sub_WF; exact OK | exact MU]].
  - eapply wmono_trans; [exact WM0 | exact WM].
Qed.

(** The function's post from a later memory, back to an earlier one. *)
Lemma pf_ret_weaken : forall v sp gp tp F m0 m lo c rcf ms,
  munch (WF (bv_unsigned sp) c) m0 m -> wmono rsegs m0 m ->
  pf_ret v sp gp tp F m lo c rcf ms -> pf_ret v sp gp tp F m0 lo c rcf ms.
Proof.
  intros v sp gp tp F m0 m lo c rcf ms MU WM H. unfold pf_ret, ret_post_fp in *.
  destruct H as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F' & fc' & m' &
                 E & FR & FF & MU' & WM' & MI & TM & STK & Q).
  exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, F', fc', m'.
  split; [exact E|]. split; [exact FR|]. split; [exact FF|].
  split; [eapply munch_trans; [exact MU | exact MU']|].
  split; [eapply wmono_trans; [exact WM | exact WM']|].
  split; [exact MI|]. split; [exact TM|]. split; [exact STK | exact Q].
Qed.

Ltac fix_ret_pc :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity])
  end.
Ltac dj := cbn [disjoint_from]; repeat split; first [exact I | lia].
Ltac okw := unfold okW; repeat (apply Forall_cons; [cbn [fst snd]; lia|]); apply Forall_nil.
Ltac regs_ok := unfold pf_regs; repeat split; first [reflexivity | f_equal; lia].
Ltac weq := first [reflexivity | f_equal; lia | apply bv_eq; rewrite ?unsigned_lit by lia; lia].
Ltac bnorm K := rewrite ?p2_u8 in K by lia; rewrite ?Z.mod_small in K by lia.

(** ** HEAD -> LONG, HDR, KEY or TAIL *)
Section Walk.
Variable n : nat.
Hypothesis HSC : strchr_contract.
Hypothesis HSL : strlen_contract.
Hypothesis HMC : memcpy_contract.
Hypothesis HTR : trim_contract.
Hypothesis HLONG : H_LONG n.
Hypothesis HHDR : H_HDR n.
Hypothesis HKEY : H_KEY n.
Hypothesis HTAIL : H_TAIL n.

Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte) (lo : Z) (v : pf_sv)
  (c t : Z) (s : list Z) (rc : rconf) (cur : option nat) (nm : list Z) (o : nat) (ln : Z) (d : list (list Z)).
Hypothesis HC0 : pf_hctx m0 fc (bv_unsigned sp) lo v c t s o ln d.
Hypothesis HS0 : pf_state m0 (bv_unsigned sp) c rc cur nm (length (skipn o s)).
Hypothesis Ho : (o < length s)%nat.
Hypothesis Hn : (length (skipn o s) <= n)%nat.

Local Abbreviation Sp := (bv_unsigned sp).
Local Abbreviation LEN := (length (pf_line s o)).
Local Abbreviation INV m := (pinv m0 m fc (bv_unsigned sp) lo v c t s o rc cur nm).
Local Abbreviation POST := (pf_fin v sp gp tp F m0 lo c (r_lines (rc, cur, nm) ln (lines (skipn o s)))).

Lemma nums : 0 <= lo /\ lo + 6032 <= Sp /\ Sp + 976 < 2 ^ 63 /\ (Sp + 976) mod 16 = 0 /\ 0 < t /\
  (t + Z.of_nat (length s) + 8 <= lo \/ Sp + 976 <= t) /\ t + Z.of_nat (length s) + 1 <= 2 ^ 64 /\
  ~ In 0 s /\ 0 <= ln <= Z.of_nat o /\ Z.of_nat (length s) <= 65535.
Proof.
  pose proof HC0 as (ENV & TXT & SPL & LC & CS).
  destruct ENV as (C0 & C16 & APc & BNI & PE & CAT & SO & MIo & SV).
  destruct PE as (FRM & TM & SSP & IL & SPH). destruct SO as (STK & DEP & AL & NR).
  destruct TXT as (T0 & TCS & TL & APt & APtc).
  destruct TCS as (bs & sl & BY & ZS & NZ & SLK).
  pose proof (bytes_at_bound _ _ _ _ BY) as BB. rewrite length_app in BB. cbn [length] in BB.
  assert (LB : length bs = length s) by (rewrite <- ZS; symmetry; apply p2_len_zs).
  destruct (pf_lctx_ln _ _ _ _ LC) as [LN _].
  unfold apart, PARSE_FILE_STACK, PARSE_FILE_FRAME, REFUSE_STACK, PRINTF_K in *.
  destruct STK as [LO0 _].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [first [exact AL | lia]|]. split; [lia|]. split; [lia|].
  split; [lia|]. split; [exact NZ|]. split; [lia|].
  apply Nat2Z.inj_le in TL. replace (Z.of_nat 65535%nat) with 65535 in TL by reflexivity. exact TL.
Qed.

Lemma inv0 : INV m0.
Proof.
  pose proof HC0 as (ENV & TXT & SPL & LC & CS). split; [exact ENV|]. split; [exact TXT|]. split; [exact SPL|].
  split; [exact CS|]. split; [exact HS0|]. split; [apply munch_refl | apply wmono_refl].
Qed.

Lemma step_eq : r_lines (rc, cur, nm) ln (lines (skipn o s)) =
  r_lines (r_line rc cur nm (ln + 1) (pf_line s o)) (ln + 1) (lines (skipn (pf_next s o) s)).
Proof. rewrite (r_lines_skipn_step s o (rc, cur, nm) ln Ho). reflexivity. Qed.

Lemma post_of : forall m st ms, munch (WF Sp c) m0 m -> wmono rsegs m0 m ->
  r_lines (rc, cur, nm) ln (lines (skipn o s)) = r_lines st (ln + 1) (lines (skipn (pf_next s o) s)) ->
  pf_fin v sp gp tp F m lo c (r_lines st (ln + 1) (lines (skipn (pf_next s o) s))) ms -> POST ms.
Proof. intros m st ms MU WM E P. unfold pf_fin in *. rewrite E. eapply pf_ret_weaken; eassumption. Qed.

Lemma ctx_next : forall m, INV m -> pf_ctx m fc Sp lo v c t s o ln (d ++ [pf_line s o]) n.
Proof.
  intros m (ENV & TXT & SPL & _). pose proof HC0 as (_ & _ & _ & LC & _).
  pose proof nums as (_ & _ & _ & _ & _ & _ & _ & NZ & _).
  unfold pf_ctx. split; [exact ENV|]. split; [exact TXT|]. split; [exact SPL|]. split; [exact Ho|].
  split; [exact Hn|]. apply pf_lctx_next; [exact NZ | exact LC | exact Ho].
Qed.

(** *** The exit cuts *)
Lemma ex_long : forall m (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
  INV m -> (512 <= LEN)%nat ->
  pf_regs s0 s1 s2 s3 s4 s10 s11 c (t + Z.of_nat (pf_next s o)) (ln + 1) ->
  s9 = Z_to_bv 64 512 -> s6 = Z_to_bv 64 (pf_cur_ptr c cur) ->
  s7 = Z_to_bv 64 (t + Z.of_nat o) -> s8 = Z_to_bv 64 (Z.of_nat LEN) ->
  evt rsegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 PF_PC_LONG) fc None m (seg_rom rsegs)).
Proof.
  intros m ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    INVm HL HR H9 H6 H7 H8.
  pose proof INVm as (_ & _ & _ & _ & ST & MU & WM).
  eapply evt_mono.
  - eapply (HLONG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              F fc m lo v c t s rc cur nm o ln (d ++ [pf_line s o]));
      [apply ctx_next; exact INVm | exact ST | exact HR | exact H9 | exact H6 | exact H7 | exact H8 | exact HL].
  - intros ms' P. eapply post_of; [exact MU | exact WM | exact step_eq | exact P].
Qed.

Lemma ex_tail : forall m (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
  INV m -> (LEN < 512)%nat -> hd0 (pf_tline s o) = 0 ->
  pf_regs s0 s1 s2 s3 s4 s10 s11 c (t + Z.of_nat (pf_next s o)) (ln + 1) ->
  s9 = Z_to_bv 64 512 -> s6 = Z_to_bv 64 (pf_cur_ptr c cur) ->
  evt rsegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 PF_PC_TAIL) fc None m (seg_rom rsegs)).
Proof.
  intros m ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    INVm HL H0 HR H9 H6.
  pose proof INVm as (ENV & TXT & SPL & _ & ST & MU & WM).
  pose proof HC0 as (_ & _ & _ & LC & _).
  pose proof nums as (_ & _ & _ & _ & _ & _ & _ & NZ & _).
  pose proof (pf_next_le s o Ho) as Hle.
  pose proof (pf_next_skipn_lt s o Ho) as SL.
  eapply evt_mono.
  - eapply (HTAIL ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              F fc m lo v c t s rc cur nm (pf_next s o) (ln + 1) (d ++ [pf_line s o])).
    + unfold pf_hctx. split; [exact ENV|]. split; [exact TXT|]. split; [exact SPL|].
      split; [apply pf_lctx_next; [exact NZ | exact LC | exact Ho]|].
      destruct TXT as (_ & TCS & _). apply L_cstr_skipn_holds; [exact TCS | exact Hle].
    + destruct ST as (RC & CO & NMa & CNT). split; [exact RC|]. split; [exact CO|]. split; [exact NMa|].
      eapply pf_cnt_mono; [|exact CNT]. lia.
    + lia.
    + exact HR.
    + exact H9.
    + exact H6.
  - intros ms' P. eapply post_of; [exact MU | exact WM | | exact P].
    rewrite step_eq, (r_line_short rc cur nm (ln + 1) s o HL), H0. reflexivity.
Qed.

Lemma ex_hdr : forall m lp (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
  INV m -> (LEN < 512)%nat ->
  pf_regs s0 s1 s2 s3 s4 s10 s11 c (t + Z.of_nat (pf_next s o)) (ln + 1) ->
  s9 = Z_to_bv 64 512 -> s6 = Z_to_bv 64 (pf_cur_ptr c cur) -> s7 = Z_to_bv 64 lp ->
  cstr_at rsegs m lp (pf_tline s o) -> pf_inb (Sp + PF_BUF) lp (pf_tline s o) -> hd0 (pf_tline s o) = LBR ->
  evt rsegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 PF_PC_HDR) fc None m (seg_rom rsegs)).
Proof.
  intros m lp ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    INVm HL HR H9 H6 H7 HCS HIB HB.
  pose proof INVm as (_ & _ & _ & _ & ST & MU & WM).
  eapply evt_mono.
  - eapply (HHDR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              F fc m lo v c t s rc cur nm o ln (d ++ [pf_line s o]) lp);
      [apply ctx_next; exact INVm | exact ST | exact HR | exact H9 | exact H6 | exact HL | exact H7 | exact HCS
      | exact HIB | exact HB].
  - intros ms' P. eapply post_of; [exact MU | exact WM | | exact P].
    rewrite step_eq, (r_line_short rc cur nm (ln + 1) s o HL), HB. reflexivity.
Qed.

Lemma ex_key : forall m lp (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
  INV m -> (LEN < 512)%nat ->
  pf_regs s0 s1 s2 s3 s4 s10 s11 c (t + Z.of_nat (pf_next s o)) (ln + 1) ->
  s9 = Z_to_bv 64 512 -> s6 = Z_to_bv 64 (pf_cur_ptr c cur) -> s7 = Z_to_bv 64 lp ->
  cstr_at rsegs m lp (pf_tline s o) -> pf_inb (Sp + PF_BUF) lp (pf_tline s o) ->
  hd0 (pf_tline s o) <> 0 -> hd0 (pf_tline s o) <> LBR ->
  evt rsegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 PF_PC_KEY) fc None m (seg_rom rsegs)).
Proof.
  intros m lp ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    INVm HL HR H9 H6 H7 HCS HIB K0 K1.
  pose proof INVm as (_ & _ & _ & _ & ST & MU & WM).
  eapply evt_mono.
  - eapply (HKEY ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              F fc m lo v c t s rc cur nm o ln (d ++ [pf_line s o]) lp);
      [apply ctx_next; exact INVm | exact ST | exact HR | exact H9 | exact H6 | exact HL | exact H7 | exact HCS
      | exact HIB | exact K0 | exact K1].
  - intros ms' P. eapply post_of; [exact MU | exact WM | | exact P].
    rewrite step_eq, (r_line_short rc cur nm (ln + 1) s o HL).
    rewrite (proj2 (Z.eqb_neq _ _) K0), (proj2 (Z.eqb_neq _ _) K1). reflexivity.
Qed.

(** *** 0x14ea8: after trim, s7 = lp, the first byte of the trimmed line picks the exit *)
Lemma at_ea8 : forall m rb lp (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s7 s8 t3 t4 t5 t6 : word),
  INV m -> (LEN < 512)%nat -> zs rb = pf_tline s o ->
  bytes_at rsegs m lp (rb ++ [ZERO]) -> Sp + 344 <= lp -> lp + Z.of_nat (length rb) < Sp + 856 ->
  evt rsegs POST (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 c) (Z_to_bv 64 35) (Z_to_bv 64 lp) a1 a2 a3 a4 a5 a6 a7
      (Z_to_bv 64 (t + Z.of_nat (pf_next s o))) (Z_to_bv 64 (ln + 1)) (Z_to_bv 64 59) s5
      (Z_to_bv 64 (pf_cur_ptr c cur)) s7 s8 (Z_to_bv 64 512) (Z_to_bv 64 32) (Z_to_bv 64 9) t3 t4 t5 t6)
      F (Z_to_bv 64 0x14ea8) fc None m (seg_rom rsegs)).
Proof.
  intros m rb lp ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s7 s8 t3 t4 t5 t6 INVm HL ZR BY L1 L2.
  pose proof INVm as (ENV & _).
  pose proof nums as (LO0 & DEP & SPH & AL & T0 & APt & TB & NZ & LN & TL).
  pose proof ENV as (_ & _ & _ & _ & _ & _ & (STK & _) & _). unfold PARSE_FILE_FRAME in STK.
  assert (NZr : ~ In 0 (zs rb)) by (rewrite ZR; apply pf_tline_nul; exact NZ).
  assert (HCS : cstr_at rsegs m lp (pf_tline s o)).
  { rewrite <- ZR. eapply p2_cstr_of_frame; [exact BY | exact STK | lia | lia | exact NZr]. }
  assert (HIB : pf_inb (Sp + PF_BUF) lp (pf_tline s o)).
  { unfold pf_inb, PF_BUF. rewrite <- ZR, p2_len_zs. lia. }
  assert (RD : ov_read_bytes rsegs m (Z_to_bv 64 lp) 1 = Some [Z_to_bv 8 (hd0 (pf_tline s o))]).
  { pose proof (p2_read_byte m lp rb 0 BY ltac:(lia)) as R. change (Z.of_nat 0) with 0 in R.
    rewrite Z.add_0_r, p2_hd0_nth, ZR in R. exact R. }
  pose proof (p2_zs_range rb 0) as RG. rewrite p2_hd0_nth, ZR in RG.
  zstep. zstep. zstep. if_cases K; zify_cond K; bnorm K.
  - eapply ex_tail; [exact INVm | exact HL | exact K | regs_ok | reflexivity | reflexivity].
  - zstep. zstep. if_cases K2; zify_cond K2; bnorm K2.
    + eapply ex_key; [exact INVm | exact HL | regs_ok | reflexivity | reflexivity | reflexivity | exact HCS
                     | exact HIB | exact K | exact K2].
    + eapply ex_hdr; [exact INVm | exact HL | regs_ok | reflexivity | reflexivity | reflexivity | exact HCS
                     | exact HIB | exact K2].
Qed.

(** *** 0x14ea0: trim(buf) *)
Lemma at_ea0 : forall m sb (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 s8 t3 t4 t5 t6 : word),
  INV m -> (LEN < 512)%nat -> zs sb = r_strip_comment (pf_line s o) ->
  bytes_at rsegs m (Sp + 344) (sb ++ [ZERO]) ->
  evt rsegs POST (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 c) (Z_to_bv 64 35) a0 a1 a2 a3 a4 a5 a6 a7
      (Z_to_bv 64 (t + Z.of_nat (pf_next s o))) (Z_to_bv 64 (ln + 1)) (Z_to_bv 64 59) s5
      (Z_to_bv 64 (pf_cur_ptr c cur)) s7 s8 (Z_to_bv 64 512) (Z_to_bv 64 32) (Z_to_bv 64 9) t3 t4 t5 t6)
      F (Z_to_bv 64 0x14ea0) fc None m (seg_rom rsegs)).
Proof.
  intros m sb ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 s8 t3 t4 t5 t6 INVm HL ZS BY.
  pose proof INVm as (ENV & _).
  pose proof nums as (LO0 & DEP & SPH & AL & T0 & APt & TB & NZ & LN & TL).
  pose proof ENV as (_ & _ & _ & _ & _ & _ & (STK & _ & _ & NR) & MI & _). unfold PARSE_FILE_FRAME in STK, NR.
  pose proof (L_line_bytes_holds s o NZ) as (_ & NZl & _).
  assert (NZs : ~ In 0 (zs sb)).
  { rewrite ZS. destruct (L_strip_holds (pf_line s o) NZl) as (k & _ & E & _). rewrite E.
    intros Hin. apply NZl. rewrite <- (firstn_skipn k (pf_line s o)). apply in_or_app. left. exact Hin. }
  assert (LSB : (length sb <= LEN)%nat) by (rewrite <- p2_len_zs, ZS; apply r_strip_comment_len_le).
  pose proof (L_trim_holds (zs sb) NZs) as (TL1 & TL2 & TL3).
  rewrite p2_len_zs in TL1.
  zstep. zstep.
  eapply evt_cut.
  { eapply HTR with (lo := lo) (s := zs sb). rewrite unsigned_lit by lia. unfold trim_pre, TRIM_STACK.
    split; [lia|]. split; [eapply p2_cstr_of_frame; [exact BY | exact STK | lia | lia | exact NZs]|].
    split; [eapply p2_wr_of_stk; [exact STK | lia | rewrite p2_len_zs; lia | lia]|].
    split; [unfold apart; right; lia|].
    split; [|exact MI].
    split; [exact (proj1 (stk_split rsegs m lo Sp (Sp + 976) STK ltac:(lia)))|].
    split; [lia|]. split; [lia|]. intros a Ha. apply NR. lia. }
  intros ms' PO. unfold ret_post in PO.
  destruct PO as (u0 & u1 & u2 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & M3 & E & MU3 & WM3
                  & MI3 & ST3 & BY3).
  subst ms'. rewrite unsigned_lit in MU3, BY3 |- * by lia. fix_ret_pc.
  unfold trim_end_addr, TRIM_STACK in MU3.
  rewrite p2_zb_firstn in BY3.
  pose proof (bytes_at_bound _ _ _ _ BY3) as BB3.
  assert (STK3 : stk rsegs M3 lo (Sp + 976)).
  { pose proof (stk_split rsegs m lo Sp (Sp + 976) STK ltac:(lia)) as [_ SA].
    pose proof (stk_split rsegs m Sp (Sp + 344) (Sp + 976) SA ltac:(lia)) as [SB SC].
    pose proof (stk_split rsegs m (Sp + 344)
                  (Sp + 344 + Z.of_nat (trim_lead (zs sb) + length (r_trim (zs sb))) + 1) (Sp + 976) SC ltac:(lia))
      as [SD SE].
    eapply stk_merge; [exact ST3 | | lia].
    eapply stk_merge; [eapply stk_transport_disjoint; [exact SB | exact MU3 | exact WM3 | dj] | | lia].
    eapply stk_merge; [eapply p2_stk_bytes_upd; [exact SD | exact WM3 | exact BY3 | ]
                      | eapply stk_transport_disjoint; [exact SE | exact MU3 | exact WM3 | dj] | lia].
    rewrite length_app, length_firstn. cbn [length]. lia. }
  assert (INV3 : INV M3) by (eapply pinv_move; [exact INVm | lia | exact MU3 | exact WM3 | exact MI3 | exact STK3 | okw]).
  rewrite p2_firstn_add in BY3.
  set (rb := firstn (length (r_trim (zs sb))) (skipn (trim_lead (zs sb)) sb)) in BY3.
  assert (ZRB : zs rb = pf_tline s o).
  { unfold pf_tline. rewrite <- ZS. unfold rb. unfold zs in *. rewrite <- firstn_map, <- pfa_skipn_map.
    symmetry. exact TL2. }
  assert (LRB : length rb = length (r_trim (zs sb))).
  { rewrite <- p2_len_zs, ZRB. unfold pf_tline. rewrite <- ZS. reflexivity. }
  assert (LF : length (firstn (trim_lead (zs sb)) sb) = trim_lead (zs sb)) by (rewrite length_firstn; lia).
  rewrite <- app_assoc in BY3. apply bytes_at_app in BY3 as [_ BY4]. rewrite LF in BY4.
  eapply at_ea8; [exact INV3 | exact HL | exact ZRB | exact BY4 | lia | lia].
Qed.

(** *** 0x14e9c: buf[k] = 0 at the comment start k *)
Lemma pinv_store : forall m a, INV m -> Sp + 344 <= a < Sp + 856 ->
  INV (write_to_mem m (wa a) [ZERO]) /\ store_ok rsegs m (wa a) 1 = true.
Proof.
  intros m a INVm Ha.
  pose proof INVm as (ENV & _).
  pose proof ENV as (_ & _ & _ & _ & _ & _ & (STK & _) & MI & _).
  pose proof nums as (LO0 & DEP & SPH & _).
  unfold PARSE_FILE_FRAME in STK.
  assert (WR : wr_at rsegs m a 1) by (eapply p2_wr_of_stk; [exact STK | lia | lia | lia]).
  assert (SO : store_ok rsegs m (wa a) 1 = true).
  { pose proof (wr_at_store_ok rsegs m a 1 0 1 WR ltac:(lia) ltac:(lia)) as H. rewrite Z.add_0_r in H. exact H. }
  split; [|exact SO].
  eapply pinv_move; [exact INVm | lia | | | | | ].
  - apply (munch_write [(a, a + 1)] m m a [ZERO]); [apply munch_refl | lia | cbn [length]; lia | cbn [inside length]; lia].
  - apply wmono_write, wmono_refl.
  - apply mem_inv_store; [exact MI | exact SO].
  - apply stk_write; [exact STK | lia | cbn [length]; lia].
  - okw.
Qed.

Lemma at_e9c : forall m src k (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 s8 t3 t4 t5 t6 : word),
  INV m -> (LEN < 512)%nat -> zs src = pf_line s o ->
  bytes_at rsegs m (Sp + 344) (src ++ [ZERO]) -> (k <= length src)%nat ->
  r_strip_comment (pf_line s o) = firstn k (pf_line s o) -> s5 = Z_to_bv 64 (Sp + 344 + Z.of_nat k) ->
  evt rsegs POST (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 c) (Z_to_bv 64 35) a0 a1 a2 a3 a4 a5 a6 a7
      (Z_to_bv 64 (t + Z.of_nat (pf_next s o))) (Z_to_bv 64 (ln + 1)) (Z_to_bv 64 59) s5
      (Z_to_bv 64 (pf_cur_ptr c cur)) s7 s8 (Z_to_bv 64 512) (Z_to_bv 64 32) (Z_to_bv 64 9) t3 t4 t5 t6)
      F (Z_to_bv 64 0x14e9c) fc None m (seg_rom rsegs)).
Proof.
  intros m src k ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 s8 t3 t4 t5 t6 INVm HL ZS BY Hk SC E5. subst s5.
  assert (LS : length src = LEN) by (rewrite <- ZS; symmetry; apply p2_len_zs).
  pose proof nums as (LO0 & DEP & SPH & _).
  destruct (pinv_store m (Sp + 344 + Z.of_nat k) INVm ltac:(lia)) as [INV' SO].
  zstep.
  replace (le1 (Z_to_bv 64 0)) with [ZERO] by reflexivity.
  change (Z_to_bv 64 (bv_unsigned sp + 344 + Z.of_nat k)) with (wa (bv_unsigned sp + 344 + Z.of_nat k)).
  eapply at_ea0 with (sb := firstn k src); [exact INV' | exact HL | | apply p2_bytes_store_cut; [exact BY | exact Hk]].
  rewrite p2_zs_firstn, ZS, SC. reflexivity.
Qed.

(** *** 0x14e68: the strip_comment loop, k bytes of the line checked *)
Lemma loop : forall (j k : nat) m src (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 s8 t3 t4 t5 t6 : word),
  INV m -> (LEN < 512)%nat -> zs src = pf_line s o ->
  bytes_at rsegs m (Sp + 344) (src ++ [ZERO]) -> (k + j = length src)%nat ->
  (forall i, (i < k)%nat -> r_comment_at (pf_line s o) i = false) ->
  s5 = Z_to_bv 64 (Sp + 344 + Z.of_nat k) -> a0 = Z_to_bv 64 (- Z.of_nat k) ->
  evt rsegs POST (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 c) (Z_to_bv 64 35) a0 a1 a2 a3 a4 a5 a6 a7
      (Z_to_bv 64 (t + Z.of_nat (pf_next s o))) (Z_to_bv 64 (ln + 1)) (Z_to_bv 64 59) s5
      (Z_to_bv 64 (pf_cur_ptr c cur)) s7 s8 (Z_to_bv 64 512) (Z_to_bv 64 32) (Z_to_bv 64 9) t3 t4 t5 t6)
      F (Z_to_bv 64 0x14e68) fc None m (seg_rom rsegs)).
Proof.
  induction j as [|j IH];
    intros k m src ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 s8 t3 t4 t5 t6 INVm HL ZS BY Hkj NB E5 E0;
    subst s5 a0;
    pose proof nums as (LO0 & DEP & SPH & AL & T0 & APt & TB & NZ & LN & TL);
    pose proof (L_line_bytes_holds s o NZ) as (_ & NZl & _);
    assert (LS : length src = LEN) by (rewrite <- ZS; symmetry; apply p2_len_zs).
  - (* k = length src: the NUL, no comment in the line *)
    assert (Ek : k = length src) by lia. subst k.
    assert (RD : ov_read_bytes rsegs m (Z_to_bv 64 (Sp + 344 + Z.of_nat (length src))) 1 = Some [Z_to_bv 8 0]).
    { rewrite (p2_read_byte m (Sp + 344) src (length src) BY ltac:(lia)).
      rewrite nth_overflow by (rewrite p2_len_zs; lia). reflexivity. }
    zstep. zstep. if_cases K1; zify_cond K1; bnorm K1; [exfalso; lia|].
    zstep. if_cases K2; zify_cond K2; bnorm K2; [exfalso; lia|].
    zstep. if_cases K3; zify_cond K3; bnorm K3; [|exfalso; lia].
    eapply at_ea0 with (sb := src); [exact INVm | exact HL | | exact BY].
    rewrite ZS, (r_strip_comment_at (pf_line s o) (length src) NZl ltac:(lia) NB ltac:(intros; exfalso; lia)).
    rewrite LS, firstn_all. reflexivity.
  - (* k < length src *)
    assert (Hk : (k < length src)%nat) by lia.
    assert (Rb : 0 <= nth k (pf_line s o) 0 < 256) by (rewrite <- ZS; apply p2_zs_range).
    assert (Bnz : nth k (pf_line s o) 0 <> 0).
    { intros E. apply NZl. rewrite <- E. apply nth_In. lia. }
    assert (ADV : forall (x10 x11 x21 : word), r_comment_at (pf_line s o) k = false ->
      x21 = Z_to_bv 64 (Sp + 344 + Z.of_nat k) -> x10 = Z_to_bv 64 (- Z.of_nat k) ->
      evt rsegs POST (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 c) (Z_to_bv 64 35) x10 x11 a2 a3 a4 a5 a6 a7
        (Z_to_bv 64 (t + Z.of_nat (pf_next s o))) (Z_to_bv 64 (ln + 1)) (Z_to_bv 64 59) x21
        (Z_to_bv 64 (pf_cur_ptr c cur)) s7 s8 (Z_to_bv 64 512) (Z_to_bv 64 32) (Z_to_bv 64 9) t3 t4 t5 t6)
        F (Z_to_bv 64 0x14e8c) fc None m (seg_rom rsegs))).
    { intros x10 x11 x21 C E21 E10. subst x10 x21.
      zstep. zstep. zstep.
      eapply (IH (S k)); [exact INVm | exact HL | exact ZS | exact BY | lia | | weq | weq].
      intros i Hi. destruct (Nat.eq_dec i k) as [->|Ne]; [exact C | apply NB; lia]. }
    assert (MARK : forall (x11 : word), is_mark (nth k (pf_line s o) 0) = true ->
      evt rsegs POST (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 c) (Z_to_bv 64 35) (Z_to_bv 64 (- Z.of_nat k)) x11
        a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (t + Z.of_nat (pf_next s o))) (Z_to_bv 64 (ln + 1)) (Z_to_bv 64 59)
        (Z_to_bv 64 (Sp + 344 + Z.of_nat k)) (Z_to_bv 64 (pf_cur_ptr c cur)) s7 s8 (Z_to_bv 64 512)
        (Z_to_bv 64 32) (Z_to_bv 64 9) t3 t4 t5 t6)
        F (Z_to_bv 64 0x14e7c) fc None m (seg_rom rsegs))).
    { intros x11 MK.
      zstep. if_cases K; zify_cond K.
      - (* k = 0: the mark opens the line *)
        assert (Ek : k = 0%nat) by lia. subst k.
        zstep. eapply at_e9c with (k := 0%nat); [exact INVm | exact HL | exact ZS | exact BY | lia | | weq].
        apply r_strip_comment_at; [exact NZl | lia | intros; exfalso; lia | intros _].
        unfold r_comment_at. rewrite MK. reflexivity.
      - assert (Kp : (0 < k)%nat) by lia.
        assert (Rp : 0 <= nth (k - 1) (pf_line s o) 0 < 256) by (rewrite <- ZS; apply p2_zs_range).
        assert (RD2 : ov_read_bytes rsegs m (Z_to_bv 64 (Sp + 344 + Z.of_nat k + -1)) 1
                      = Some [Z_to_bv 8 (nth (k - 1) (pf_line s o) 0)]).
        { replace (Sp + 344 + Z.of_nat k + -1) with (Sp + 344 + Z.of_nat (k - 1)) by lia.
          rewrite <- ZS. apply p2_read_byte; [exact BY | lia]. }
        zstep. zstep. if_cases K2; zify_cond K2; bnorm K2.
        + eapply at_e9c with (k := k); [exact INVm | exact HL | exact ZS | exact BY | lia | | weq].
          apply r_strip_comment_at; [exact NZl | lia | exact NB | intros _].
          unfold r_comment_at. rewrite MK, K2. destruct (k =? 0)%nat; reflexivity.
        + zstep. if_cases K3; zify_cond K3; bnorm K3.
          * eapply at_e9c with (k := k); [exact INVm | exact HL | exact ZS | exact BY | lia | | weq].
            apply r_strip_comment_at; [exact NZl | lia | exact NB | intros _].
            unfold r_comment_at. rewrite MK, K3. destruct (k =? 0)%nat; reflexivity.
          * eapply ADV; [| weq | weq].
            unfold r_comment_at. rewrite MK. replace (k =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
            unfold sp_tab. rewrite (proj2 (Z.eqb_neq _ _) K2), (proj2 (Z.eqb_neq _ _) K3). reflexivity. }
    assert (RD : ov_read_bytes rsegs m (Z_to_bv 64 (Sp + 344 + Z.of_nat k)) 1
                 = Some [Z_to_bv 8 (nth k (pf_line s o) 0)]).
    { rewrite <- ZS. apply p2_read_byte; [exact BY | lia]. }
    zstep. zstep. if_cases K1; zify_cond K1; bnorm K1.
    + apply MARK. unfold is_mark. rewrite K1. reflexivity.
    + zstep. if_cases K2; zify_cond K2; bnorm K2.
      * apply MARK. unfold is_mark. rewrite K2. reflexivity.
      * zstep. if_cases K3; zify_cond K3; bnorm K3; [exfalso; exact (Bnz K3)|].
        zstep. eapply ADV; [| weq | weq].
        unfold r_comment_at, is_mark. rewrite (proj2 (Z.eqb_neq _ _) K1), (proj2 (Z.eqb_neq _ _) K2). reflexivity.
Qed.

(** *** 0x14e48: memcpy(buf, p, len), buf[len] = 0, then the loop *)
Lemma at_e48 : forall m (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 t3 t4 t5 t6 : word),
  INV m -> (LEN < 512)%nat ->
  evt rsegs POST (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 c) (Z_to_bv 64 35) a0 a1 a2 a3 a4 a5 a6 a7
      (Z_to_bv 64 (t + Z.of_nat (pf_next s o))) (Z_to_bv 64 (ln + 1)) (Z_to_bv 64 59) s5
      (Z_to_bv 64 (pf_cur_ptr c cur)) (Z_to_bv 64 (t + Z.of_nat o)) (Z_to_bv 64 (Z.of_nat LEN))
      (Z_to_bv 64 512) (Z_to_bv 64 32) (Z_to_bv 64 9) t3 t4 t5 t6)
      F (Z_to_bv 64 0x14e48) fc None m (seg_rom rsegs)).
Proof.
  intros m ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 t3 t4 t5 t6 INVm HL.
  pose proof INVm as (ENV & TXT & SPL & CS & ST & MU & WM).
  pose proof nums as (LO0 & DEP & SPH & AL & T0 & APt & TB & NZ & LN & TL).
  pose proof ENV as (_ & _ & _ & _ & _ & _ & (STK & _) & MI & _). unfold PARSE_FILE_FRAME in STK.
  destruct CS as (bs & sl & BYt & ZSt & NZt & SLt).
  assert (Lbs : length bs = length (skipn o s)) by (rewrite <- ZSt; symmetry; apply p2_len_zs).
  pose proof (pf_line_len_le s o) as LL. pose proof (pfa_len_skipn o s) as LSK.
  pose proof (L_line_bytes_holds s o NZ) as (LB1 & _ & _).
  set (src := firstn LEN bs).
  assert (Lsrc : length src = LEN) by (unfold src; rewrite length_firstn; lia).
  assert (ZSrc : zs src = pf_line s o) by (unfold src; rewrite p2_zs_firstn, ZSt; symmetry; exact LB1).
  assert (BYs : bytes_at rsegs m (t + Z.of_nat o) src).
  { unfold src. rewrite <- (firstn_skipn LEN bs), <- app_assoc in BYt. apply bytes_at_app in BYt as [B _]. exact B. }
  pose proof (stk_split rsegs m lo (Sp + 344) (Sp + 976) STK ltac:(lia)) as [SL0 SR0].
  pose proof (stk_split rsegs m (Sp + 344) (Sp + 344 + Z.of_nat LEN) (Sp + 976) SR0 ltac:(lia)) as [SM0 SH0].
  destruct (stk_carve rsegs m (Sp + 344) (Sp + 344 + Z.of_nat LEN) LEN SM0 ltac:(lia)) as [_ [junk RWj]].
  replace (Sp + 344 + Z.of_nat LEN - Z.of_nat LEN) with (Sp + 344) in RWj by lia.
  zstep. zstep. zstep. zstep. zstep.
  eapply evt_cut.
  { eapply HMC with (src := src) (junk := junk); rewrite ?unsigned_lit by lia.
    - exact BYs.
    - rewrite Nat2Z.id. exact Lsrc.
    - rewrite Nat2Z.id. exact RWj.
    - lia.
    - exact MI. }
  intros ms' PO. unfold memcpy_post in PO.
  destruct PO as (u0 & u1 & u2 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & M1 & E & MU1 & WM1
                  & MI1 & RW1 & BY1).
  subst ms'. rewrite ?unsigned_lit in MU1, RW1 by lia. rewrite Nat2Z.id in RW1. fix_ret_pc.
  destruct RW1 as [[_ BR] _]. cbn [cells_bytes cbytes] in BR. rewrite app_nil_r in BR.
  assert (STK1 : stk rsegs M1 lo (Sp + 976)).
  { eapply stk_merge; [eapply stk_transport_disjoint; [exact SL0 | exact MU1 | exact WM1 | dj] | | lia].
    eapply stk_merge; [eapply p2_stk_bytes_upd; [exact SM0 | exact WM1 | exact BR | rewrite Lsrc; lia]
                      | eapply stk_transport_disjoint; [exact SH0 | exact MU1 | exact WM1 | dj] | lia]. }
  assert (INV1 : INV M1) by (eapply pinv_move; [exact INVm | lia | exact MU1 | exact WM1 | exact MI1 | exact STK1 | okw]).
  zstep. zstep.
  destruct (pinv_store M1 (Sp + 344 + Z.of_nat LEN) INV1 ltac:(lia)) as [INV2 SO].
  zstep.
  replace (le1 (Z_to_bv 64 0)) with [ZERO] by reflexivity.
  change (Z_to_bv 64 (bv_unsigned sp + 344 + Z.of_nat LEN)) with (wa (bv_unsigned sp + 344 + Z.of_nat LEN)).
  eapply (loop (length src) 0); [exact INV2 | exact HL | exact ZSrc | | lia | intros; exfalso; lia | weq | weq].
  rewrite <- Lsrc. apply p2_bytes_store_end; [exact BR | lia].
Qed.

(** *** 0x14e00: lineno++, then the length test *)
Lemma at_e00 : forall m (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s7 s8 t3 t4 t5 t6 : word),
  INV m -> s2 = Z_to_bv 64 (t + Z.of_nat (pf_next s o)) -> s7 = Z_to_bv 64 (t + Z.of_nat o) ->
  s8 = Z_to_bv 64 (Z.of_nat LEN) ->
  evt rsegs POST (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 c) (Z_to_bv 64 35) a0 a1 a2 a3 a4 a5 a6 a7
      s2 (Z_to_bv 64 ln) (Z_to_bv 64 59) s5 (Z_to_bv 64 (pf_cur_ptr c cur)) s7 s8
      (Z_to_bv 64 512) (Z_to_bv 64 32) (Z_to_bv 64 9) t3 t4 t5 t6)
      F (Z_to_bv 64 0x14e00) fc None m (seg_rom rsegs)).
Proof.
  intros m ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s7 s8 t3 t4 t5 t6 INVm E2 E7 E8. subst s2 s7 s8.
  pose proof nums as (LO0 & DEP & SPH & AL & T0 & APt & TB & NZ & LN & TL).
  pose proof (pf_line_len_le s o) as LL. pose proof (pfa_len_skipn o s) as LSK.
  assert (LB : 0 <= Z.of_nat LEN < 65536) by lia.
  zstep.
  rewrite (p2_swrap1 ln) by lia.
  zstep. if_cases K; zify_cond K.
  - eapply at_e48; [exact INVm | lia].
  - eapply ex_long; [exact INVm | lia | regs_ok | reflexivity | reflexivity | reflexivity | reflexivity].
Qed.

(** *** HEAD 0x14dc4: strchr(p, '\n'), or strlen(p) when the line ends the text *)
Lemma head : forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
  pf_regs s0 s1 s2 s3 s4 s10 s11 c (t + Z.of_nat o) ln -> s9 = Z_to_bv 64 512 -> s6 = Z_to_bv 64 (pf_cur_ptr c cur) ->
  evt rsegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 PF_PC_HEAD) fc None m0 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (E0 & E2 & E3 & E1 & E4 & E10 & E11) E9 E6. subst s0 s1 s2 s3 s4 s6 s9 s10 s11.
  pose proof inv0 as INV0.
  pose proof INV0 as (ENV & TXT & SPL & CS & ST & MU & WM).
  pose proof nums as (LO0 & DEP & SPH & AL & T0 & APt & TB & NZ & LN & TL).
  pose proof ENV as (_ & _ & _ & _ & _ & _ & (STK & _) & MI & _). unfold PARSE_FILE_FRAME in STK.
  destruct CS as (bs0 & sl0 & BY0 & ZSt & NZt & SL0).
  assert (Lbs : length bs0 = length (skipn o s)) by (rewrite <- ZSt; symmetry; apply p2_len_zs).
  pose proof (pfa_len_skipn o s) as LSK. pose proof (pf_line_len_le s o) as LL.
  rewrite <- Lbs in SL0.
  destruct (p2_slack_cut _ _ _ _ BY0 SL0) as (sl & BY & SL7 & SL8). clear BY0 SL0.
  assert (NZB : ~ In ZERO bs0) by (apply nul_free_bytes; rewrite ZSt; exact NZt).
  pose proof (stk_split rsegs m0 lo Sp (Sp + 976) STK ltac:(lia)) as [SLo SHi].
  destruct (L_next_holds s o Ho) as (Hsk & Hgt & Hle & Hnx).
  unfold PF_PC_HEAD.
  zstep. zstep. zstep. zstep.
  eapply evt_cut.
  { eapply HSC with (str := bs0) (slack := sl) (lo := lo); rewrite ?unsigned_lit by lia.
    - exact SLo.
    - exact BY.
    - exact NZB.
    - exact SL8.
    - exact MI.
    - lia.
    - lia. }
  intros ms' PO. unfold strchr_post in PO.
  destruct PO as (u0 & u1 & u2 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & M1 & E & MU1 & WM1
                  & MI1 & ST1 & BY1).
  subst ms'. rewrite (unsigned_lit (t + Z.of_nat o)) in BY1 by lia. fix_ret_pc.
  assert (STK1 : stk rsegs M1 lo (Sp + 976)).
  { eapply stk_merge; [exact ST1 | eapply stk_transport_disjoint; [exact SHi | exact MU1 | exact WM1 | dj] | lia]. }
  assert (INV1 : INV M1) by (eapply pinv_move; [exact INV0 | lia | exact MU1 | exact WM1 | exact MI1 | exact STK1 | okw]).
  rewrite (unsigned_lit (t + Z.of_nat o)) by lia. rewrite (unsigned_lit 10) by lia.
  change (10 mod 256) with 10.
  rewrite (bridge_strchr (t + Z.of_nat o) 10 bs0 NZB ltac:(lia)).
  rewrite ZSt.
  destruct (L_break_nl_holds (skipn o s) NZt) as [[SC SPL'] | [SC [F1 F2]]].
  - (* a '\n' ends the line: nl = p + len *)
    change (fst (break_nl (skipn o s))) with (pf_line s o) in SC, SPL'. rewrite SC. cbv iota.
    assert (LT : (o + LEN < length s)%nat).
    { pose proof (f_equal (@length Z) SPL') as L. rewrite length_app in L. cbn [length] in L. lia. }
    rewrite (proj2 (Nat.ltb_lt _ _) LT) in Hnx. cbv iota in Hnx.
    zstep. zstep. if_cases K; zify_cond K; [exfalso; lia|].
    zstep. zstep. if_cases K2; zify_cond K2; [exfalso; lia|].
    zstep. zstep.
    eapply at_e00; [exact INV1 | weq | reflexivity | weq].
  - (* no '\n': the line is the rest, len = strlen(p), p' = p + len *)
    change (fst (break_nl (skipn o s))) with (pf_line s o) in F1. rewrite SC. cbv iota.
    assert (GE : (length s <= o + LEN)%nat) by (rewrite F1; lia).
    rewrite (proj2 (Nat.ltb_ge _ _) GE) in Hnx. cbv iota in Hnx.
    zstep. zstep. if_cases K; zify_cond K; [|exfalso; lia].
    zstep. zstep.
    eapply evt_cut.
    { eapply HSL with (str := bs0) (slack := sl); rewrite ?unsigned_lit by lia;
        [exact BY1 | exact NZB | exact SL8 | exact MI1]. }
    intros ms' PO. unfold strlen_post in PO.
    destruct PO as (w0 & w1 & w2 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & w3 & w4 & w5 & w6 & M2 & E & MU2 & WM2
                    & MI2 & BY2).
    subst ms'. fix_ret_pc.
    assert (STK2 : stk rsegs M2 lo (Sp + 976)) by (eapply stk_transport_disjoint; [exact STK1 | exact MU2 | exact WM2 | exact I]).
    assert (INV2 : INV M2)
      by (eapply pinv_move; [exact INV1 | lia | exact MU2 | exact WM2 | exact MI2 | exact STK2 | apply Forall_nil]).
    zstep. zstep. if_cases K2; zify_cond K2; [exfalso; lia|].
    zstep.
    eapply at_e00; [exact INV2 | | reflexivity | ]; rewrite F1 in *; weq.
Qed.

End Walk.

(** ** TAIL -> HEAD (pred n) or DONE *)
Lemma tail_holds : forall n, H_HEAD (pred n) -> H_DONE -> H_TAIL n.
Proof.
  intros n HH HD. unfold H_TAIL.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo v c t s rc cur nm o ln d HC HS Hlt HR H9 H6.
  pose proof HC as (ENV & TXT & SPL & LC & CS).
  destruct HR as (E0 & E2 & E3 & E1 & E4 & E10 & E11). subst s0 s1 s2 s3 s4 s6 s9 s10 s11.
  pose proof CS as (bs & sl & BY & ZS & NZ & SLK).
  pose proof (bytes_at_bound _ _ _ _ BY) as BB. rewrite length_app in BB. cbn [length] in BB.
  assert (RG : 0 <= hd0 (skipn o s) < 256) by (rewrite <- p2_hd0_nth, <- ZS; apply p2_zs_range).
  assert (RD : ov_read_bytes rsegs m (Z_to_bv 64 (t + Z.of_nat o)) 1 = Some [Z_to_bv 8 (hd0 (skipn o s))]).
  { replace (Z_to_bv 64 (t + Z.of_nat o)) with (wa (t + Z.of_nat o + 0)) by (unfold wa; f_equal; lia).
    rewrite (bytes_at_read rsegs m _ _ 0 1 BY) by (try rewrite length_app; cbn [length]; lia).
    change (Z.to_nat 0) with 0%nat. cbn [skipn]. rewrite <- ZS.
    destruct bs as [|b bs']; cbn [firstn app zs map hd0]; [reflexivity|]. rewrite p2_zb8. reflexivity. }
  zstep. zstep. if_cases K; zify_cond K; bnorm K.
  - (* a byte left: the next line *)
    assert (Ho : (o < length s)%nat).
    { destruct (Nat.lt_ge_cases o (length s)) as [H|H]; [exact H|].
      exfalso. apply K. pose proof (pfa_len_skipn o s) as L. revert L.
      destruct (skipn o s) as [|x r]; intros L; [reflexivity|]. cbn [length] in L. lia. }
    eapply HH; [exact HC | exact HS | exact Ho | lia | regs_ok | reflexivity | reflexivity].
  - (* the text's NUL: DONE *)
    assert (E : skipn o s = []).
    { destruct (skipn o s) as [|x r] eqn:Ex; [reflexivity|]. exfalso.
      try rewrite Ex in K. try rewrite Ex in NZ.
      cbn [hd0] in K. subst x. apply NZ. left. reflexivity. }
    rewrite E. zstep.
    change (r_lines (rc, cur, nm) ln (lines [])) with (rc, cur, nm). unfold pf_fin. cbn [fst].
    eapply HD; [exact ENV | exact (proj1 HS) |].
    unfold pf_spill in SPL.
    do 5 apply p2_saved_tl in SPL. apply p2_saved_hd in SPL.
    replace (bv_unsigned sp + PF_NSLOT) with (bv_unsigned sp + 8 + 8 + 8 + 8 + 8 + 8) by (unfold PF_NSLOT; lia).
    exact SPL.
Qed.

Theorem pf_p2_holds : strchr_contract -> strlen_contract -> memcpy_contract -> trim_contract -> S_P2.
Proof.
  intros HSC HSL HMC HTR n. split.
  - intros HL HH HK HT. unfold H_HEAD.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      F fc m lo v c t s rc cur nm o ln d HC HS Ho Hn HR H9 H6.
    eapply head; eassumption.
  - apply tail_holds.
Qed.
