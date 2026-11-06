From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes MState.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts CommandModel CommandFP SlotSpec
  SlotRuns check_reply_c check_arity_c check_reply_answer_c rec_shape_of_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require SlotWords SlotWordsRun strspn_c strcspn_c memcpy_c
  KindB send_message hand_back SlotEnd SlotRec HarnessPropsProof RecAns.
Import ListNotations.
Local Open Scope Z_scope.

(* The Kind A part of one message from the third malloc's return (0x141c8) to check_words' entry (0x14980): the
   splitter (SlotWordsRun.sw_run), check_reply, 0x142cc .. check_arity, check_arity, 0x142d4 .. check_words. *)

Lemma b2_tb : forall W m m' a bs, munch W m m' -> bytes_at rsegs m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> Frame.outside W (a + i)) -> bytes_at rsegs m' a bs.
Proof.
  intros W m m' a bs MU H HO. pose proof H as (H0 & H1 & _).
  apply (KindB.bytes_at_transfer rsegs m m' a bs H). intros i Hi.
  exact (KindB.munch_mbyte rsegs W m m' (a + i) MU ltac:(lia) (HO i Hi)).
Qed.

Lemma b2_cells : forall W m m' a cs, munch W m m' -> rw_cells rsegs m a cs ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> Frame.outside W (a + i)) -> rw_cells rsegs m' a cs.
Proof.
  intros W m m' a cs MU H HO. pose proof (Cells.cells_at_bound rsegs m a cs (proj1 H)) as [H0 H1].
  apply (KindB.rw_cells_transfer rsegs m m' a cs H). intros i Hi.
  split; [exact (KindB.munch_mbyte rsegs W m m' (a + i) MU ltac:(lia) (HO i Hi))|].
  intros Hw. exact (proj1 (KindB.munch_writable rsegs W m m' (a + i) MU ltac:(lia) (HO i Hi)) Hw).
Qed.

Lemma b2_out1 : forall lo hi x, x < lo \/ hi <= x -> Frame.outside [(lo, hi)] x.
Proof. intros lo hi x H. cbn. split; [lia | exact Logic.I]. Qed.

Lemma b2_cells_bytes : forall m a cs, rw_cells rsegs m a cs -> bytes_at rsegs m a (cells_bytes cs).
Proof. intros m a cs [[_ H] _]. exact H. Qed.

Lemma b2_munch : forall Wa Wb Wc m m' m'', munch Wa m m' -> munch Wb m' m'' ->
  (forall x, Frame.outside Wc x -> Frame.outside Wa x /\ Frame.outside Wb x) -> munch Wc m m''.
Proof.
  intros Wa Wb Wc m m' m'' Ha Hb H x Hx. destruct (H _ Hx) as [H1 H2]. rewrite (Hb x H2), (Ha x H1). reflexivity.
Qed.

Lemma b2_le8_nth : forall (wp : list Z) k p, nth_error wp k = Some p ->
  firstn 8 (skipn (8 * k) (concat (map (fun q => le8 (Z_to_bv 64 q)) wp))) = le8 (Z_to_bv 64 p).
Proof.
  induction wp as [|q wp IH]; intros [|k] p H; cbn in H; try discriminate.
  - injection H as <-. cbn [map concat]. rewrite Nat.mul_0_r, skipn_O, firstn_app, length_le8, Nat.sub_diag, firstn_O,
      app_nil_r. apply firstn_all2. rewrite length_le8. lia.
  - cbn [map concat]. replace (8 * S k)%nat with (8 + 8 * k)%nat by lia.
    rewrite skipn_app, length_le8, skipn_all2 by (rewrite length_le8; lia).
    replace (8 + 8 * k - 8)%nat with (8 * k)%nat by lia. cbn [app]. exact (IH k p H).
Qed.

Lemma b2_firstn_ptr : forall (Aa : list byte) (wp : list Z) k p,
  firstn (8 * length wp) Aa = concat (map (fun q => le8 (Z_to_bv 64 q)) wp) -> nth_error wp k = Some p ->
  firstn 8 (skipn (8 * k) Aa) = le8 (Z_to_bv 64 p).
Proof.
  intros Aa wp k p H E. assert (Hk : (k < length wp)%nat) by (apply nth_error_Some; rewrite E; discriminate).
  rewrite <- (b2_le8_nth wp k p E), <- H. rewrite !firstn_skipn_comm, firstn_firstn.
  replace (Init.Nat.min (8 * k + 8) (8 * length wp)) with (8 * k + 8)%nat by lia. reflexivity.
Qed.

Lemma b2_sub : forall m a (C X : list byte) k, bytes_at rsegs m a C -> (k + length X <= length C)%nat ->
  firstn (length X) (skipn k C) = X -> bytes_at rsegs m (a + Z.of_nat k) X.
Proof.
  intros m a C X k H Hl E.
  pose proof (RecAns.bytes_at_firstn_skipn rsegs m a C k H) as [_ H2]. rewrite length_firstn in H2.
  replace (Init.Nat.min k (length C)) with k in H2 by lia.
  pose proof (RecAns.bytes_at_firstn_skipn rsegs m (a + Z.of_nat k) (skipn k C) (length X) H2) as [H3 _].
  rewrite E in H3. exact H3.
Qed.

Lemma b2_upto_len : forall M, (length (Verbs.line M) <= length M)%nat.
Proof.
  intros M. pose proof (SlotRec.line_len M) as H1.
  pose proof (f_equal (@length byte) (SlotWords.sw_upto_prefix (fun b => bv_unsigned b =? 0) M)) as H2.
  rewrite length_firstn in H2. unfold Verbs.upto0 in H1. lia.
Qed.

Lemma b2_round : forall e c, e <= c -> e + (- e) mod 8 <= 8 * ((c + 7) / 8).
Proof. intros e c H. Z.div_mod_to_equations. lia. Qed.

Lemma b2_r8 : forall c t, c <= t -> t mod 8 = 0 -> 8 * ((c + 7) / 8) <= t.
Proof. intros c t H1 H2. Z.div_mod_to_equations. lia. Qed.

Lemma b2_r8_ge : forall c, c <= 8 * ((c + 7) / 8).
Proof. intros c. Z.div_mod_to_equations. lia. Qed.

Lemma b2_arr_bound : forall k nw L, (k < nw)%nat -> (2 * nw <= L + 1)%nat ->
  (8 * k + 8 <= Z.to_nat (8 * (Z.of_nat L / 2) + 16))%nat.
Proof. intros k nw L H1 H2. Z.div_mod_to_equations. lia. Qed.

Lemma b2_nth {X : Type} (l : list X) n x d : nth_error l n = Some x -> nth n l d = x.
Proof.
  revert n. induction l as [|y l IH]; intros [|n] H; cbn in H |- *; try discriminate;
    [injection H as <-; reflexivity | exact (IH n H)].
Qed.

(* The state at check_words' entry (pc 0x14980, returning to 0x142dc) after the splitter, check_reply and
   check_arity: the words of the message's line in copy, their addresses in arr, the struct words at sp + 40. *)
Definition w_post (sp gp tp s2 s3 s6 s8 : word) (m0 : word -> option byte) (lo src len text copy arr : Z)
    (M : list byte) : machine_state -> Prop := fun ms' =>
  exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (Ft : bvmap 5 word) (fc' : bv 32) m' T C Aa
    (wp : list Z) jsv' jp,
    ms' = MS (mkR (Z_to_bv 64 0x142dc) sp gp tp t0' t1' t2' (Z_to_bv 64 src) (Z_to_bv 64 len)
                  (Z_to_bv 64 (bv_unsigned sp + 40)) a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 (Z_to_bv 64 text) (Z_to_bv 64 copy) s6 (Z_to_bv 64 (bv_unsigned s8 - len)) s8
                  (Z_to_bv 64 MASK) (Z_to_bv 64 arr) (Z_to_bv 64 32) t3' t4' t5' t6')
             Ft (Z_to_bv 64 0x14980) fc' None m' (seg_rom rsegs) /\
    munch [(text, text + strnlen_res len M + 1); (copy, copy + strnlen_res len M + 1);
           (arr, arr + arr_size (strnlen_res len M)); (lo, bv_unsigned sp + 72)] m0 m' /\
    wmono rsegs m0 m' /\ mem_inv rsegs m' /\ frm0 fc' /\
    rw_cells rsegs m' (bv_unsigned sp) (LOC0 jsv') /\
    rw_cells rsegs m' (bv_unsigned sp + 40)
      [C8 (Z_to_bv 64 text); C8 (Z_to_bv 64 copy); C8 (Z_to_bv 64 arr);
       C4 (Z_to_bv 64 (Z.of_nat (length (Verbs.words (Verbs.line M))))); CB 4 jp] /\
    rw_cells rsegs m' text [CB (Z.to_nat (strnlen_res len M + 1)) T] /\
    rw_cells rsegs m' copy [CB (Z.to_nat (strnlen_res len M + 1)) C] /\
    rw_cells rsegs m' arr [CB (Z.to_nat (arr_size (strnlen_res len M))) Aa] /\
    length wp = length (Verbs.words (Verbs.line M)) /\
    firstn (8 * length (Verbs.words (Verbs.line M))) Aa = concat (map (fun p => le8 (Z_to_bv 64 p)) wp) /\
    (forall k p w, nth_error wp k = Some p -> nth_error (Verbs.words (Verbs.line M)) k = Some w ->
       copy <= p /\ p + Z.of_nat (length w) + 1 <= copy + strnlen_res len M + 1 /\
       firstn (length w + 1) (skipn (Z.to_nat (p - copy)) C) = w ++ [Z_to_bv 8 0]).

(* From check_reply's entry (the splitter's post SlotWords.sw_post, pc 0x14404, ra 0x142cc) to check_words' entry:
   check_reply, 0x142cc .. check_arity, check_arity, 0x142d4 .. check_words. The premises are those of Section W
   below but the splitter's three callee contracts. *)
Definition ck_spec : Prop :=
  forall (sp gp tp s2 s3 s6 s8 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
    (lo src len text copy arr : Z) (M : list byte) (can ans rep : word) (xr slack xa : list byte) (nc fn0 q : Z),
  let L0w := strnlen_res len M in
  let ws := Verbs.words (Verbs.line M) in
  let W0 := [(text, text + L0w + 1); (copy, copy + L0w + 1); (arr, arr + arr_size L0w);
             (bv_unsigned sp - 96, bv_unsigned sp + 72)] in
  0x54cb8 <= lo -> lo + 6000 <= bv_unsigned sp -> bv_unsigned sp + 176 <= 2 ^ 63 ->
  bv_unsigned sp + 176 <= TASK_SIZE ->
  0 <= len <= 8192 -> 0 <= src /\ src + len <= lo -> 0 <= L0w <= len ->
  0 < text /\ text + L0w + 1 <= lo -> 0 < copy /\ copy + L0w + 1 <= lo -> 0 < arr /\ arr + arr_size L0w <= lo ->
  arr_size L0w = 8 * (L0w / 2) + 16 ->
  check_reply_contract -> check_arity_contract ->
  Z.of_nat (length M) = len ->
  text + L0w + 1 <= 0x10000 \/ 0x54cb8 <= text ->
  copy + L0w + 1 <= 0x10000 \/ 0x54cb8 <= copy ->
  arr + arr_size L0w <= 0x10000 \/ 0x54cb8 <= arr ->
  text + L0w + 1 <= copy \/ copy + L0w + 1 <= text ->
  arr + arr_size L0w <= text \/ text + L0w + 1 <= arr ->
  arr + arr_size L0w <= copy \/ copy + L0w + 1 <= arr ->
  src + len <= text \/ text + L0w + 1 <= src ->
  text mod 8 = 0 /\ arr mod 8 = 0 /\ lo mod 8 = 0 ->
  frm0 fc ->
  MemNorm.task_mem rsegs m0 ->
  rw_cells rsegs m0 GOT_GUARD [C8 (Z_to_bv 64 GUARD)] ->
  rw_cells rsegs m0 GUARD [C8 can] ->
  (forall a, copy + L0w + 1 <= a < 8 * ((copy + L0w + 1 + 7) / 8) -> mbyte rsegs m0 a <> None) ->
  bytes_at rsegs m0 GOT_GREC (le8 (Z_to_bv 64 G_REC)) ->
  bytes_at rsegs m0 (G_REC + REC_ANSWER) (le8 ans) ->
  bytes_at rsegs m0 (G_REC + REC_NREPLIES) (le4 (Z_to_bv 64 1)) ->
  bytes_at rsegs m0 (G_REC + REC_REPLY) (le8 rep) ->
  bytes_at rsegs m0 (G_REC + REC_REPLY_SIZE) (le8 (Z_to_bv 64 (Z.of_nat (length xr) + 1))) ->
  bytes_at rsegs m0 G_SHAPES g_shapes_bytes ->
  bv_unsigned rep <> 0 ->
  bytes_at rsegs m0 (bv_unsigned rep) (xr ++ NUL :: slack) ->
  ~ In NUL xr ->
  (- (bv_unsigned rep + Z.of_nat (length xr) + 1)) mod 8 <= Z.of_nat (length slack) ->
  (forall i, 0 <= i < Z.of_nat (length xr) + 1 + Z.of_nat (length slack) ->
     Frame.outside W0 (bv_unsigned rep + i) /\ bv_unsigned rep + i < lo) ->
  (bv_unsigned ans <> 0 -> cstr_at m0 (bv_unsigned ans) xa /\
     forall i, 0 <= i < Z.of_nat (length xa) + 1 -> Frame.outside W0 (bv_unsigned ans + i) /\ bv_unsigned ans + i < lo) ->
  answer_ok ans xr xa (Z.of_nat (length ws)) (nth 0 ws []) ->
  reply_ok (Z.of_nat (length ws)) (nth 0 ws []) xr ->
  bytes_at rsegs m0 G_PARSED g_parsed_bytes ->
  0 <= nc <= 16 /\ bytes_at rsegs m0 (G_REC + REC_NCALLS) (le4 (Z_to_bv 64 nc)) ->
  (0 < nc -> 0 <= fn0 < 26 /\ bytes_at rsegs m0 (G_REC + REC_CALLS + CALL_FN) (le4 (Z_to_bv 64 fn0))) ->
  bytes_at rsegs m0 GOT_GQUIT (le8 (Z_to_bv 64 G_QUIT)) ->
  0 <= q < 2 ^ 32 /\ bytes_at rsegs m0 G_QUIT (le4 (Z_to_bv 64 q)) ->
  arity_ok (Z.of_nat (length ws)) (nth 0 ws []) q nc fn0 ->
  forall ms, SlotWords.sw_post sp gp tp s2 s3 s6 s8 F fc m0 lo src len text copy arr M ms ->
  evt rsegs (w_post sp gp tp s2 s3 s6 s8 m0 lo src len text copy arr M) ms.

Section W.
Variables (sp gp tp s2 s3 s6 s8 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
  (lo src len text copy arr : Z) (M : list byte) (can : word).

Notation SP := (bv_unsigned sp).
Notation L0w := (strnlen_res len M).
Notation ws := (Verbs.words (Verbs.line M)).
Notation W0 := [(text, text + strnlen_res len M + 1); (copy, copy + strnlen_res len M + 1);
                (arr, arr + arr_size (strnlen_res len M)); (bv_unsigned sp - 96, bv_unsigned sp + 72)].
Notation W1 := [(text, text + strnlen_res len M + 1); (copy, copy + strnlen_res len M + 1);
                (arr, arr + arr_size (strnlen_res len M)); (lo, bv_unsigned sp + 72)].

Hypothesis H_lo : 0x54cb8 <= lo.
Hypothesis H_LOS : lo + 6000 <= SP.
Hypothesis H_SPH : SP + 176 <= 2 ^ 63.
Hypothesis H_TS : SP + 176 <= TASK_SIZE.
Hypothesis H_len : 0 <= len <= 8192.
Hypothesis H_src : 0 <= src /\ src + len <= lo.
Hypothesis H_L0 : 0 <= L0w <= len.
Hypothesis H_tx : 0 < text /\ text + L0w + 1 <= lo.
Hypothesis H_cp : 0 < copy /\ copy + L0w + 1 <= lo.
Hypothesis H_ar : 0 < arr /\ arr + arr_size L0w <= lo.
Hypothesis H_AS : arr_size L0w = 8 * (L0w / 2) + 16.
Hypothesis SSPN : strspn_c.strspn_contract.
Hypothesis SCSPN : strcspn_c.strcspn_contract.
Hypothesis MEMC : memcpy_c.memcpy_contract.
Hypothesis CRC : check_reply_contract.
Hypothesis CAC : check_arity_contract.
Hypothesis H_M : Z.of_nat (length M) = len.
Hypothesis H_txi : text + L0w + 1 <= 0x10000 \/ 0x54cb8 <= text.
Hypothesis H_cpi : copy + L0w + 1 <= 0x10000 \/ 0x54cb8 <= copy.
Hypothesis H_ari : arr + arr_size L0w <= 0x10000 \/ 0x54cb8 <= arr.
Hypothesis H_d1 : text + L0w + 1 <= copy \/ copy + L0w + 1 <= text.
Hypothesis H_d2 : arr + arr_size L0w <= text \/ text + L0w + 1 <= arr.
Hypothesis H_d3 : arr + arr_size L0w <= copy \/ copy + L0w + 1 <= arr.
Hypothesis H_d4 : src + len <= text \/ text + L0w + 1 <= src.
Hypothesis H_al : text mod 8 = 0 /\ arr mod 8 = 0 /\ lo mod 8 = 0.
Hypothesis H_fc : frm0 fc.
Hypothesis H_tk : MemNorm.task_mem rsegs m0.
Hypothesis H_gg : rw_cells rsegs m0 GOT_GUARD [C8 (Z_to_bv 64 GUARD)].
Hypothesis H_gu : rw_cells rsegs m0 GUARD [C8 can].
(* the slack of the copy block up to its 8-byte end *)
Hypothesis H_cs : forall a, copy + L0w + 1 <= a < 8 * ((copy + L0w + 1 + 7) / 8) -> mbyte rsegs m0 a <> None.

(* the recorder and the image tables *)
Variables (ans rep : word) (xr slack xa : list byte) (nc fn0 q : Z).
Hypothesis H_grec : bytes_at rsegs m0 GOT_GREC (le8 (Z_to_bv 64 G_REC)).
Hypothesis H_ans : bytes_at rsegs m0 (G_REC + REC_ANSWER) (le8 ans).
Hypothesis H_nr : bytes_at rsegs m0 (G_REC + REC_NREPLIES) (le4 (Z_to_bv 64 1)).
Hypothesis H_rp : bytes_at rsegs m0 (G_REC + REC_REPLY) (le8 rep).
Hypothesis H_rs : bytes_at rsegs m0 (G_REC + REC_REPLY_SIZE) (le8 (Z_to_bv 64 (Z.of_nat (length xr) + 1))).
Hypothesis H_sh : bytes_at rsegs m0 G_SHAPES g_shapes_bytes.
Hypothesis H_rnz : bv_unsigned rep <> 0.
Hypothesis H_rb : bytes_at rsegs m0 (bv_unsigned rep) (xr ++ NUL :: slack).
Hypothesis H_xr : ~ In NUL xr.
Hypothesis H_sl : (- (bv_unsigned rep + Z.of_nat (length xr) + 1)) mod 8 <= Z.of_nat (length slack).
Hypothesis H_ro : forall i, 0 <= i < Z.of_nat (length xr) + 1 + Z.of_nat (length slack) ->
  Frame.outside W0 (bv_unsigned rep + i) /\ bv_unsigned rep + i < lo.
Hypothesis H_ab : bv_unsigned ans <> 0 -> cstr_at m0 (bv_unsigned ans) xa /\
  forall i, 0 <= i < Z.of_nat (length xa) + 1 -> Frame.outside W0 (bv_unsigned ans + i) /\ bv_unsigned ans + i < lo.
Hypothesis H_aok : answer_ok ans xr xa (Z.of_nat (length ws)) (nth 0 ws []).
Hypothesis H_rok : reply_ok (Z.of_nat (length ws)) (nth 0 ws []) xr.
Hypothesis H_par : bytes_at rsegs m0 G_PARSED g_parsed_bytes.
Hypothesis H_nc : 0 <= nc <= 16 /\ bytes_at rsegs m0 (G_REC + REC_NCALLS) (le4 (Z_to_bv 64 nc)).
Hypothesis H_fn : 0 < nc -> 0 <= fn0 < 26 /\ bytes_at rsegs m0 (G_REC + REC_CALLS + CALL_FN) (le4 (Z_to_bv 64 fn0)).
Hypothesis H_gq : bytes_at rsegs m0 GOT_GQUIT (le8 (Z_to_bv 64 G_QUIT)).
Hypothesis H_q : 0 <= q < 2 ^ 32 /\ bytes_at rsegs m0 G_QUIT (le4 (Z_to_bv 64 q)).
Hypothesis H_aro : arity_ok (Z.of_nat (length ws)) (nth 0 ws []) q nc fn0.


Lemma w_out_img : forall a, 0x10000 <= a < 0x54cb8 -> Frame.outside W0 a.
Proof. intros a Ha. cbn. unfold arr_size in *. repeat split; lia. Qed.

Lemma w_out_lo : forall a, a < lo -> Frame.outside [(lo, SP)] a.
Proof. intros a Ha. apply b2_out1. lia. Qed.

(* W_EVT_BEGIN
Lemma w_evt : forall ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s10' t3' t4' t5' t6' jt jc ja jsv jw,
  mem_inv rsegs m0 -> stk rsegs m0 lo SP ->
  bytes_at rsegs m0 src M ->
  u8arr rsegs m0 text jt -> length jt = Z.to_nat (L0w + 1) ->
  u8arr rsegs m0 copy jc -> length jc = Z.to_nat (L0w + 1) ->
  u8arr rsegs m0 arr ja -> length ja = Z.to_nat (arr_size L0w) ->
  rw_cells rsegs m0 SP (LOC0 jsv) ->
  rw_cells rsegs m0 (SP + 40) [C8 (Z_to_bv 64 text); C8 (Z_to_bv 64 copy); CB 16 jw] ->
  evt rsegs w_post (MS (mkR ra' sp gp tp t0' t1' t2' (Z_to_bv 64 src) (Z_to_bv 64 len) (Z_to_bv 64 arr) a1' a2' a3' a4'
       a5' a6' a7' s2 s3 (Z_to_bv 64 text) (Z_to_bv 64 copy) s6 (Z_to_bv 64 L0w) s8 (Z_to_bv 64 MASK) s10'
       (Z_to_bv 64 32) t3' t4' t5' t6') F (Z_to_bv 64 0x141c8) fc None m0 (seg_rom rsegs)).
Proof.
  intros ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s10' t3' t4' t5' t6' jt jc ja jsv jw
    MI ST SRC TX LT CP LC AR LA FR0 FR1.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (G1 : bytes_at rsegs m0 strspn_c.SSP_GOT (le8 (Z_to_bv 64 strspn_c.SSP_GUARD))).
  { pose proof (b2_cells_bytes _ _ _ H_gg) as Hb. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (G2 : bytes_at rsegs m0 strspn_c.SSP_GUARD (le8 can)).
  { pose proof (b2_cells_bytes _ _ _ H_gu) as Hb. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  eapply evt_cut.
  { exact (SlotWordsRun.sw_run sp gp tp s2 s3 s6 s8 F fc m0 lo src len text copy arr M can H_lo ltac:(lia) ltac:(lia)
      H_len H_src H_L0 H_tx H_cp H_ar H_AS SSPN SCSPN MEMC H_M H_txi H_cpi H_ari H_d1 H_d2 H_d3 H_d4
      ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s10' t3' t4' t5' t6' jt jc ja jsv jw
      MI ST SRC TX LT CP LC AR LA G1 G2 FR0 FR1). }
  intros ms1 (t0a & t1a & t2a & a1a & a2a & a3a & a4a & a5a & a6a & a7a & t3a & t4a & t5a & t6a & m1 & T & C & Aa & wp &
    jsv1 & jp & -> & MU1 & WM1 & MI1 & ST1 & LC01 & LC11 & TT & CC & AA & WPL & WPF & WPW).
  (* facts of m0 kept in m1 (the image) *)
  assert (IMG1 : forall a bs, bytes_at rsegs m0 a bs -> 0x10000 <= a -> a + Z.of_nat (length bs) <= 0x54cb8 ->
            bytes_at rsegs m1 a bs).
  { intros a bs H Ha Hb. apply (b2_tb _ m0 m1 a bs MU1 H). intros i Hi. apply w_out_img. lia. }
  assert (CB1 : bytes_at rsegs m1 copy C).
  { pose proof (b2_cells_bytes _ _ _ CC) as Hb. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (LCC : length C = Z.to_nat (L0w + 1)) by (destruct CC as [[[H _] _] _]; exact H).
  assert (AB1 : bytes_at rsegs m1 arr Aa).
  { pose proof (b2_cells_bytes _ _ _ AA) as Hb. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (LAA : length Aa = Z.to_nat (arr_size L0w)) by (destruct AA as [[[H _] _] _]; exact H).
  assert (NWS : (2 * length ws <= length M + 1)%nat).
  { pose proof (SlotRec.words_count (Verbs.line M)). pose proof (b2_upto_len M). lia. }
  assert (WB : forall k p w, nth_error wp k = Some p -> nth_error ws k = Some w ->
            bytes_at rsegs m1 p (w ++ [Z_to_bv 8 0]) /\ copy <= p /\ p + Z.of_nat (length w) + 1 <= copy + L0w + 1).
  { intros k p w Ep Ew. destruct (WPW k p w Ep Ew) as (P1 & P2 & P3). split; [|split; assumption].
    replace p with (copy + Z.of_nat (Z.to_nat (p - copy))) by lia.
    apply (b2_sub m1 copy C _ _ CB1); [rewrite length_app; cbn [length]; lia|].
    rewrite length_app. cbn [length]. exact P3. }
  assert (PB : forall k p, nth_error wp k = Some p -> bytes_at rsegs m1 (arr + 8 * Z.of_nat k) (le8 (Z_to_bv 64 p))).
  { intros k p Ep. assert (Hk : (k < length wp)%nat) by (apply nth_error_Some; rewrite Ep; discriminate).
    replace (8 * Z.of_nat k) with (Z.of_nat (8 * k)) by lia.
    apply (b2_sub m1 arr Aa _ _ AB1).
    - rewrite length_le8, LAA, H_AS. rewrite WPL in Hk. pose proof (SlotRec.words_count (Verbs.line M)) as HWC.
      pose proof (SlotRec.line_len M) as HLL. pose proof (SlotRec.strnlen_upto0 M len H_M) as HU.
      rewrite HU. apply (b2_arr_bound k (length ws) _ Hk). lia.
    - rewrite length_le8. exact (b2_firstn_ptr Aa wp k p ltac:(rewrite WPL; exact WPF) Ep). }
  assert (WIN : forall w, nth_error ws 0 = Some w -> ~ In NUL w).
  { intros w Ew Hin. apply nth_error_In in Ew. destruct (HarnessPropsProof.hwords_word M w Ew) as [_ Hb].
    destruct (Hb NUL Hin) as (_ & _ & H0). apply H0. reflexivity. }
  (* the first word with its slack up to its 8-byte end *)
  assert (WS0 : exists sl0, (length ws <> 0)%nat ->
     bytes_at rsegs m1 (nth 0 wp 0) (nth 0 ws [] ++ NUL :: sl0) /\
     (- (nth 0 wp 0 + Z.of_nat (length (nth 0 ws [])) + 1)) mod 8 <= Z.of_nat (length sl0) /\
     copy <= nth 0 wp 0 /\ nth 0 wp 0 + Z.of_nat (length (nth 0 ws [])) + 1 + Z.of_nat (length sl0) <= lo).
  { destruct (nth_error ws 0) as [w0|] eqn:Ew.
    2: { exists []. intros Hn. apply nth_error_None in Ew. lia. }
    destruct (nth_error wp 0) as [p0|] eqn:Ep.
    2: { exfalso. apply nth_error_None in Ep. assert (H0 : (0 < length ws)%nat).
         { apply nth_error_Some. rewrite Ew. discriminate. } lia. }
    rewrite (b2_nth wp 0 p0 0 Ep), (b2_nth ws 0 w0 [] Ew).
    destruct (WB 0%nat p0 w0 Ep Ew) as (Bw & P1 & P2).
    pose proof (Z.mod_pos_bound (- (p0 + Z.of_nat (length w0) + 1)) 8 ltac:(lia)) as KM.
    pose proof (b2_round (p0 + Z.of_nat (length w0) + 1) (copy + L0w + 1) ltac:(lia)) as RD.
    destruct H_al as (AL1 & AL2 & AL3).
    pose proof (b2_r8_ge (copy + L0w + 1)) as RG.
    assert (RL : 8 * ((copy + L0w + 1 + 7) / 8) <= lo) by (apply b2_r8; [lia | exact AL3]).
    assert (RT : copy + L0w + 1 <= text -> 8 * ((copy + L0w + 1 + 7) / 8) <= text)
      by (intros Ht; apply b2_r8; [exact Ht | exact AL1]).
    assert (RA : copy + L0w + 1 <= arr -> 8 * ((copy + L0w + 1 + 7) / 8) <= arr)
      by (intros Ht; apply b2_r8; [exact Ht | exact AL2]).
    destruct (hand_back.hb_bytes_pad rsegs m1 p0 (w0 ++ [Z_to_bv 8 0])
                (Z.to_nat ((- (p0 + Z.of_nat (length w0) + 1)) mod 8)) Bw) as (sl & Lsl & Bs).
    - rewrite length_app. cbn [length]. lia.
    - intros j Hj. rewrite length_app in *. cbn [length] in *.
      destruct (Z_lt_ge_dec (p0 + Z.of_nat (length w0 + 1) + Z.of_nat j) (copy + L0w + 1)) as [Hx|Hx].
      + replace (p0 + Z.of_nat (length w0 + 1) + Z.of_nat j)
          with (copy + Z.of_nat (Z.to_nat (p0 + Z.of_nat (length w0 + 1) + Z.of_nat j - copy))) by lia.
        rewrite (KindB.mbyte_of_bytes_at rsegs m1 copy C _ CB1) by lia.
        intros E. apply nth_error_None in E. lia.
      + assert (Ho : Frame.outside W0 (p0 + Z.of_nat (length w0 + 1) + Z.of_nat j)).
        { cbn. repeat split; lia. }
        rewrite (KindB.munch_mbyte rsegs W0 m0 m1 (p0 + Z.of_nat (length w0 + 1) + Z.of_nat j) MU1 ltac:(lia) Ho).
        apply H_cs. lia.
    - exists sl. intros _. rewrite <- app_assoc in Bs. cbn [app] in Bs. split; [exact Bs|].
      rewrite Lsl. split; [lia|]. split; [lia|]. lia. }
  destruct WS0 as (sl0 & WS0).
  pose proof (SlotRec.words_count (Verbs.line M)) as HWC. pose proof (b2_upto_len M) as HUL.
  assert (U40 : bv_unsigned (Z_to_bv 64 (SP + 40)) = SP + 40) by (apply unsigned_lit; lia).
  assert (UAR : bv_unsigned (Z_to_bv 64 arr) = arr) by (apply unsigned_lit; lia).
  assert (WN1 : bytes_at rsegs m1 (SP + 40 + WORDS_N) (le4 (Z_to_bv 64 (Z.of_nat (length ws))))).
  { exact (send_message.sm_cell_get2 rsegs m1 (SP + 40) [C8 (Z_to_bv 64 text); C8 (Z_to_bv 64 copy); C8 (Z_to_bv 64 arr)]
      (C4 (Z_to_bv 64 (Z.of_nat (length ws)))) [CB 4 jp] 24%nat LC11 eq_refl). }
  assert (WW1 : bytes_at rsegs m1 (SP + 40 + WORDS_W) (le8 (Z_to_bv 64 arr))).
  { exact (send_message.sm_cell_get2 rsegs m1 (SP + 40) [C8 (Z_to_bv 64 text); C8 (Z_to_bv 64 copy)]
      (C8 (Z_to_bv 64 arr)) [C4 (Z_to_bv 64 (Z.of_nat (length ws))); CB 4 jp] 16%nat LC11 eq_refl). }
  assert (GGb : bytes_at rsegs m0 GOT_GUARD (le8 (Z_to_bv 64 GUARD))).
  { pose proof (b2_cells_bytes _ _ _ H_gg) as Hb. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (GUb : bytes_at rsegs m0 GUARD (le8 can)).
  { pose proof (b2_cells_bytes _ _ _ H_gu) as Hb. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (SHL : G_SHAPES + Z.of_nat (length g_shapes_bytes) <= 0x54cb8) by (apply Z.leb_le; vm_compute; reflexivity).
  assert (PRL : G_PARSED + Z.of_nat (length g_parsed_bytes) <= 0x54cb8) by (apply Z.leb_le; vm_compute; reflexivity).
  pose proof CRC as CR. unfold check_reply_contract, CHECK_REPLY, CHECK_REPLY_K in CR.
  eapply evt_cut.
  { eapply CR with (lo := lo) (ans := ans) (rep := rep) (ww := Z_to_bv 64 arr) (p0 := Z_to_bv 64 (nth 0 wp 0))
      (xr := xr) (slack := slack) (xa := xa) (w0 := nth 0 ws []) (sl0 := sl0) (n := Z.of_nat (length ws)) (can := can).
    - exact MI1.
    - intros a b E. destruct (Z_lt_ge_dec (bv_unsigned a) TASK_SIZE) as [Hl|Hg]; [right; exact Hl|].
      assert (Ho : Frame.outside W0 (bv_unsigned a)) by (cbn; unfold arr_size in *; repeat split; lia).
      rewrite (MU1 a Ho) in E. exact (H_tk a b E).
    - exact H_fc.
    - exact ST1.
    - lia.
    - match goal with |- ?x <= _ => change x with 0x54cb8 end. lia.
    - lia.
    - apply (b2_cells _ m0 m1 _ _ MU1 H_gg). intros i Hi. apply w_out_img. cbn in Hi. unfold GOT_GUARD. lia.
    - apply (b2_cells _ m0 m1 _ _ MU1 H_gu). intros i Hi. apply w_out_img. cbn in Hi. unfold GUARD. lia.
    - apply IMG1; [exact H_grec | unfold GOT_GREC; lia | rewrite length_le8; unfold GOT_GREC; lia].
    - apply IMG1; [exact H_ans | unfold G_REC, REC_ANSWER; lia | rewrite length_le8; unfold G_REC, REC_ANSWER; lia].
    - apply IMG1; [exact H_nr | unfold G_REC, REC_NREPLIES; lia | rewrite length_le4; unfold G_REC, REC_NREPLIES; lia].
    - apply IMG1; [exact H_rp | unfold G_REC, REC_REPLY; lia | rewrite length_le8; unfold G_REC, REC_REPLY; lia].
    - apply IMG1; [exact H_rs | unfold G_REC, REC_REPLY_SIZE; lia | rewrite length_le8; unfold G_REC, REC_REPLY_SIZE; lia].
    - apply IMG1; [exact H_sh | unfold G_SHAPES; lia | exact SHL].
    - exact H_rnz.
    - apply (b2_tb _ m0 m1 _ _ MU1 H_rb). intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
      exact (proj1 (H_ro i ltac:(lia))).
    - exact H_xr.
    - exact H_sl.
    - unfold outside_stack. cbn [disjoint_from]. split; [left | exact Logic.I].
      pose proof (proj2 (H_ro (Z.of_nat (length xr) + Z.of_nat (length slack)) ltac:(lia))). lia.
    - intros Hne. destruct (H_ab Hne) as [[Hb Hn] Ho]. split; [split; [|exact Hn]|].
      + apply (b2_tb _ m0 m1 _ _ MU1 Hb). intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
        exact (proj1 (Ho i ltac:(lia))).
      + unfold outside_stack. cbn [disjoint_from]. split; [left | exact Logic.I].
        pose proof (proj2 (Ho (Z.of_nat (length xa)) ltac:(lia))). lia.
    - lia.
    - rewrite U40. exact WN1.
    - rewrite U40. unfold outside_stack. cbn [disjoint_from]. split; [right; unfold WORDS_N; lia | exact Logic.I].
    - rewrite U40. exact WW1.
    - rewrite U40. unfold outside_stack. cbn [disjoint_from]. split; [right; unfold WORDS_W; lia | exact Logic.I].
    - intros Hn. assert (Hn' : (length ws <> 0)%nat) by lia. destruct (WS0 Hn') as (B0 & S0 & C0 & L0').
      destruct (nth_error wp 0) as [p0|] eqn:Ep.
      2: { exfalso. apply nth_error_None in Ep. lia. }
      destruct (nth_error ws 0) as [w0|] eqn:Ew.
      2: { exfalso. apply nth_error_None in Ew. lia. }
      rewrite (b2_nth wp 0 p0 0 Ep) in *. rewrite (b2_nth ws 0 w0 [] Ew) in *.
      assert (UP : bv_unsigned (Z_to_bv 64 p0) = p0) by (apply unsigned_lit; lia).
      rewrite UAR, UP. pose proof (PB 0%nat p0 Ep) as PB0. rewrite Z.add_0_r in PB0.
      split; [exact PB0|]. split.
      { unfold outside_stack. cbn [disjoint_from]. split; [left; unfold arr_size in *; lia | exact Logic.I]. }
      split; [exact B0|]. split; [exact (WIN w0 eq_refl)|]. split; [exact S0|].
      unfold outside_stack. cbn [disjoint_from]. split; [left; lia | exact Logic.I].
    - exact H_aok.
    - exact H_rok. }
  intros ms2 (t0b & t1b & t2b & a0b & a1b & a2b & a3b & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & Ft & fc2 & m2 &
    -> & MU2 & WM2 & MI2 & FR2 & _ & ST2).
  rewrite (SlotEnd.se_ret_pc 0x142cc eq_refl).
  eapply evt_cut; [apply run_g_ca_ok; lia|]. intros ms3 ->.
  assert (T12 : forall a bs, bytes_at rsegs m1 a bs -> a + Z.of_nat (length bs) <= lo \/ SP <= a ->
            bytes_at rsegs m2 a bs).
  { intros a bs H Ha. apply (b2_tb _ m1 m2 a bs MU2 H). intros i Hi. apply b2_out1. lia. }
  assert (IMG2 : forall a bs, bytes_at rsegs m0 a bs -> 0x10000 <= a -> a + Z.of_nat (length bs) <= 0x54cb8 ->
            bytes_at rsegs m2 a bs).
  { intros a bs H Ha Hb. apply T12; [exact (IMG1 a bs H Ha Hb) | lia]. }
  pose proof CAC as CA. unfold check_arity_contract, CHECK_ARITY, CHECK_ARITY_K in CA.
  eapply evt_cut.
  { eapply CA with (lo := lo) (t := Z.of_nat (length ws)) (q := q) (nc := nc) (fn0 := fn0) (ww := Z_to_bv 64 arr)
      (p0 := Z_to_bv 64 (nth 0 wp 0)) (v := nth 0 ws []) (can := can).
    - exact MI2.
    - exact ST2.
    - lia.
    - match goal with |- ?x <= _ => change x with 0x54cb8 end. lia.
    - apply IMG2; [exact GGb | unfold GOT_GUARD; lia | rewrite length_le8; unfold GOT_GUARD; lia].
    - apply IMG2; [exact GUb | unfold GUARD; lia | rewrite length_le8; unfold GUARD; lia].
    - apply IMG2; [exact H_par | unfold G_PARSED; lia | exact PRL].
    - apply IMG2; [exact H_grec | unfold GOT_GREC; lia | rewrite length_le8; unfold GOT_GREC; lia].
    - exact (proj1 H_nc).
    - apply IMG2; [exact (proj2 H_nc) | unfold G_REC, REC_NCALLS; lia | rewrite length_le4; unfold G_REC, REC_NCALLS; lia].
    - intros Hp. destruct (H_fn Hp) as [Hf Hb]. split; [exact Hf|].
      apply IMG2; [exact Hb | unfold G_REC, REC_CALLS, CALL_FN; lia |
        rewrite length_le4; unfold G_REC, REC_CALLS, CALL_FN; lia].
    - apply IMG2; [exact H_gq | unfold GOT_GQUIT; lia | rewrite length_le8; unfold GOT_GQUIT; lia].
    - exact (proj1 H_q).
    - apply IMG2; [exact (proj2 H_q) | unfold G_QUIT; lia | rewrite length_le4; unfold G_QUIT; lia].
    - lia.
    - rewrite U40. apply T12; [exact WN1 | right; lia].
    - rewrite U40. unfold outside_stack. cbn [disjoint_from]. split; [right; unfold WORDS_N; lia | exact Logic.I].
    - rewrite U40. apply T12; [exact WW1 | right; lia].
    - rewrite U40. unfold outside_stack. cbn [disjoint_from]. split; [right; unfold WORDS_W; lia | exact Logic.I].
    - intros Hn. assert (Hn' : (length ws <> 0)%nat) by lia. destruct (WS0 Hn') as (_ & _ & C0 & L0').
      destruct (nth_error wp 0) as [p0|] eqn:Ep.
      2: { exfalso. apply nth_error_None in Ep. lia. }
      destruct (nth_error ws 0) as [w0|] eqn:Ew.
      2: { exfalso. apply nth_error_None in Ew. lia. }
      rewrite (b2_nth wp 0 p0 0 Ep) in *. rewrite (b2_nth ws 0 w0 [] Ew) in *.
      destruct (WB 0%nat p0 w0 Ep Ew) as (Bw & P1 & P2).
      assert (UP : bv_unsigned (Z_to_bv 64 p0) = p0) by (apply unsigned_lit; lia).
      pose proof (PB 0%nat p0 Ep) as PB0. rewrite Z.add_0_r in PB0.
      unfold word_slot. rewrite UAR, UP.
      split; [apply T12; [exact PB0 | left; rewrite length_le8; unfold arr_size in *; lia]|].
      split; [unfold outside_stack; cbn [disjoint_from]; split; [left; unfold arr_size in *; lia | exact Logic.I]|].
      split; [split; [apply T12; [exact Bw | left; rewrite length_app; cbn [length]; lia] | exact (WIN w0 eq_refl)]|].
      unfold outside_stack. cbn [disjoint_from]. split; [left; lia | exact Logic.I].
    - exact H_aro. }
  intros ms4 (t0c & t1c & t2c & a0c & a1c & a2c & a3c & a4c & a5c & a6c & a7c & t3c & t4c & t5c & t6c & m3 & -> & MU3 &
    WM3 & MI3 & ST3).
  rewrite (SlotEnd.se_ret_pc 0x142d4 eq_refl).
  eapply evt_cut; [apply run_g_cw_ok; lia|]. intros ms5 ->. apply evt_done.
  assert (C13 : forall a cs, rw_cells rsegs m1 a cs -> a + Z.of_nat (cells_size cs) <= lo \/ SP <= a ->
            rw_cells rsegs m3 a cs).
  { intros a cs H Ha. apply (b2_cells _ m2 m3 a cs MU3); [apply (b2_cells _ m1 m2 a cs MU2 H) |];
      intros i Hi; apply b2_out1; lia. }
  exists t0c, t1c, t2c, a1c, a2c, a3c, a4c, a5c, a6c, a7c, t3c, t4c, t5c, t6c, Ft, fc2, m3, T, C, Aa, wp, jsv1, jp.
  split; [reflexivity|].
  split.
  { apply (b2_munch W1 [(lo, SP)] W1 m0 m2 m3); [apply (b2_munch W0 [(lo, SP)] W1 m0 m1 m2 MU1 MU2) | exact MU3 |].
    - intros x Hx. cbn in Hx |- *. destruct Hx as (X1 & X2 & X3 & X4 & _). repeat split; try assumption; lia.
    - intros x Hx. split; [exact Hx|]. cbn in Hx |- *. destruct Hx as (X1 & X2 & X3 & X4 & _). split; [lia | exact Logic.I]. }
  split; [intros x Hx; apply WM3, WM2, WM1, Hx|].
  split; [exact MI3|]. split; [exact FR2|].
  split; [apply C13; [exact LC01 | right; lia]|].
  split; [apply C13; [exact LC11 | right; lia]|].
  split; [apply C13; [exact TT | left; cbn; lia]|].
  split; [apply C13; [exact CC | left; cbn; lia]|].
  split; [apply C13; [exact AA | left; cbn; unfold arr_size in *; lia]|].
  split; [exact WPL|]. split; [exact WPF|]. exact WPW.
Qed.
W_EVT_END *)

Hypothesis CK : ck_spec.

Lemma w_evt : forall ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s10' t3' t4' t5' t6' jt jc ja jsv jw,
  mem_inv rsegs m0 -> stk rsegs m0 lo SP ->
  bytes_at rsegs m0 src M ->
  u8arr rsegs m0 text jt -> length jt = Z.to_nat (L0w + 1) ->
  u8arr rsegs m0 copy jc -> length jc = Z.to_nat (L0w + 1) ->
  u8arr rsegs m0 arr ja -> length ja = Z.to_nat (arr_size L0w) ->
  rw_cells rsegs m0 SP (LOC0 jsv) ->
  rw_cells rsegs m0 (SP + 40) [C8 (Z_to_bv 64 text); C8 (Z_to_bv 64 copy); CB 16 jw] ->
  evt rsegs (w_post sp gp tp s2 s3 s6 s8 m0 lo src len text copy arr M)
    (MS (mkR ra' sp gp tp t0' t1' t2' (Z_to_bv 64 src) (Z_to_bv 64 len) (Z_to_bv 64 arr) a1' a2' a3' a4'
       a5' a6' a7' s2 s3 (Z_to_bv 64 text) (Z_to_bv 64 copy) s6 (Z_to_bv 64 L0w) s8 (Z_to_bv 64 MASK) s10'
       (Z_to_bv 64 32) t3' t4' t5' t6') F (Z_to_bv 64 0x141c8) fc None m0 (seg_rom rsegs)).
Proof.
  intros ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s10' t3' t4' t5' t6' jt jc ja jsv jw
    MI ST SRC TX LT CP LC AR LA FR0 FR1.
  assert (G1 : bytes_at rsegs m0 strspn_c.SSP_GOT (le8 (Z_to_bv 64 strspn_c.SSP_GUARD))).
  { pose proof (b2_cells_bytes _ _ _ H_gg) as Hb. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (G2 : bytes_at rsegs m0 strspn_c.SSP_GUARD (le8 can)).
  { pose proof (b2_cells_bytes _ _ _ H_gu) as Hb. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (E1 : lo + 96 <= SP) by (clear - H_LOS; lia).
  assert (E2 : SP + 176 <= 2 ^ 64) by (clear - H_SPH; lia).
  eapply evt_cut.
  { exact (SlotWordsRun.sw_run sp gp tp s2 s3 s6 s8 F fc m0 lo src len text copy arr M can H_lo E1 E2
      H_len H_src H_L0 H_tx H_cp H_ar H_AS SSPN SCSPN MEMC H_M H_txi H_cpi H_ari H_d1 H_d2 H_d3 H_d4
      ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s10' t3' t4' t5' t6' jt jc ja jsv jw
      MI ST SRC TX LT CP LC AR LA G1 G2 FR0 FR1). }
  intros ms1 H1.
  exact (CK sp gp tp s2 s3 s6 s8 F fc m0 lo src len text copy arr M can ans rep xr slack xa nc fn0 q H_lo H_LOS H_SPH
    H_TS H_len H_src H_L0 H_tx H_cp H_ar H_AS CRC CAC H_M H_txi H_cpi H_ari H_d1 H_d2 H_d3 H_d4 H_al H_fc H_tk H_gg
    H_gu H_cs H_grec H_ans H_nr H_rp H_rs H_sh H_rnz H_rb H_xr H_sl H_ro H_ab H_aok H_rok H_par H_nc H_fn H_gq H_q
    H_aro ms1 H1).
Qed.

End W.
