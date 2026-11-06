From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes MState.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts CommandModel CommandFP SlotSpec
  SlotRuns check_reply_c check_arity_c check_reply_answer_c rec_shape_of_c SlotItB2.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require SlotWords SlotWordsRun strspn_c strcspn_c memcpy_c
  KindB send_message hand_back SlotEnd SlotRec HarnessPropsProof RecAns.
Import ListNotations.
Local Open Scope Z_scope.

(* SlotItB2.ck_spec: from check_reply's entry (SlotWords.sw_post) to check_words' entry (w_post), in two calls:
   check_reply (to ck_mid at 0x142cc), then 0x142cc .. check_arity, check_arity, 0x142d4 .. check_words. *)

Section CK.
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
Hypothesis H_cs : forall a, copy + L0w + 1 <= a < 8 * ((copy + L0w + 1 + 7) / 8) -> mbyte rsegs m0 a <> None.

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

(* Facts wrapped so that lia does not see them. *)
Definition ck_sl : Prop := (- (bv_unsigned rep + Z.of_nat (length xr) + 1)) mod 8 <= Z.of_nat (length slack).
Definition ck_ab : Prop := bv_unsigned ans <> 0 -> cstr_at m0 (bv_unsigned ans) xa /\
  forall i, 0 <= i < Z.of_nat (length xa) + 1 -> Frame.outside W0 (bv_unsigned ans + i) /\ bv_unsigned ans + i < lo.
Definition ck_fn : Prop :=
  0 < nc -> 0 <= fn0 < 26 /\ bytes_at rsegs m0 (G_REC + REC_CALLS + CALL_FN) (le4 (Z_to_bv 64 fn0)).

Lemma ck_out0 : forall a, 0x10000 <= a < 0x54cb8 -> Frame.outside W0 a.
Proof. intros a Ha. clear - H_lo H_LOS H_txi H_cpi H_ari Ha. cbn [Frame.outside]. repeat split; lia. Qed.

Lemma ck_out1 : forall a, 0x10000 <= a < 0x54cb8 -> Frame.outside W1 a.
Proof. intros a Ha. clear - H_lo H_txi H_cpi H_ari Ha. cbn [Frame.outside]. repeat split; lia. Qed.

Lemma ck_img : forall W m, munch W m0 m -> (forall a, 0x10000 <= a < 0x54cb8 -> Frame.outside W a) ->
  forall a bs, bytes_at rsegs m0 a bs -> 0x10000 <= a -> a + Z.of_nat (length bs) <= 0x54cb8 -> bytes_at rsegs m a bs.
Proof.
  intros W m MU HO a bs H Ha Hb. apply (b2_tb W m0 m a bs MU H). intros i Hi. apply HO. clear - Ha Hb Hi. lia.
Qed.

Lemma ck_nws : (2 * length ws <= length M + 1)%nat.
Proof. pose proof (SlotRec.words_count (Verbs.line M)). pose proof (b2_upto_len M). clear - H H0. lia. Qed.

Lemma ck_as16 : 16 <= arr_size L0w.
Proof. clear - H_L0. unfold arr_size. pose proof (Z.div_pos (strnlen_res len M) 2 ltac:(lia) ltac:(lia)). lia. Qed.

Lemma ck_win : forall w, nth_error ws 0 = Some w -> ~ In NUL w.
Proof.
  intros w Ew Hin. apply nth_error_In in Ew. destruct (HarnessPropsProof.hwords_word M w Ew) as [_ Hb].
  destruct (Hb NUL Hin) as (_ & _ & H0). apply H0. reflexivity.
Qed.

(* The words in copy and their addresses in arr. *)
Lemma ck_wb : forall m C Aa wp,
  rw_cells rsegs m copy [CB (Z.to_nat (L0w + 1)) C] -> rw_cells rsegs m arr [CB (Z.to_nat (arr_size L0w)) Aa] ->
  length wp = length ws -> firstn (8 * length ws) Aa = concat (map (fun p => le8 (Z_to_bv 64 p)) wp) ->
  (forall k p w, nth_error wp k = Some p -> nth_error ws k = Some w ->
     copy <= p /\ p + Z.of_nat (length w) + 1 <= copy + L0w + 1 /\
     firstn (length w + 1) (skipn (Z.to_nat (p - copy)) C) = w ++ [Z_to_bv 8 0]) ->
  (forall k p w, nth_error wp k = Some p -> nth_error ws k = Some w ->
     bytes_at rsegs m p (w ++ [Z_to_bv 8 0]) /\ copy <= p /\ p + Z.of_nat (length w) + 1 <= copy + L0w + 1) /\
  (forall k p, nth_error wp k = Some p -> bytes_at rsegs m (arr + 8 * Z.of_nat k) (le8 (Z_to_bv 64 p))).
Proof.
  intros m C Aa wp CC AA WPL WPF WPW.
  assert (CB1 : bytes_at rsegs m copy C).
  { pose proof (b2_cells_bytes _ _ _ CC) as Hb. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (LCC : length C = Z.to_nat (L0w + 1)) by (destruct CC as [[[H _] _] _]; exact H).
  assert (AB1 : bytes_at rsegs m arr Aa).
  { pose proof (b2_cells_bytes _ _ _ AA) as Hb. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (LAA : length Aa = Z.to_nat (arr_size L0w)) by (destruct AA as [[[H _] _] _]; exact H).
  split.
  - intros k p w Ep Ew. destruct (WPW k p w Ep Ew) as (P1 & P2 & P3). split; [|split; assumption].
    replace p with (copy + Z.of_nat (Z.to_nat (p - copy))) by (clear - P1; lia).
    apply (b2_sub m copy C _ _ CB1); [rewrite length_app; cbn [length]; clear - P1 P2 LCC H_L0; lia|].
    rewrite length_app. cbn [length]. exact P3.
  - intros k p Ep. assert (Hk : (k < length wp)%nat) by (apply nth_error_Some; rewrite Ep; discriminate).
    replace (8 * Z.of_nat k) with (Z.of_nat (8 * k)) by lia.
    apply (b2_sub m arr Aa _ _ AB1).
    + rewrite length_le8, LAA, H_AS. rewrite WPL in Hk. pose proof (SlotRec.words_count (Verbs.line M)) as HWC.
      pose proof (SlotRec.strnlen_upto0 M len H_M) as HU.
      pose proof (SlotRec.line_len M) as HLL.
      rewrite HU. apply (b2_arr_bound k (length ws) _ Hk). clear - HWC HLL. lia.
    + rewrite length_le8. exact (b2_firstn_ptr Aa wp k p ltac:(rewrite WPL; exact WPF) Ep).
Qed.

Definition ck_ws0_ok (m1 : word -> option byte) (wp : list Z) (sl0 : list byte) : Prop :=
  (length ws <> 0)%nat ->
  bytes_at rsegs m1 (nth 0 wp 0) (nth 0 ws [] ++ NUL :: sl0) /\
  (- (nth 0 wp 0 + Z.of_nat (length (nth 0 ws [])) + 1)) mod 8 <= Z.of_nat (length sl0) /\
  copy <= nth 0 wp 0 /\ nth 0 wp 0 + Z.of_nat (length (nth 0 ws [])) + 1 + Z.of_nat (length sl0) <= lo.

(* The first word with its slack up to its 8-byte end. *)
Lemma ck_ws0 : forall m1 C wp, munch W0 m0 m1 -> bytes_at rsegs m1 copy C -> length C = Z.to_nat (L0w + 1) ->
  length wp = length ws ->
  (forall k p w, nth_error wp k = Some p -> nth_error ws k = Some w ->
     bytes_at rsegs m1 p (w ++ [Z_to_bv 8 0]) /\ copy <= p /\ p + Z.of_nat (length w) + 1 <= copy + L0w + 1) ->
  exists sl0, ck_ws0_ok m1 wp sl0.
Proof.
  intros m1 C wp MU1 CB1 LCC WPL WB. unfold ck_ws0_ok.
  destruct (nth_error ws 0) as [w0|] eqn:Ew.
  2: { exists []. intros Hn. apply nth_error_None in Ew. lia. }
  destruct (nth_error wp 0) as [p0|] eqn:Ep.
  2: { exfalso. apply nth_error_None in Ep. assert (H0 : (0 < length ws)%nat).
       { apply nth_error_Some. rewrite Ew. discriminate. } lia. }
  rewrite (b2_nth wp 0 p0 0 Ep), (b2_nth ws 0 w0 [] Ew).
  destruct (WB 0%nat p0 w0 Ep Ew) as (Bw & P1 & P2).
  clear H_txi H_cpi H_ari H_d2 H_d4 H_ab H_fn H_sl H_AS.
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
      { cbn [Frame.outside]. repeat split; lia. }
      rewrite (KindB.munch_mbyte rsegs W0 m0 m1 (p0 + Z.of_nat (length w0 + 1) + Z.of_nat j) MU1 ltac:(lia) Ho).
      apply H_cs. lia.
  - exists sl. intros _. rewrite <- app_assoc in Bs. cbn [app] in Bs. split; [exact Bs|].
    rewrite Lsl. split; [lia|]. split; [lia|]. lia.
Qed.

(* After check_reply returned (pc 0x142cc). *)
Definition ck_mid : machine_state -> Prop := fun ms' =>
  exists ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (Ft : bvmap 5 word) (fc' : bv 32) m' T C Aa
    (wp : list Z) jsv' jp,
    ms' = MS (mkR ra' sp gp tp t0' t1' t2' (Z_to_bv 64 src) (Z_to_bv 64 len) a0' a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 (Z_to_bv 64 text) (Z_to_bv 64 copy) s6 (Z_to_bv 64 (bv_unsigned s8 - len)) s8
                  (Z_to_bv 64 MASK) (Z_to_bv 64 arr) (Z_to_bv 64 32) t3' t4' t5' t6')
             Ft (Z_to_bv 64 0x142cc) fc' None m' (seg_rom rsegs) /\
    munch W1 m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\ frm0 fc' /\ stk rsegs m' lo SP /\
    rw_cells rsegs m' SP (LOC0 jsv') /\
    rw_cells rsegs m' (SP + 40)
      [C8 (Z_to_bv 64 text); C8 (Z_to_bv 64 copy); C8 (Z_to_bv 64 arr); C4 (Z_to_bv 64 (Z.of_nat (length ws))); CB 4 jp] /\
    rw_cells rsegs m' text [CB (Z.to_nat (L0w + 1)) T] /\
    rw_cells rsegs m' copy [CB (Z.to_nat (L0w + 1)) C] /\
    rw_cells rsegs m' arr [CB (Z.to_nat (arr_size L0w)) Aa] /\
    length wp = length ws /\
    firstn (8 * length ws) Aa = concat (map (fun p => le8 (Z_to_bv 64 p)) wp) /\
    (forall k p w, nth_error wp k = Some p -> nth_error ws k = Some w ->
       copy <= p /\ p + Z.of_nat (length w) + 1 <= copy + L0w + 1 /\
       firstn (length w + 1) (skipn (Z.to_nat (p - copy)) C) = w ++ [Z_to_bv 8 0]).

(* check_reply's call. *)
Lemma ck_reply : forall ms, SlotWords.sw_post sp gp tp s2 s3 s6 s8 F fc m0 lo src len text copy arr M ms ->
  evt rsegs ck_mid ms.
Proof.
  intros ms1 (t0a & t1a & t2a & a1a & a2a & a3a & a4a & a5a & a6a & a7a & t3a & t4a & t5a & t6a & m1 & T & C & Aa & wp &
    jsv1 & jp & -> & MU1 & WM1 & MI1 & ST1 & LC01 & LC11 & TT & CC & AA & WPL & WPF & WPW).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (ck_img W0 m1 MU1 ck_out0) as IMG1.
  destruct (ck_wb m1 C Aa wp CC AA WPL WPF WPW) as [WB PB].
  assert (CB1 : bytes_at rsegs m1 copy C).
  { pose proof (b2_cells_bytes _ _ _ CC) as Hb. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (LCC : length C = Z.to_nat (L0w + 1)) by (destruct CC as [[[H _] _] _]; exact H).
  destruct (ck_ws0 m1 C wp MU1 CB1 LCC WPL WB) as (sl0 & WS0).
  pose proof ck_win as WIN. pose proof ck_nws as NWS. pose proof ck_as16 as AS16.
  assert (HSL : ck_sl) by exact H_sl. assert (HAB : ck_ab) by exact H_ab.
  pose proof ck_out0 as O0.
  clear H_txi H_cpi H_ari H_d1 H_d2 H_d3 H_d4 H_al H_cs H_AS H_sl H_ab H_fn.
  assert (U40 : bv_unsigned (Z_to_bv 64 (SP + 40)) = SP + 40) by (apply unsigned_lit; lia).
  assert (UAR : bv_unsigned (Z_to_bv 64 arr) = arr) by (apply unsigned_lit; lia).
  assert (WN1 : bytes_at rsegs m1 (SP + 40 + WORDS_N) (le4 (Z_to_bv 64 (Z.of_nat (length ws))))).
  { exact (send_message.sm_cell_get2 rsegs m1 (SP + 40) [C8 (Z_to_bv 64 text); C8 (Z_to_bv 64 copy); C8 (Z_to_bv 64 arr)]
      (C4 (Z_to_bv 64 (Z.of_nat (length ws)))) [CB 4 jp] 24%nat LC11 eq_refl). }
  assert (WW1 : bytes_at rsegs m1 (SP + 40 + WORDS_W) (le8 (Z_to_bv 64 arr))).
  { exact (send_message.sm_cell_get2 rsegs m1 (SP + 40) [C8 (Z_to_bv 64 text); C8 (Z_to_bv 64 copy)]
      (C8 (Z_to_bv 64 arr)) [C4 (Z_to_bv 64 (Z.of_nat (length ws))); CB 4 jp] 16%nat LC11 eq_refl). }
  assert (SHL : G_SHAPES + Z.of_nat (length g_shapes_bytes) <= 0x54cb8) by (apply Z.leb_le; vm_compute; reflexivity).
  pose proof CRC as CR. unfold check_reply_contract, CHECK_REPLY, CHECK_REPLY_K in CR.
  eapply evt_cut.
  { eapply CR with (lo := lo) (ans := ans) (rep := rep) (ww := Z_to_bv 64 arr) (p0 := Z_to_bv 64 (nth 0 wp 0))
      (xr := xr) (slack := slack) (xa := xa) (w0 := nth 0 ws []) (sl0 := sl0) (n := Z.of_nat (length ws)) (can := can).
    - exact MI1.
    - intros a b E. destruct (Z_lt_ge_dec (bv_unsigned a) TASK_SIZE) as [Hl|Hg]; [right; exact Hl|].
      assert (Ho : Frame.outside W0 (bv_unsigned a)) by (cbn [Frame.outside]; repeat split; lia).
      rewrite (MU1 a Ho) in E. exact (H_tk a b E).
    - exact H_fc.
    - exact ST1.
    - lia.
    - unfold IMG_END. lia.
    - lia.
    - apply (b2_cells _ m0 m1 _ _ MU1 H_gg). intros i Hi. apply O0. cbn in Hi. unfold GOT_GUARD. lia.
    - apply (b2_cells _ m0 m1 _ _ MU1 H_gu). intros i Hi. apply O0. cbn in Hi. unfold GUARD. lia.
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
    - exact HSL.
    - unfold outside_stack. cbn [disjoint_from]. split; [left | exact Logic.I].
      pose proof (proj2 (H_ro (Z.of_nat (length xr) + Z.of_nat (length slack)) ltac:(lia))). lia.
    - intros Hne. destruct (HAB Hne) as [[Hb Hn] Ho]. split; [split; [|exact Hn]|].
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
      rewrite UAR, UP. pose proof (PB 0%nat p0 Ep) as PB0.
      replace (arr + 8 * Z.of_nat 0) with arr in PB0 by lia.
      split; [exact PB0|]. split.
      { unfold outside_stack. cbn [disjoint_from]. split; [left; lia | exact Logic.I]. }
      split; [exact B0|]. split; [exact (WIN w0 eq_refl)|]. split; [exact S0|].
      unfold outside_stack. cbn [disjoint_from]. split; [left; lia | exact Logic.I].
    - exact H_aok.
    - exact H_rok. }
  intros ms2 (t0b & t1b & t2b & a0b & a1b & a2b & a3b & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & Ft & fc2 & m2 &
    -> & MU2 & WM2 & MI2 & FR2 & _ & ST2).
  rewrite (SlotEnd.se_ret_pc 0x142cc eq_refl).
  apply evt_done.
  assert (C12 : forall a cs, rw_cells rsegs m1 a cs -> a + Z.of_nat (cells_size cs) <= lo \/ SP <= a ->
            rw_cells rsegs m2 a cs).
  { intros a cs H Ha. apply (b2_cells _ m1 m2 a cs MU2 H). intros i Hi. apply b2_out1. lia. }
  exists (Z_to_bv 64 0x142cc), t0b, t1b, t2b, a0b, a1b, a2b, a3b, a4b, a5b, a6b, a7b, t3b, t4b, t5b, t6b, Ft, fc2, m2,
    T, C, Aa, wp, jsv1, jp.
  split; [reflexivity|].
  split.
  { apply (b2_munch W0 [(lo, SP)] W1 m0 m1 m2 MU1 MU2).
    intros x Hx. cbn [Frame.outside] in Hx |- *. destruct Hx as (X1 & X2 & X3 & X4 & _).
    split; [split; [exact X1|]; split; [exact X2|]; split; [exact X3|]; split; [lia | exact Logic.I]|].
    split; [lia | exact Logic.I]. }
  split; [intros x Hx; apply WM2, WM1, Hx|].
  split; [exact MI2|]. split; [exact FR2|]. split; [exact ST2|].
  split; [apply C12; [exact LC01 | right; lia]|].
  split; [apply C12; [exact LC11 | right; lia]|].
  split; [apply C12; [exact TT | left; cbn [cells_size csize]; lia]|].
  split; [apply C12; [exact CC | left; cbn [cells_size csize]; lia]|].
  split; [apply C12; [exact AA | left; cbn [cells_size csize]; lia]|].
  split; [exact WPL|]. split; [exact WPF|]. exact WPW.
Qed.

(* 0x142cc .. check_arity, check_arity's call, 0x142d4 .. check_words. *)
Lemma ck_arity : forall ms, ck_mid ms -> evt rsegs (w_post sp gp tp s2 s3 s6 s8 m0 lo src len text copy arr M) ms.
Proof.
  intros ms (ra2 & t0b & t1b & t2b & a0b & a1b & a2b & a3b & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & Ft & fc2 &
    m2 & T & C & Aa & wp & jsv1 & jp & -> & MU2 & WM2 & MI2 & FR2 & ST2 & LC0 & LC1 & TT & CC & AA & WPL & WPF & WPW).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (ck_img W1 m2 MU2 ck_out1) as IMG2.
  destruct (ck_wb m2 C Aa wp CC AA WPL WPF WPW) as [WB PB].
  pose proof ck_win as WIN. pose proof ck_nws as NWS. pose proof ck_as16 as AS16.
  assert (HFN : ck_fn) by exact H_fn.
  clear H_txi H_cpi H_ari H_d1 H_d2 H_d3 H_d4 H_al H_cs H_AS H_sl H_ab H_fn.
  eapply evt_cut; [apply run_g_ca_ok; lia|]. intros ms3 ->.
  assert (U40 : bv_unsigned (Z_to_bv 64 (SP + 40)) = SP + 40) by (apply unsigned_lit; lia).
  assert (UAR : bv_unsigned (Z_to_bv 64 arr) = arr) by (apply unsigned_lit; lia).
  assert (WN2 : bytes_at rsegs m2 (SP + 40 + WORDS_N) (le4 (Z_to_bv 64 (Z.of_nat (length ws))))).
  { exact (send_message.sm_cell_get2 rsegs m2 (SP + 40) [C8 (Z_to_bv 64 text); C8 (Z_to_bv 64 copy); C8 (Z_to_bv 64 arr)]
      (C4 (Z_to_bv 64 (Z.of_nat (length ws)))) [CB 4 jp] 24%nat LC1 eq_refl). }
  assert (WW2 : bytes_at rsegs m2 (SP + 40 + WORDS_W) (le8 (Z_to_bv 64 arr))).
  { exact (send_message.sm_cell_get2 rsegs m2 (SP + 40) [C8 (Z_to_bv 64 text); C8 (Z_to_bv 64 copy)]
      (C8 (Z_to_bv 64 arr)) [C4 (Z_to_bv 64 (Z.of_nat (length ws))); CB 4 jp] 16%nat LC1 eq_refl). }
  assert (GGb : bytes_at rsegs m0 GOT_GUARD (le8 (Z_to_bv 64 GUARD))).
  { pose proof (b2_cells_bytes _ _ _ H_gg) as Hb. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (GUb : bytes_at rsegs m0 GUARD (le8 can)).
  { pose proof (b2_cells_bytes _ _ _ H_gu) as Hb. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (PRL : G_PARSED + Z.of_nat (length g_parsed_bytes) <= 0x54cb8) by (apply Z.leb_le; vm_compute; reflexivity).
  pose proof CAC as CA. unfold check_arity_contract, CHECK_ARITY, CHECK_ARITY_K in CA.
  eapply evt_cut.
  { eapply CA with (lo := lo) (t := Z.of_nat (length ws)) (q := q) (nc := nc) (fn0 := fn0) (ww := Z_to_bv 64 arr)
      (p0 := Z_to_bv 64 (nth 0 wp 0)) (v := nth 0 ws []) (can := can).
    - exact MI2.
    - exact ST2.
    - lia.
    - unfold IMG_END. lia.
    - apply IMG2; [exact GGb | unfold GOT_GUARD; lia | rewrite length_le8; unfold GOT_GUARD; lia].
    - apply IMG2; [exact GUb | unfold GUARD; lia | rewrite length_le8; unfold GUARD; lia].
    - apply IMG2; [exact H_par | unfold G_PARSED; lia | exact PRL].
    - apply IMG2; [exact H_grec | unfold GOT_GREC; lia | rewrite length_le8; unfold GOT_GREC; lia].
    - exact (proj1 H_nc).
    - apply IMG2; [exact (proj2 H_nc) | unfold G_REC, REC_NCALLS; lia | rewrite length_le4; unfold G_REC, REC_NCALLS; lia].
    - intros Hp. destruct (HFN Hp) as [Hf Hb]. split; [exact Hf|].
      apply IMG2; [exact Hb | unfold G_REC, REC_CALLS, CALL_FN; lia |
        rewrite length_le4; unfold G_REC, REC_CALLS, CALL_FN; lia].
    - apply IMG2; [exact H_gq | unfold GOT_GQUIT; lia | rewrite length_le8; unfold GOT_GQUIT; lia].
    - exact (proj1 H_q).
    - apply IMG2; [exact (proj2 H_q) | unfold G_QUIT; lia | rewrite length_le4; unfold G_QUIT; lia].
    - lia.
    - rewrite U40. exact WN2.
    - rewrite U40. unfold outside_stack. cbn [disjoint_from]. split; [right; unfold WORDS_N; lia | exact Logic.I].
    - rewrite U40. exact WW2.
    - rewrite U40. unfold outside_stack. cbn [disjoint_from]. split; [right; unfold WORDS_W; lia | exact Logic.I].
    - intros Hn. assert (Hn' : (length ws <> 0)%nat) by lia.
      destruct (nth_error wp 0) as [p0|] eqn:Ep.
      2: { exfalso. apply nth_error_None in Ep. lia. }
      destruct (nth_error ws 0) as [w0|] eqn:Ew.
      2: { exfalso. apply nth_error_None in Ew. lia. }
      rewrite (b2_nth wp 0 p0 0 Ep). rewrite (b2_nth ws 0 w0 [] Ew).
      destruct (WB 0%nat p0 w0 Ep Ew) as (Bw & P1 & P2).
      assert (UP : bv_unsigned (Z_to_bv 64 p0) = p0) by (apply unsigned_lit; lia).
      pose proof (PB 0%nat p0 Ep) as PB0. replace (arr + 8 * Z.of_nat 0) with arr in PB0 by lia.
      unfold word_slot. rewrite UAR, UP.
      split; [exact PB0|].
      split; [unfold outside_stack; cbn [disjoint_from]; split; [left; lia | exact Logic.I]|].
      split; [split; [exact Bw | exact (WIN w0 eq_refl)]|].
      unfold outside_stack. cbn [disjoint_from]. split; [left; lia | exact Logic.I].
    - exact H_aro. }
  intros ms4 (t0c & t1c & t2c & a0c & a1c & a2c & a3c & a4c & a5c & a6c & a7c & t3c & t4c & t5c & t6c & m3 & -> & MU3 &
    WM3 & MI3 & ST3).
  rewrite (SlotEnd.se_ret_pc 0x142d4 eq_refl).
  eapply evt_cut; [apply run_g_cw_ok; lia|]. intros ms5 ->. apply evt_done.
  assert (C23 : forall a cs, rw_cells rsegs m2 a cs -> a + Z.of_nat (cells_size cs) <= lo \/ SP <= a ->
            rw_cells rsegs m3 a cs).
  { intros a cs H Ha. apply (b2_cells _ m2 m3 a cs MU3 H). intros i Hi. apply b2_out1. lia. }
  exists t0c, t1c, t2c, a1c, a2c, a3c, a4c, a5c, a6c, a7c, t3c, t4c, t5c, t6c, Ft, fc2, m3, T, C, Aa, wp, jsv1, jp.
  split; [reflexivity|].
  split.
  { apply (b2_munch W1 [(lo, SP)] W1 m0 m2 m3 MU2 MU3).
    intros x Hx. split; [exact Hx|]. cbn [Frame.outside] in Hx |- *. destruct Hx as (X1 & X2 & X3 & X4 & _).
    split; [lia | exact Logic.I]. }
  split; [intros x Hx; apply WM3, WM2, Hx|].
  split; [exact MI3|]. split; [exact FR2|].
  split; [apply C23; [exact LC0 | right; lia]|].
  split; [apply C23; [exact LC1 | right; lia]|].
  split; [apply C23; [exact TT | left; cbn [cells_size csize]; lia]|].
  split; [apply C23; [exact CC | left; cbn [cells_size csize]; lia]|].
  split; [apply C23; [exact AA | left; cbn [cells_size csize]; lia]|].
  split; [exact WPL|]. split; [exact WPF|]. exact WPW.
Qed.

Lemma ck_evt : forall ms, SlotWords.sw_post sp gp tp s2 s3 s6 s8 F fc m0 lo src len text copy arr M ms ->
  evt rsegs (w_post sp gp tp s2 s3 s6 s8 m0 lo src len text copy arr M) ms.
Proof. intros ms H. eapply evt_cut; [exact (ck_reply ms H) | exact ck_arity]. Qed.

End CK.

Lemma ck_evt_holds : ck_spec.
Proof.
  unfold ck_spec. cbv zeta.
  intros sp gp tp s2 s3 s6 s8 F fc m0 lo src len text copy arr M can ans rep xr slack xa nc fn0 q.
  intros H_lo H_LOS H_SPH H_TS H_len H_src H_L0 H_tx H_cp H_ar H_AS CRC CAC H_M H_txi H_cpi H_ari H_d1 H_d2 H_d3
    H_d4 H_al H_fc H_tk H_gg H_gu H_cs H_grec H_ans H_nr H_rp H_rs H_sh H_rnz H_rb H_xr H_sl H_ro H_ab H_aok H_rok
    H_par H_nc H_fn H_gq H_q H_aro ms Hms.
  eapply ck_evt; eassumption.
Qed.
