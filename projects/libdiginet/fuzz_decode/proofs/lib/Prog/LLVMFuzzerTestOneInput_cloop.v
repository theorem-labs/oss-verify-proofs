(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode: cloop_holds, the proof of LLVMFuzzerTestOneInput_seg2.cloop_stmt, the cursor loop
   of LLVMFuzzerTestOneInput (plain image) from its head 0x12ddc after k passes to its exit 0x13024. One pass:
   cstep_stmt to 0x12ef8, memset (&msg, 0, 40), r = diginet_msg_next (&c, &msg), check_cursor_step (&m, r, &c),
   steps++, check_cursor_message (body, &m, &msg) when m.code = 1, the exit at 0x12f40 when m.code <> 1 and at >= len,
   the latch (status = m.status_out, at = m.next) and the exit at 0x12f50 when steps > len. The model facts the
   contracts need come from DgnLib.diginet_msg_next_msg_step and DgnAgreeCursor (cloop_facts_hold); the loop is an
   induction on len + 1 - k. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib DgnDecHarness DgnAgreeCursor.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog Require Import memset_c memcpy_c DgnLayout
  diginet_cursor_init_c diginet_msg_next_c diginet_personality_of_c diginet_decoder_init_c diginet_decoder_next_c
  check_cursor_step_c check_cursor_message_c check_events_step_c check_events_fields_c
  LLVMFuzzerTestOneInput_seg LLVMFuzzerTestOneInput_seg2.
Import ListNotations.
Open Scope Z_scope.

(* ---- frame pieces ---- *)

Lemma cloop_app : forall m A cs1 cs2, rw_cells rsegs m A cs1 ->
  rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2 -> rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros m A cs1 cs2 [[W1 B1] (R1a & R1b & R1)] [[W2 B2] (R2a & R2b & R2)].
  split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|].
    rewrite cells_bytes_length by exact W1. exact B2.
  - rewrite cells_size_app. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z_lt_le_dec i (Z.of_nat (cells_size cs1))) as [H|H]; [apply R1; lia|].
    replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia.
    apply R2. lia.
Qed.

Lemma cloop_split : forall m A cs1 cs2, rw_cells rsegs m A (cs1 ++ cs2) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[W B] (Ra & Rb & R)].
  apply cells_wf_app in W as [W1 W2]. rewrite cells_bytes_app in B. apply bytes_at_app in B as [B1 B2].
  rewrite cells_bytes_length in B2 by exact W1. rewrite cells_size_app in Rb, R.
  pose proof (cells_bytes_length cs1 W1) as L1.
  pose proof (bytes_at_bound rsegs _ _ _ B2) as BB2.
  rewrite cells_bytes_length in BB2 by exact W2.
  split.
  - unfold rw_cells, cells_at, wr_at. split; [split; assumption|].
    split; [lia|]. split; [lia|]. intros i Hi. apply R. lia.
  - unfold rw_cells, cells_at, wr_at. split; [split; assumption|].
    split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia.
    apply R. lia.
Qed.

Lemma cloop_mid : forall m A pre mid post, rw_cells rsegs m A (pre ++ mid ++ post) ->
  ro_cells rsegs m (A + Z.of_nat (cells_size pre)) mid.
Proof.
  intros m A pre mid post H. apply cloop_split in H as [_ H]. apply cloop_split in H as [[H _] _]. exact H.
Qed.

Lemma cloop_mt : forall lo hi W m0 m1 m2, munch [(lo, hi)] m0 m1 -> munch W m1 m2 ->
  (forall x, outside [(lo, hi)] x -> outside W x) -> munch [(lo, hi)] m0 m2.
Proof. intros lo hi W m0 m1 m2 H1 H2 Hs. eapply munch_trans; [exact H1|]. eapply munch_weaken; [|exact H2]. exact Hs. Qed.

(* ---- the model ---- *)

Lemma cloop_bzl_range : forall bb, Forall (fun x => 0 <= x < 256) (bzl bb).
Proof.
  intros bb. unfold bzl. apply Forall_forall. intros x Hx. apply in_map_iff in Hx as (y & <- & _).
  pose proof (bz_range y) as H. change (2 ^ 8) with 256 in H. exact H.
Qed.

Lemma cloop_code_int : forall b len pos st, -2^31 <= sm_code (spec_msg_step b len pos st) < 2^31.
Proof.
  intros b len pos st. unfold spec_msg_step; cbv beta zeta.
  split_ifs; cbn; unfold SPEC_E_TRUNCATED, SPEC_E_STATUS, SPEC_E_NO_STATUS; lia.
Qed.

Lemma cloop_status_out : forall b len pos st, Forall (fun x => 0 <= x < 256) b -> lp_st st ->
  lp_st (sm_status_out (spec_msg_step b len pos st)).
Proof.
  intros b len pos st Hb Hs. unfold lp_st in *. pose proof (byte_at_range b pos Hb) as Hl.
  unfold spec_msg_step; cbv beta zeta.
  split_ifs; cbn; bools; lia.
Qed.

Lemma cloop_status_msg : forall b len pos st, Forall (fun x => 0 <= x < 256) b -> lp_st st -> 0 <= pos ->
  0 <= sm_status (spec_msg_step b len pos st) < 256 /\
  (sm_status (spec_msg_step b len pos st) = 240 -> sm_sysex_at (spec_msg_step b len pos st) <> 0).
Proof.
  intros b len pos st Hb Hs Hp. unfold lp_st in *. pose proof (byte_at_range b pos Hb) as Hl.
  unfold spec_msg_step; cbv beta zeta.
  split_ifs; cbn; bools; lia.
Qed.

Lemma cloop_next_range : forall b len pos st, 0 <= pos <= len ->
  0 <= sm_next (spec_msg_step b len pos st) <= len.
Proof.
  intros b len pos st Hp. destruct (Z.eq_dec (sm_code (spec_msg_step b len pos st)) 0) as [E|N].
  - apply spec_msg_step_end in E. destruct (spec_msg_step_end_fields b len pos st E) as [-> _]. lia.
  - pose proof (spec_msg_step_progress b len pos st N). lia.
Qed.

Lemma cloop_chan_nosx : forall b start st status run d,
  writes_sysex (mr_kind (chan_step b start st status run d)) = false.
Proof.
  intros. unfold chan_step.
  destruct (_ <? _)%nat; [reflexivity|]. destruct (0x80 <=? _); [reflexivity|].
  destruct (_ && _); reflexivity.
Qed.

Lemma cloop_sysex_pos : forall bb pos st,
  writes_sysex (mr_kind (msg_step bb pos st)) = true -> (0 < mr_sysex (msg_step bb pos st))%nat.
Proof.
  intros bb pos st. unfold msg_step.
  destruct (length bb <=? pos)%nat; [cbn; discriminate|].
  destruct (at8 bb pos =? 0xf0); [destruct (find_f7 _); cbn; [lia | discriminate]|].
  destruct (0xf0 <=? at8 bb pos); [cbn; discriminate|].
  destruct (0x80 <=? at8 bb pos); [rewrite cloop_chan_nosx; discriminate|].
  destruct (st =? 0); [cbn; discriminate | rewrite cloop_chan_nosx; discriminate].
Qed.

(* ---- one call of diginet_msg_next on the body, in the harness's terms ---- *)

Lemma cloop_bridge : forall bb pos st m,
  diginet_msg_next (map bz bb) (DgnCursor (Z.of_nat (length bb)) (Z.of_nat pos) st) m =
  (mr_code (msg_step bb pos st), msg_after (msg_step bb pos st) m,
   DgnCursor (Z.of_nat (length bb)) (Z.of_nat (mr_pos (msg_step bb pos st))) (mr_st (msg_step bb pos st))).
Proof. intros. exact (diginet_msg_next_msg_step (map bz bb) bb pos st m (holds_body_map bb)). Qed.

Lemma cloop_agree : forall bb pos st, 0 <= pos ->
  mr_code (msg_step bb (Z.to_nat pos) st) = sm_code (spec_msg_step (bzl bb) (Z.of_nat (length bb)) pos st) /\
  Z.of_nat (mr_pos (msg_step bb (Z.to_nat pos) st)) = sm_next (spec_msg_step (bzl bb) (Z.of_nat (length bb)) pos st) /\
  mr_st (msg_step bb (Z.to_nat pos) st) = sm_status_out (spec_msg_step (bzl bb) (Z.of_nat (length bb)) pos st) /\
  (sm_code (spec_msg_step (bzl bb) (Z.of_nat (length bb)) pos st) = 1 ->
   check_cursor_message_ok (spec_msg_step (bzl bb) (Z.of_nat (length bb)) pos st)
     (msg_after (msg_step bb (Z.to_nat pos) st) dgn_msg_zero) = true).
Proof.
  intros bb pos st Hp.
  pose proof (cloop_bridge bb (Z.to_nat pos) st dgn_msg_zero) as E. rewrite Z2Nat.id in E by lia.
  pose proof (cursor_step_checks (bzl bb) (Z.of_nat (length bb)) pos st dgn_msg_zero _ _ _ (cloop_bzl_range bb) E)
    as [_ C2].
  destruct (diginet_msg_next_step (bzl bb) (Z.of_nat (length bb)) pos st dgn_msg_zero _ _ _ (cloop_bzl_range bb) E)
    as [Hr [Hc _]].
  injection Hc as Hp' Hs'.
  split; [exact Hr|]. split; [exact Hp'|]. split; [exact Hs'|].
  intros H1. rewrite H1 in C2. cbn in C2. exact C2.
Qed.

(* ---- the message diginet_msg_next leaves in the zeroed msg ---- *)

Lemma cloop_msg_cells_size : forall body mj r, cells_size (msg_cells body mj r) = 40%nat.
Proof.
  intros. unfold msg_cells. destruct (is_end r); [reflexivity|].
  destruct (writes_len (mr_kind r)); reflexivity.
Qed.

Lemma cloop_msg_bytes : forall body r,
  (writes_sysex (mr_kind r) = true -> (0 < mr_sysex r)%nat) ->
  cells_bytes (dmsg_cells body (repeat (b8 0) 4) (msg_after r dgn_msg_zero)) =
  cells_bytes (msg_cells body (repeat (b8 0) 40) r).
Proof.
  intros body [k st0 p st sta run d1 d2 sx sxl ln] H.
  unfold msg_cells, dmsg_cells, msg_after, is_end, sysex_ptr.
  destruct k; cbn [mr_kind mr_status mr_running mr_d1 mr_d2 mr_sysex mr_sysex_len mr_start mr_len
    writes_status writes_running writes_sysex writes_len dm_status dm_running dm_d1 dm_d2 dm_sysex dm_sysex_len
    dm_offset dm_len dgn_msg_zero] in *.
  all: try reflexivity.
  - specialize (H eq_refl). destruct (Z.of_nat sx =? 0) eqn:E; [lia|]. reflexivity.
Qed.

Lemma cloop_msg_ro : forall m A body r,
  (writes_sysex (mr_kind r) = true -> (0 < mr_sysex r)%nat) ->
  ro_cells rsegs m A (msg_cells body (repeat (b8 0) 40) r) ->
  ro_cells rsegs m A (dmsg_cells body (repeat (b8 0) 4) (msg_after r dgn_msg_zero)).
Proof.
  intros m A body r H [Hwf Hb]. split.
  - cbn. repeat split.
  - rewrite cloop_msg_bytes by exact H. exact Hb.
Qed.

(* the facts of one pass the walk uses: M the harness's step, R the library's *)
Definition cloop_facts (bb : list byte) (pos status : Z) (M : spec_msg) (R : msg_res) : Prop :=
  R = msg_step bb (Z.to_nat pos) status /\
  mr_code R = sm_code M /\ Z.of_nat (mr_pos R) = sm_next M /\ mr_st R = sm_status_out M /\
  -2^31 <= sm_code M < 2^31 /\
  0 <= sm_next M <= Z.of_nat (length bb) /\ lp_st (sm_status_out M) /\
  (sm_code M = 1 -> check_cursor_message_ok M (msg_after R dgn_msg_zero) = true) /\
  0 <= sm_status M < 256 /\ (sm_status M = 240 -> sm_sysex_at M <> 0) /\
  (writes_sysex (mr_kind R) = true -> (0 < mr_sysex R)%nat).

Lemma cloop_facts_hold : forall bb pos status,
  0 <= pos <= Z.of_nat (length bb) -> lp_st status ->
  cloop_facts bb pos status (spec_msg_step (bzl bb) (Z.of_nat (length bb)) pos status)
    (msg_step bb (Z.to_nat pos) status).
Proof.
  intros bb pos status Hp Hs.
  destruct (cloop_agree bb pos status ltac:(lia)) as (A1 & A2 & A3 & A4).
  destruct (cloop_status_msg (bzl bb) (Z.of_nat (length bb)) pos status (cloop_bzl_range bb) Hs ltac:(lia))
    as [B1 B2].
  split; [reflexivity|]. split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
  split; [apply cloop_code_int|]. split; [apply cloop_next_range; lia|].
  split; [apply cloop_status_out; [apply cloop_bzl_range | exact Hs]|].
  split; [exact A4|]. split; [exact B1|]. split; [exact B2|]. apply cloop_sysex_pos.
Qed.

(* ---- the loop's head after k passes (cloop_stmt's conclusion) ---- *)
Definition cloop_head (Q : machine_state -> Prop) (x3 x4 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 : word -> option byte) (Sp lo body : Z) (bb j0 : list byte) (w8 w10 : word) (saved : list cell)
    (k : Z) : Prop :=
  forall (pos status : Z)
    (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x26 x28 x29 x30 x31 : word)
    (m : word -> option byte) (mj jA cpad : list byte),
  0 <= k <= Z.of_nat (length bb) -> 0 <= pos <= Z.of_nat (length bb) -> lp_st status ->
  munch (loop_fp lo Sp) m0 m -> wmono rsegs m0 m -> mem_inv rsegs m -> stk rsegs m lo Sp ->
  bytes_at rsegs m body bb ->
  rw_cells rsegs m Sp (fr_head j0 w8 w10 body ++ CB 56 mj :: CB 224 jA ::
    cursor_cells body (Z.of_nat (length bb)) (Z.to_nat pos) status ++ CB 7 cpad :: saved) ->
  evt rsegs Q
    (MS (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 (Z_to_bv 64 status) x9 x10 x11 x12 x13 x14 x15 x16 x17
           (Z_to_bv 64 (Z.of_nat (length bb))) (Z_to_bv 64 k) x20 (Z_to_bv 64 body)
           (Z_to_bv 64 (- Z.of_nat (length bb))) (Z_to_bv 64 240) (Z_to_bv 64 247) (Z_to_bv 64 pos) x26
           (Z_to_bv 64 241) x28 x29 x30 x31)
        F (Z_to_bv 64 0x12ddc) fc None m (seg_rom rsegs)).

(* the frame in a pass: m (Mc), 144 bytes, msg at +232 (Gc), d (40 bytes), c at +312 (Cc), its padding, saved *)
Definition cloop_big (j0 : list byte) (w8 w10 : word) (body : Z) (Mc : list cell) (a1 : list byte)
    (Gc : list cell) (a3 : list byte) (Cc : list cell) (cpad : list byte) (saved : list cell) : list cell :=
  fr_head j0 w8 w10 body ++ Mc ++ CB 144 a1 :: Gc ++ CB 40 a3 :: Cc ++ CB 7 cpad :: saved.

Lemma cloop_list5 : forall (H Mc Gc Cc S : list cell) (a b c : cell),
  H ++ Mc ++ a :: Gc ++ b :: Cc ++ c :: S = H ++ (Mc ++ a :: Gc ++ b :: Cc ++ [c]) ++ S.
Proof. intros. repeat first [rewrite <- app_assoc | rewrite <- app_comm_cons]. reflexivity. Qed.

Lemma cloop_list2 : forall (H Gc T : list cell) (x a b : cell),
  H ++ x :: a :: Gc ++ b :: T = (H ++ [x]) ++ ([a] ++ Gc ++ [b]) ++ T.
Proof. intros. repeat first [rewrite <- app_assoc | rewrite <- app_comm_cons]. reflexivity. Qed.

Ltac cloop_sz := repeat first [rewrite cells_size_app | progress cbn [cells_size csize]].

Lemma cloop_to_head : forall m Sp j0 w8 w10 body Mc a1 Gc a3 Cc cpad saved,
  cells_size Mc = 56%nat -> cells_size Gc = 40%nat ->
  rw_cells rsegs m Sp (cloop_big j0 w8 w10 body Mc a1 Gc a3 Cc cpad saved) ->
  rw_cells rsegs m Sp (fr_head j0 w8 w10 body ++ CB 56 (cells_bytes Mc) ::
    CB 224 (a1 ++ cells_bytes Gc ++ a3) :: Cc ++ CB 7 cpad :: saved).
Proof.
  intros m Sp j0 w8 w10 body Mc a1 Gc a3 Cc cpad saved SM SG H. unfold cloop_big in H.
  apply rw_cells_merge in H. rewrite SM in H.
  rewrite cloop_list2 in H. apply rw_cells_merge in H.
  assert (E : cells_size ([CB 144 a1] ++ Gc ++ [CB 40 a3]) = 224%nat) by (cloop_sz; rewrite SG; reflexivity).
  rewrite E in H. rewrite !cells_bytes_app in H. cbn [cells_bytes cbytes] in H. rewrite !app_nil_r in H.
  rewrite <- app_assoc in H. exact H.
Qed.

Lemma cloop_big_pieces : forall m Sp j0 w8 w10 body Mc a1 Gc a3 Cc cpad saved,
  cells_size Mc = 56%nat -> cells_size Gc = 40%nat ->
  rw_cells rsegs m Sp (cloop_big j0 w8 w10 body Mc a1 Gc a3 Cc cpad saved) ->
  rw_cells rsegs m (Sp + 32) Mc /\ rw_cells rsegs m (Sp + 232) Gc /\ rw_cells rsegs m (Sp + 312) Cc.
Proof.
  intros m Sp j0 w8 w10 body Mc a1 Gc a3 Cc cpad saved SM SG H. unfold cloop_big in H.
  apply cloop_split in H as [_ H]. change (Z.of_nat (cells_size (fr_head j0 w8 w10 body))) with 32 in H.
  apply cloop_split in H as [HM H]. rewrite SM in H.
  change (CB 144 a1 :: Gc ++ CB 40 a3 :: Cc ++ CB 7 cpad :: saved)
    with ([CB 144 a1] ++ Gc ++ CB 40 a3 :: Cc ++ CB 7 cpad :: saved) in H.
  apply cloop_split in H as [_ H]. change (Z.of_nat (cells_size [CB 144 a1])) with 144 in H.
  apply cloop_split in H as [HG H]. rewrite SG in H.
  change (CB 40 a3 :: Cc ++ CB 7 cpad :: saved) with ([CB 40 a3] ++ Cc ++ CB 7 cpad :: saved) in H.
  apply cloop_split in H as [_ H]. change (Z.of_nat (cells_size [CB 40 a3])) with 40 in H.
  apply cloop_split in H as [HC _].
  replace (Sp + 32 + Z.of_nat 56 + 144) with (Sp + 232) in HG by lia.
  replace (Sp + 32 + Z.of_nat 56 + 144 + Z.of_nat 40 + 40) with (Sp + 312) in HC by lia.
  split; [exact HM|]. split; [exact HG | exact HC].
Qed.

Lemma cloop_ro : forall m A cs, rw_cells rsegs m A cs -> ro_cells rsegs m A cs.
Proof. intros m A cs [H _]. exact H. Qed.

(* the frame of cstep's end in pieces around msg (Sp + 232) and c (Sp + 312) *)
Lemma cloop_pieces : forall m Sp (H Mc : list cell) (jA : list byte) (Cc S : list cell) (cpad : list byte),
  cells_size H = 32%nat -> cells_size Mc = 56%nat -> cells_size Cc = 25%nat ->
  rw_cells rsegs m Sp (H ++ Mc ++ CB 224 jA :: Cc ++ CB 7 cpad :: S) ->
  rw_cells rsegs m Sp (H ++ Mc ++ [CB 144 (firstn 144 jA)]) /\
  rw_cells rsegs m (Sp + 232) [CB 40 (firstn 40 (skipn 144 jA))] /\
  rw_cells rsegs m (Sp + 272) [CB 40 (firstn 40 (skipn 40 (skipn 144 jA)))] /\
  rw_cells rsegs m (Sp + 312) Cc /\
  rw_cells rsegs m (Sp + 337) (CB 7 cpad :: S).
Proof.
  intros m Sp H Mc jA Cc S cpad SH SM SC FR.
  rewrite app_assoc in FR.
  apply (rw_cells_split_CB rsegs m Sp (H ++ Mc) 224 jA (Cc ++ CB 7 cpad :: S) [144; 40; 40]%nat) in FR;
    [|reflexivity].
  cbn [mk_CB_cells app] in FR.
  destruct (cloop_split m Sp ((H ++ Mc) ++ [CB 144 (firstn 144 jA)]) _ ltac:(rewrite <- app_assoc; exact FR))
    as [P1 R1].
  rewrite <- app_assoc in P1.
  assert (E1 : Z.of_nat (cells_size ((H ++ Mc) ++ [CB 144 (firstn 144 jA)])) = 232)
    by (rewrite !cells_size_app, SH, SM; reflexivity).
  rewrite E1 in R1.
  change (CB 40 (firstn 40 (skipn 144 jA)) :: CB 40 (firstn 40 (skipn 40 (skipn 144 jA))) :: Cc ++ CB 7 cpad :: S)
    with ([CB 40 (firstn 40 (skipn 144 jA))] ++ [CB 40 (firstn 40 (skipn 40 (skipn 144 jA)))] ++ Cc ++ CB 7 cpad :: S)
    in R1.
  apply cloop_split in R1 as [P2 R2]. change (Z.of_nat (cells_size [CB 40 (firstn 40 (skipn 144 jA))])) with 40 in R2.
  apply cloop_split in R2 as [P3 R3].
  change (Z.of_nat (cells_size [CB 40 (firstn 40 (skipn 40 (skipn 144 jA)))])) with 40 in R3.
  apply cloop_split in R3 as [P4 P5]. rewrite SC in P5.
  replace (Sp + 232 + 40) with (Sp + 272) in P3 by lia.
  replace (Sp + 232 + 40 + 40) with (Sp + 312) in P4 by lia.
  replace (Sp + 232 + 40 + 40 + Z.of_nat 25) with (Sp + 337) in P5 by lia.
  split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4 | exact P5].
Qed.

Lemma cloop_join : forall m Sp (H Mc Gc Cc S : list cell) (a1 a3 cpad : list byte),
  cells_size H = 32%nat -> cells_size Mc = 56%nat -> cells_size Gc = 40%nat -> cells_size Cc = 25%nat ->
  rw_cells rsegs m Sp (H ++ Mc ++ [CB 144 a1]) -> rw_cells rsegs m (Sp + 232) Gc ->
  rw_cells rsegs m (Sp + 272) [CB 40 a3] -> rw_cells rsegs m (Sp + 312) Cc ->
  rw_cells rsegs m (Sp + 337) (CB 7 cpad :: S) ->
  rw_cells rsegs m Sp (H ++ Mc ++ CB 144 a1 :: Gc ++ CB 40 a3 :: Cc ++ CB 7 cpad :: S).
Proof.
  intros m Sp H Mc Gc Cc S a1 a3 cpad SH SM SG SC P1 P2 P3 P4 P5.
  assert (X4 : rw_cells rsegs m (Sp + 312) (Cc ++ CB 7 cpad :: S)).
  { apply cloop_app; [exact P4|]. rewrite SC. replace (Sp + 312 + Z.of_nat 25) with (Sp + 337) by lia. exact P5. }
  assert (X3 : rw_cells rsegs m (Sp + 272) ([CB 40 a3] ++ Cc ++ CB 7 cpad :: S)).
  { apply cloop_app; [exact P3|]. change (Z.of_nat (cells_size [CB 40 a3])) with 40.
    replace (Sp + 272 + 40) with (Sp + 312) by lia. exact X4. }
  assert (X2 : rw_cells rsegs m (Sp + 232) (Gc ++ [CB 40 a3] ++ Cc ++ CB 7 cpad :: S)).
  { apply cloop_app; [exact P2|]. rewrite SG. replace (Sp + 232 + Z.of_nat 40) with (Sp + 272) by lia. exact X3. }
  assert (X1 : rw_cells rsegs m Sp ((H ++ Mc ++ [CB 144 a1]) ++ Gc ++ [CB 40 a3] ++ Cc ++ CB 7 cpad :: S)).
  { apply cloop_app; [exact P1|]. rewrite !cells_size_app, SH, SM.
    change (Z.of_nat (32 + (56 + cells_size [CB 144 a1]))) with 232. exact X2. }
  rewrite <- !app_assoc in X1. exact X1.
Qed.

Lemma cloop_exit : forall (Q : machine_state -> Prop) (x3 x4 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 : word -> option byte) (Sp lo body : Z) (bb j0 : list byte) (w8 w10 : word) (saved : list cell)
    (r1 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r19 r20 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 : word)
    (m : word -> option byte) (Mc Gc Cc : list cell) (a1 a3 cpad : list byte),
  cexit Q x3 x4 F fc m0 Sp lo body bb j0 w8 w10 saved ->
  cells_size Mc = 56%nat -> cells_size Gc = 40%nat -> cells_size Cc = 25%nat ->
  munch (loop_fp lo Sp) m0 m -> wmono rsegs m0 m -> mem_inv rsegs m -> stk rsegs m lo Sp ->
  bytes_at rsegs m body bb ->
  rw_cells rsegs m Sp (cloop_big j0 w8 w10 body Mc a1 Gc a3 Cc cpad saved) ->
  evt rsegs Q
    (MS (mkR r1 (Z_to_bv 64 Sp) x3 x4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17
           (Z_to_bv 64 (Z.of_nat (length bb))) r19 r20 (Z_to_bv 64 body) r22 r23 r24 r25 r26 r27 r28 r29 r30 r31)
        F (Z_to_bv 64 0x13024) fc None m (seg_rom rsegs)).
Proof.
  intros Q x3 x4 F fc m0 Sp lo body bb j0 w8 w10 saved
    r1 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r19 r20 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31
    m Mc Gc Cc a1 a3 cpad EX SM SG SC MU WM MI ST BA FR.
  unfold cloop_big in FR. rewrite cloop_list5 in FR. apply rw_cells_merge in FR.
  assert (E : cells_size (Mc ++ CB 144 a1 :: Gc ++ CB 40 a3 :: Cc ++ [CB 7 cpad]) = 312%nat)
    by (cloop_sz; rewrite SM, SG, SC; reflexivity).
  rewrite E in FR.
  exact (EX r1 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r19 r20 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31
    m _ MU WM MI ST BA FR).
Qed.

Ltac cloop_usub := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia end.
Ltac cloop_solve_c := unfold bv_eqb, bv_ltu, bv_leu, bv_lts; cbn [negb]; cloop_usub; fold_lit_ux; solve_cond_rec.
Ltac cloop_take b := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b; [cbv iota | symmetry; cloop_solve_c]
  end.
Ltac cloop_ret := lazymatch goal with
  | |- context [ret_pc (Z_to_bv 64 ?n)] =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity])
  end.
Ltac cloop_dj := cbn [disjoint_from]; repeat split; try exact I; lia.
Ltac cloop_subfp := cbn [outside]; intros ? [? _]; repeat split; try exact I; lia.
(* carry a fact over a callee whose footprint is MU's *)
Ltac cloop_trw H MU WM :=
  let H' := fresh in pose proof (rw_cells_transport rsegs _ _ _ _ _ H MU WM ltac:(cloop_dj)) as H';
  clear H; rename H' into H.
Ltac cloop_tba H MU :=
  let H' := fresh in pose proof (bytes_at_transport rsegs _ _ _ _ _ H MU ltac:(cloop_dj)) as H';
  clear H; rename H' into H.
Ltac cloop_tst H MU WM :=
  let H' := fresh in pose proof (stk_transport_disjoint rsegs _ _ _ _ _ H MU WM ltac:(cloop_dj)) as H';
  clear H; rename H' into H.
Ltac cloop_tmu MU MU1 :=
  let H' := fresh in pose proof (cloop_mt _ _ _ _ _ _ MU MU1 ltac:(cloop_subfp)) as H';
  clear MU MU1; rename H' into MU.
Ltac cloop_twm WM WM1 :=
  let H' := fresh in pose proof (wmono_trans rsegs _ _ _ WM WM1) as H'; clear WM WM1; rename H' into WM.

(* the latch 0x12f44: s0 = status_out, s9 = next; the next pass's head or the exit *)
Lemma cloop_latch : forall (Q : machine_state -> Prop) (x3 x4 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 : word -> option byte) (Sp lo body : Z) (bb j0 : list byte) (w8 w10 : word) (saved : list cell)
    (k pos' st' : Z) (y1 y5 y6 y7 y8 y10 y11 y12 y13 y14 y15 y16 y17 y20 y25 y28 y29 y30 y31 : word)
    (m : word -> option byte) (Mc Gc : list cell) (a1 a3 cpad : list byte),
  seg_ok Sp body bb ->
  cexit Q x3 x4 F fc m0 Sp lo body bb j0 w8 w10 saved ->
  cloop_head Q x3 x4 F fc m0 Sp lo body bb j0 w8 w10 saved (k + 1) ->
  0 <= k <= Z.of_nat (length bb) -> 0 <= pos' <= Z.of_nat (length bb) -> lp_st st' ->
  cells_size Mc = 56%nat -> cells_size Gc = 40%nat ->
  munch (loop_fp lo Sp) m0 m -> wmono rsegs m0 m -> mem_inv rsegs m -> stk rsegs m lo Sp ->
  bytes_at rsegs m body bb ->
  rw_cells rsegs m Sp (cloop_big j0 w8 w10 body Mc a1 Gc a3
    (cursor_cells body (Z.of_nat (length bb)) (Z.to_nat pos') st') cpad saved) ->
  evt rsegs Q
    (MS (mkR y1 (Z_to_bv 64 Sp) x3 x4 y5 y6 y7 y8 (Z_to_bv 64 pos') y10 y11 y12 y13 y14 y15 y16 y17
           (Z_to_bv 64 (Z.of_nat (length bb))) (Z_to_bv 64 (k + 1)) y20 (Z_to_bv 64 body)
           (Z_to_bv 64 (- Z.of_nat (length bb))) (Z_to_bv 64 240) (Z_to_bv 64 247) y25 (Z_to_bv 64 st')
           (Z_to_bv 64 241) y28 y29 y30 y31)
        F (Z_to_bv 64 0x12f44) fc None m (seg_rom rsegs)).
Proof.
  intros Q x3 x4 F fc m0 Sp lo body bb j0 w8 w10 saved k pos' st'
    y1 y5 y6 y7 y8 y10 y11 y12 y13 y14 y15 y16 y17 y20 y25 y28 y29 y30 y31 m Mc Gc a1 a3 cpad
    SEG EX IH Hk Hp Hs SM SG MU WM MI ST BA FR.
  pose proof SEG as (S0 & S1 & B0 & B1 & L26).
  step. step. step.
  destruct (Z_le_gt_dec (k + 1) (Z.of_nat (length bb))) as [Hle|Hgt].
  - cloop_take true.
    unfold cloop_head in IH.
    eapply (IH pos' st') with (mj := cells_bytes Mc) (jA := a1 ++ cells_bytes Gc ++ a3) (cpad := cpad);
      [lia | exact Hp | exact Hs | exact MU | exact WM | exact MI | exact ST | exact BA | ].
    apply cloop_to_head; assumption.
  - cloop_take false. step.
    eapply cloop_exit with (Mc := Mc) (Gc := Gc)
      (Cc := cursor_cells body (Z.of_nat (length bb)) (Z.to_nat pos') st') (a1 := a1) (a3 := a3) (cpad := cpad);
      [exact EX | exact SM | exact SG | reflexivity | exact MU | exact WM | exact MI | exact ST | exact BA | exact FR].
Qed.

(* 0x12f24, check_cursor_step returned: steps++, check_cursor_message when s4 = 1, the exit at the end of the
   body, the latch *)
Lemma cloop_t2 : check_cursor_message_contract ->
  forall (Q : machine_state -> Prop) (x3 x4 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 : word -> option byte) (Sp lo body : Z) (bb j0 : list byte) (w8 w10 : word) (saved : list cell)
    (k pos status : Z) (M : spec_msg) (R : msg_res)
    (y1 y5 y6 y7 y8 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word)
    (m : word -> option byte) (a1 a3 cpad : list byte),
  seg_ok Sp body bb -> lo_ok lo Sp body bb -> cells_size saved = 104%nat ->
  cexit Q x3 x4 F fc m0 Sp lo body bb j0 w8 w10 saved ->
  cloop_head Q x3 x4 F fc m0 Sp lo body bb j0 w8 w10 saved (k + 1) ->
  0 <= k <= Z.of_nat (length bb) -> 0 <= pos <= Z.of_nat (length bb) ->
  cloop_facts bb pos status M R ->
  munch (loop_fp lo Sp) m0 m -> wmono rsegs m0 m -> mem_inv rsegs m -> stk rsegs m lo Sp ->
  bytes_at rsegs m body bb ->
  rw_cells rsegs m Sp (cloop_big j0 w8 w10 body (spec_msg_cells M) a1 (msg_cells body (repeat (b8 0) 40) R) a3
    (cursor_cells body (Z.of_nat (length bb)) (Z.to_nat (sm_next M)) (sm_status_out M)) cpad saved) ->
  evt rsegs Q
    (MS (mkR y1 (Z_to_bv 64 Sp) x3 x4 y5 y6 y7 y8 (Z_to_bv 64 (sm_next M)) y10 y11 y12 y13 y14 y15 y16 y17
           (Z_to_bv 64 (Z.of_nat (length bb))) (Z_to_bv 64 k) (Z_to_bv 64 (if sm_code M =? 1 then 1 else 0))
           (Z_to_bv 64 body) (Z_to_bv 64 (- Z.of_nat (length bb))) (Z_to_bv 64 240) (Z_to_bv 64 247)
           (Z_to_bv 64 pos) (Z_to_bv 64 (sm_status_out M)) (Z_to_bv 64 241) y28 y29 y30 y31)
        F (Z_to_bv 64 0x12f24) fc None m (seg_rom rsegs)).
Proof.
  intros CCM Q x3 x4 F fc m0 Sp lo body bb j0 w8 w10 saved k pos status M R
    y1 y5 y6 y7 y8 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m a1 a3 cpad
    SEG LO Hsv EX IH Hk Hpos FA MU WM MI ST BA FR.
  pose proof SEG as (S0 & S1 & B0 & B1 & L26). pose proof LO as (L0 & L1 & L2).
  pose proof FA as (HR & F1 & F2 & F3 & F5 & F8 & F9 & F4 & F6 & F7 & F11).
  unfold loop_fp in MU.
  step.
  destruct (sm_code M =? 1) eqn:E1; cbv iota.
  - apply Z.eqb_eq in E1.
    step. cloop_take false.
    step. step. step. step.
    pose proof (cloop_big_pieces m Sp j0 w8 w10 body _ _ _ _ _ _ saved (spec_msg_cells_size M)
      (cloop_msg_cells_size _ _ _) FR) as (PM & PG & PC).
    eapply evt_cut.
    { eapply CCM with (b := body) (p := Sp + 32) (q := Sp + 232) (lo := lo) (sm := M)
        (msg := msg_after R dgn_msg_zero) (pad := repeat (b8 0) 4).
      - exact (F4 E1).
      - exact F6.
      - exact F7.
      - exact (cloop_ro _ _ _ PM).
      - apply cloop_msg_ro; [exact F11 | exact (cloop_ro _ _ _ PG)].
      - rewrite unsigned_lit by lia. exact ST.
      - rewrite unsigned_lit by lia. unfold CHECK_CURSOR_MESSAGE_FRAME. lia.
      - right. rewrite unsigned_lit by lia. lia.
      - right. rewrite unsigned_lit by lia. lia.
      - exact MI. }
    intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 &
      -> & MU1 & WM1 & MI1 & ST1).
    rewrite unsigned_lit in MU1, ST1 by lia. unfold CHECK_CURSOR_MESSAGE_FRAME in MU1.
    cloop_ret.
    cloop_trw FR MU1 WM1. cloop_tba BA MU1. cloop_tmu MU MU1. cloop_twm WM WM1.
    step.
    eapply cloop_latch with (Mc := spec_msg_cells M) (Gc := msg_cells body (repeat (b8 0) 40) R)
      (a1 := a1) (a3 := a3) (cpad := cpad) (pos' := sm_next M) (st' := sm_status_out M) (k := k);
      [exact SEG | exact EX | exact IH | exact Hk | exact F8 | exact F9 | apply spec_msg_cells_size
      | apply cloop_msg_cells_size | exact MU | exact WM | exact MI1 | exact ST1 | exact BA | exact FR].
  - step. cloop_take true.
    step.
    destruct (Z_le_gt_dec (Z.of_nat (length bb)) pos) as [Hge|Hlt].
    + cloop_take true.
      eapply cloop_exit with (Mc := spec_msg_cells M) (Gc := msg_cells body (repeat (b8 0) 40) R)
        (Cc := cursor_cells body (Z.of_nat (length bb)) (Z.to_nat (sm_next M)) (sm_status_out M))
        (a1 := a1) (a3 := a3) (cpad := cpad);
        [exact EX | apply spec_msg_cells_size | apply cloop_msg_cells_size | reflexivity | exact MU | exact WM
        | exact MI | exact ST | exact BA | exact FR].
    + cloop_take false.
      eapply cloop_latch with (Mc := spec_msg_cells M) (Gc := msg_cells body (repeat (b8 0) 40) R)
        (a1 := a1) (a3 := a3) (cpad := cpad) (pos' := sm_next M) (st' := sm_status_out M) (k := k);
        [exact SEG | exact EX | exact IH | exact Hk | exact F8 | exact F9 | apply spec_msg_cells_size
        | apply cloop_msg_cells_size | exact MU | exact WM | exact MI | exact ST | exact BA | exact FR].
Qed.

(* 0x12ef8, cstep's end: memset (&msg, 0, 40), r = diginet_msg_next (&c, &msg), check_cursor_step (&m, r, &c) *)
Lemma cloop_t1 : memset_contract -> diginet_msg_next_contract -> check_cursor_step_contract ->
  check_cursor_message_contract ->
  forall (Q : machine_state -> Prop) (x3 x4 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 : word -> option byte) (Sp lo body : Z) (bb j0 : list byte) (w8 w10 : word) (saved : list cell)
    (k pos status : Z) (M : spec_msg) (R : msg_res)
    (r1 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r28 r29 r30 r31 : word)
    (m : word -> option byte) (jA cpad : list byte),
  seg_ok Sp body bb -> lo_ok lo Sp body bb -> cells_size saved = 104%nat ->
  cexit Q x3 x4 F fc m0 Sp lo body bb j0 w8 w10 saved ->
  cloop_head Q x3 x4 F fc m0 Sp lo body bb j0 w8 w10 saved (k + 1) ->
  0 <= k <= Z.of_nat (length bb) -> 0 <= pos <= Z.of_nat (length bb) -> lp_st status ->
  cloop_facts bb pos status M R ->
  munch (loop_fp lo Sp) m0 m -> wmono rsegs m0 m -> mem_inv rsegs m -> stk rsegs m lo Sp ->
  bytes_at rsegs m body bb ->
  rw_cells rsegs m Sp (fr_head j0 w8 w10 body ++ spec_msg_cells M ++ CB 224 jA ::
    cursor_cells body (Z.of_nat (length bb)) (Z.to_nat pos) status ++ CB 7 cpad :: saved) ->
  evt rsegs Q
    (MS (mkR r1 (Z_to_bv 64 Sp) x3 x4 r5 r6 r7 (Z_to_bv 64 status) (Z_to_bv 64 (sm_next M))
           r10 r11 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 (Z.of_nat (length bb))) (Z_to_bv 64 k)
           (Z_to_bv 64 (if sm_code M =? 1 then 1 else 0))
           (Z_to_bv 64 body) (Z_to_bv 64 (- Z.of_nat (length bb))) (Z_to_bv 64 240) (Z_to_bv 64 247)
           (Z_to_bv 64 pos) (Z_to_bv 64 (sm_status_out M)) (Z_to_bv 64 241) r28 r29 r30 r31)
        F (Z_to_bv 64 0x12ef8) fc None m (seg_rom rsegs)).
Proof.
  intros MSET MN CCS CCM Q x3 x4 F fc m0 Sp lo body bb j0 w8 w10 saved k pos status M R
    r1 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r28 r29 r30 r31 m jA cpad
    SEG LO Hsv EX IH Hk Hpos Hst FA MU WM MI ST BA FR.
  pose proof SEG as (S0 & S1 & B0 & B1 & L26). pose proof LO as (L0 & L1 & L2).
  pose proof FA as (HR & F1 & F2 & F3 & F5 & F8 & _).
  unfold loop_fp in MU.
  destruct (cloop_pieces m Sp (fr_head j0 w8 w10 body) (spec_msg_cells M) jA
    (cursor_cells body (Z.of_nat (length bb)) (Z.to_nat pos) status) saved cpad eq_refl eq_refl eq_refl FR)
    as (P1 & P2 & P3 & P4 & P5).
  clear FR.
  assert (Z1 : Z.of_nat (cells_size (fr_head j0 w8 w10 body ++ spec_msg_cells M ++ [CB 144 (firstn 144 jA)])) = 232)
    by reflexivity.
  assert (Z3 : Z.of_nat (cells_size [CB 40 (firstn 40 (skipn 40 (skipn 144 jA)))]) = 40) by reflexivity.
  (* memset (&msg, 0, 40) *)
  step. step. step. step.
  eapply evt_cut.
  { eapply MSET with (junk := firstn 40 (skipn 144 jA)).
    - rewrite !unsigned_lit by lia. exact P2.
    - exact MI. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 &
    -> & MU1 & WM1 & MI1 & G1).
  rewrite !unsigned_lit in MU1, G1 by lia.
  change (Z.to_nat 40) with 40%nat in G1. change (0 mod 256) with 0 in G1.
  cloop_ret.
  cloop_trw P1 MU1 WM1. cloop_trw P3 MU1 WM1. cloop_trw P4 MU1 WM1. cloop_trw P5 MU1 WM1.
  cloop_tba BA MU1. cloop_tst ST MU1 WM1. cloop_tmu MU MU1. cloop_twm WM WM1. clear MI P2.
  (* r = diginet_msg_next (&c, &msg) *)
  step. step. step.
  eapply evt_cut.
  { eapply MN with (c := Sp + 312) (mp := Sp + 232) (body := body) (bb := bb) (mj := repeat (Z_to_bv 8 0) 40)
      (pos := Z.to_nat pos) (st := status).
    - lia.
    - lia.
    - lia.
    - exact Hst.
    - exact P4.
    - exact BA.
    - exact G1.
    - lia.
    - lia.
    - lia.
    - exact MI1. }
  intros ms' (t0'' & t1'' & t2'' & b1 & b2 & b3 & b4 & b5 & b6 & b7 & t3'' & m2 & -> & MU2 & WM2 & MI2 & C2 & G2).
  cloop_ret.
  rewrite <- HR in C2. rewrite <- HR in G2. rewrite <- HR.
  cloop_trw P1 MU2 WM2. cloop_trw P3 MU2 WM2. cloop_trw P5 MU2 WM2.
  cloop_tba BA MU2. cloop_tst ST MU2 WM2. cloop_tmu MU MU2. cloop_twm WM WM2. clear MI1 P4 G1.
  assert (EP : mr_pos R = Z.to_nat (sm_next M)) by (rewrite <- F2, Nat2Z.id; reflexivity).
  rewrite EP, F3 in C2.
  pose proof (cloop_mid m2 Sp (fr_head j0 w8 w10 body) (spec_msg_cells M) _ P1) as RM.
  change (Z.of_nat (cells_size (fr_head j0 w8 w10 body))) with 32 in RM.
  pose proof (cloop_ro _ _ _ C2) as RC.
  pose proof (cloop_join m2 Sp (fr_head j0 w8 w10 body) (spec_msg_cells M)
    (msg_cells body (repeat (Z_to_bv 8 0) 40) R)
    (cursor_cells body (Z.of_nat (length bb)) (Z.to_nat (sm_next M)) (sm_status_out M)) saved
    (firstn 144 jA) (firstn 40 (skipn 40 (skipn 144 jA))) cpad eq_refl eq_refl (cloop_msg_cells_size _ _ _) eq_refl
    P1 G2 P3 C2 P5) as BIG.
  clear P1 P3 P5 G2 C2.
  (* check_cursor_step (&m, r, &c) *)
  step. step. step. step.
  eapply evt_cut.
  { eapply CCS with (p := Sp + 32) (c := Sp + 312) (body := body) (r := mr_code R) (lo := lo) (sm := M)
      (cur := DgnCursor (Z.of_nat (length bb)) (sm_next M) (sm_status_out M)).
    - rewrite F1. apply check_cursor_step_ok_refl.
    - exact F5.
    - rewrite F1. exact F5.
    - cbn [dc_pos]. lia.
    - exact RM.
    - exact RC.
    - rewrite unsigned_lit by lia. exact ST.
    - rewrite unsigned_lit by lia. unfold CHECK_CURSOR_STEP_FRAME. lia.
    - right. rewrite unsigned_lit by lia. lia.
    - right. rewrite unsigned_lit by lia. lia.
    - exact MI2. }
  intros ms' (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m3 &
    -> & MU3 & WM3 & MI3 & ST3).
  rewrite unsigned_lit in MU3, ST3 by lia. unfold CHECK_CURSOR_STEP_FRAME in MU3.
  cloop_ret.
  cloop_trw BIG MU3 WM3. cloop_tba BA MU3. cloop_tmu MU MU3. cloop_twm WM WM3.
  eapply (cloop_t2 CCM) with (M := M) (R := R) (a1 := firstn 144 jA) (a3 := firstn 40 (skipn 40 (skipn 144 jA)))
    (cpad := cpad) (k := k) (pos := pos) (status := status) (m := m3);
    [exact SEG | exact LO | exact Hsv | exact EX | exact IH | exact Hk | exact Hpos | exact FA | exact MU | exact WM
    | exact MI3 | exact ST3 | exact BA | exact BIG].
Qed.

(* one pass: cstep_stmt to 0x12ef8, then cloop_t1 *)
Lemma cloop_pass : memset_contract -> diginet_msg_next_contract -> check_cursor_step_contract ->
  check_cursor_message_contract -> cstep_stmt ->
  forall (Q : machine_state -> Prop) (x3 x4 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 : word -> option byte) (Sp lo body : Z) (bb j0 : list byte) (w8 w10 : word) (saved : list cell) (k : Z),
  seg_ok Sp body bb -> lo_ok lo Sp body bb -> cells_size saved = 104%nat ->
  cexit Q x3 x4 F fc m0 Sp lo body bb j0 w8 w10 saved ->
  cloop_head Q x3 x4 F fc m0 Sp lo body bb j0 w8 w10 saved (k + 1) ->
  cloop_head Q x3 x4 F fc m0 Sp lo body bb j0 w8 w10 saved k.
Proof.
  intros MSET MN CCS CCM CS Q x3 x4 F fc m0 Sp lo body bb j0 w8 w10 saved k SEG LO Hsv EX IH.
  unfold cloop_head.
  intros pos status x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x26 x28 x29 x30 x31 m mj jA cpad
    Hk Hpos Hst MU WM MI ST BA FR.
  pose proof SEG as (S0 & S1 & B0 & B1 & L26). pose proof LO as (L0 & L1 & L2).
  assert (Hs256 : 0 <= status < 256) by (unfold lp_st in Hst; lia).
  apply (CS MSET x1 x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 k) x20 x26 x28 x29 x30 x31
    F fc m Sp body pos status bb j0 mj w8 w10
    (CB 224 jA :: cursor_cells body (Z.of_nat (length bb)) (Z.to_nat pos) status ++ CB 7 cpad :: saved) Q
    SEG Hpos Hs256 BA FR MI).
  intros r1 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r28 r29 r30 r31 m1 MU1 WM1 MI1 BA1 FR1.
  unfold loop_fp in MU.
  cloop_tst ST MU1 WM1. cloop_tmu MU MU1. cloop_twm WM WM1.
  eapply (cloop_t1 MSET MN CCS CCM) with (M := spec_msg_step (bzl bb) (Z.of_nat (length bb)) pos status)
    (R := msg_step bb (Z.to_nat pos) status) (jA := jA) (cpad := cpad) (k := k) (m := m1);
    [exact SEG | exact LO | exact Hsv | exact EX | exact IH | exact Hk | exact Hpos | exact Hst
    | apply cloop_facts_hold; [exact Hpos | exact Hst] | exact MU | exact WM | exact MI1 | exact ST | exact BA1
    | exact FR1].
Qed.

Theorem cloop_holds : cloop_stmt.
Proof.
  unfold cloop_stmt.
  intros MSET MN CCS CCM CS x3 x4 F fc m0 Sp lo body bb j0 w8 w10 saved Q SEG LO Hsv EX.
  assert (H : forall (n : nat) (k : Z), (Z.to_nat (Z.of_nat (length bb) + 1 - k) <= n)%nat ->
    cloop_head Q x3 x4 F fc m0 Sp lo body bb j0 w8 w10 saved k).
  { induction n as [|n IHn]; intros k Hn.
    - unfold cloop_head. intros. lia.
    - apply (cloop_pass MSET MN CCS CCM CS); [exact SEG | exact LO | exact Hsv | exact EX |].
      apply IHn. lia. }
  intros k. exact (H _ k (le_n _)).
Qed.
