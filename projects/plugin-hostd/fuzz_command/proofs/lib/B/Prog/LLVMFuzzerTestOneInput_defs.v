(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the boundary states and segment statements of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86530), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (the CL_*_stmtX statements: from a point of the function to its return, under the entry's context) and A/ACf5.v (rtcx, rt_base: the entry's facts bundled once). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep
  CmdObj CmdRo CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import rec_clear_c send_message_c check_reply_c
  check_arity_c check_words_c check_refusal_c check_round_trip_c verbs_receive_c LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require SlotSpec HarnessProps.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs StrFun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* The frame (addi sp,sp,-256 at 0x86530) and the registers it saves, at entry sp - 8, - 16, ..., - 104
   (0x86534 .. 0x86564): ra, s0, s1, s2, ..., s11. *)
Definition LT_FRAME : Z := 256.
Definition LT_SAVED : list (bv 5) := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
(* s2, the bit mask of {\t, \n, \r, space} the trim loop tests (0x865f4, 0x86614, 0x86628: 0x800013 << 9) *)
Definition LT_MASK : Z := 0x100002600.
(* the shadow offset, the code table, the address of the code count and the count it holds (rec_codes 0x21be0,
   rec_ncodes 0x21d00 holds 58; the GOT words 0xa6bd8 / 0xa6bd0) *)
Definition LT_SB : Z := 0x7fff8000.
Definition LT_CODES : Z := 0x21be0.
Definition LT_NCODESA : Z := 0x21d00.
Definition LT_NCODES : Z := 58.
(* The ten words the entry stores below the struct before the top loop (0x8659c .. 0x86650) that a pass reads,
   with sp = entry sp - 256 and G = &g_rec: (&rec_ncodes & 7) + 3 (the slow path of rec_ncodes' load4 check,
   0x86a94), ((G + 4) & 7) + 3 (the slow path of g_rec.code's store4 check, 0x86ab0), the shadow cell of G + 4, the
   code table and its complement (UBSan's pointer-overflow test, 0x86720), the shadow cell of rec_ncodes, its
   address, and the shadow cells of G, G + 952 and G + 944. The words at sp + 8, 16, 24 (G + 4, G + 952, G + 944)
   are read only by the ASan error calls, which the walk never reaches. *)
Definition LT_SLOTS : list (Z * Z) :=
  [(32, 3); (40, 7); (48, LT_SB + (A_G_REC + 4) / 8); (56, LT_CODES); (64, 2 ^ 64 - 1 - LT_CODES);
   (72, LT_SB + LT_NCODESA / 8); (80, LT_NCODESA); (88, LT_SB + A_G_REC / 8);
   (96, LT_SB + (A_G_REC + 952) / 8); (104, LT_SB + (A_G_REC + 944) / 8)].
(* the other frame words: g_rec.host_settings before the send (0x8673c; g_rec.state before the send stays in s5,
   0x866e4), and the struct words w (text, copy, the pointer array, the count; 0x8677c .. 0x86940) *)
Definition LT_HOSTB : Z := 112.
Definition LT_W : Z := 120.
(* the points of the listing (offsets from BASE = 0x86530) at which a segment starts or ends *)
Definition LO_RC1RA : Z := 0x58.   (* 0x86588: after the first rec_clear *)
Definition LO_LH : Z := 0x124.     (* 0x86654: the top loop's head, its size test beqz s8 *)
Definition LO_SMRA : Z := 0x230.   (* 0x86760: after send_message *)
Definition LO_K : Z := 0x4d4.      (* 0x86a04: the words are built (every exit of the split loop); the five checks *)
Definition LO_RTRA : Z := 0x50c.   (* 0x86a3c: after check_round_trip; the three frees and the latch *)
Definition LO_RC2RA : Z := 0x5c4.  (* 0x86af4: after the second rec_clear *)

(* The message the top loop carves from the r bytes left of the payload (lib/Prog/SlotSpec.v:28-34), and what the
   walk's event count ev_msgs (LLVMFuzzerTestOneInput_c.v) charges for the rest. *)
Definition lt_rest (pl : list byte) (n r : Z) : list byte := skipn (Z.to_nat (n - r)) pl.
Definition lt_hdr (pl : list byte) (n r : Z) : list byte := firstn (Z.to_nat (SlotSpec.hdr_n r)) (lt_rest pl n r).
Definition lt_len (pl : list byte) (n r : Z) : Z := SlotSpec.msg_len r (lt_hdr pl n r).
Definition lt_D (pl : list byte) (n r : Z) : list byte :=
  firstn (Z.to_nat (lt_len pl n r)) (skipn (Z.to_nat (SlotSpec.hdr_n r)) (lt_rest pl n r)).
Definition lt_R0 (pl : list byte) (n r : Z) (Rh : rstate) : rstate :=
  rec_set_rc Rh (SlotSpec.msg_rf (lt_hdr pl n r)) (SlotSpec.msg_cd (lt_hdr pl n r)).
Definition lt_ws (pl : list byte) (n r : Z) : list (list byte) := HarnessProps.hwords (lt_D pl n r).
(* the bytes left after the message *)
Definition lt_r' (pl : list byte) (n r : Z) : Z := r - SlotSpec.hdr_n r - lt_len pl n r.
(* one message's events, as ev_msgs sums them *)
Definition lt_cost (R0 : rstate) (D : list byte) (R1 : rstate) (ws : list (list byte)) : Z :=
  EV_SEND_MESSAGE R0 D + (3 + 3) + EV_CHECK_REPLY + EV_CHECK_ARITY + EV_CHECK_WORDS + EV_CHECK_REFUSAL +
  EV_CHECK_ROUND_TRIP R1 ws.
(* the events from a loop head with f passes left, recorder R and payload rest l, to the return: the passes and the
   final rec_clear *)
Definition ev_from (f : nat) (R : rstate) (l : list byte) : Z :=
  fst (ev_msgs f R l) + EV_REC_CLEAR (snd (ev_msgs f R l)).
(* the part of a recorder state ev_msgs reads (through rec_set_rc and rec_clear: the calls, the spill, the state and
   the host settings) *)
Definition rkey (R : rstate) : list rcall * rcall * Z * Z := (r_calls R, r_spill R, r_state R, r_host R).
Lemma rkey_rec_clear_set : forall R R' rf cd, rkey R = rkey R' ->
  RecModel.rec_clear (rec_set_rc R rf cd) = RecModel.rec_clear (rec_set_rc R' rf cd).
Proof. intros [] [] rf cd H. unfold rkey in H. cbn in H. inversion H. reflexivity. Qed.
Lemma rkey_ev_rec_clear : forall R R', rkey R = rkey R' -> EV_REC_CLEAR R = EV_REC_CLEAR R'.
Proof. intros [] [] H. unfold rkey in H. cbn in H. inversion H. reflexivity. Qed.
Lemma rkey_ev_send : forall R R' rf cd D, rkey R = rkey R' ->
  EV_SEND_MESSAGE (rec_set_rc R rf cd) D = EV_SEND_MESSAGE (rec_set_rc R' rf cd) D.
Proof.
intros R R' rf cd D H. unfold EV_SEND_MESSAGE. rewrite (rkey_rec_clear_set R R' rf cd H).
rewrite (rkey_ev_rec_clear (rec_set_rc R rf cd) (rec_set_rc R' rf cd)); [reflexivity|].
destruct R, R'. unfold rkey in *. cbn in *. inversion H. reflexivity.
Qed.
(* the events left depend on the recorder only through rkey *)
Lemma ev_msgs_rkey : forall f R R' l, rkey R = rkey R' ->
  fst (ev_msgs f R l) = fst (ev_msgs f R' l) /\ rkey (snd (ev_msgs f R l)) = rkey (snd (ev_msgs f R' l)).
Proof.
induction f as [|f IH]; intros R R' l H; [cbn; auto|].
destruct l as [|b l]; [cbn; auto|].
cbn [ev_msgs]. rewrite !(rkey_rec_clear_set R R' _ _ H). rewrite !(rkey_ev_send R R' _ _ _ H).
match goal with |- context [ev_msgs f ?R1 ?l1] => destruct (ev_msgs f R1 l1) as [k Rf] end.
cbn. auto.
Qed.
Lemma ev_from_rkey : forall f R R' l, rkey R = rkey R' -> ev_from f R l = ev_from f R' l.
Proof.
intros f R R' l H. unfold ev_from. destruct (ev_msgs_rkey f R R' l H) as [H1 H2]. rewrite H1.
rewrite (rkey_ev_rec_clear _ _ H2). reflexivity.
Qed.
Lemma ev_from_nil : forall f R, ev_from f R [] = EV_REC_CLEAR R.
Proof. intros [|f] R; reflexivity. Qed.
Lemma ev_from_O : forall R l, ev_from O R l = EV_REC_CLEAR R.
Proof. reflexivity. Qed.
(* no byte is left once r = 0: the head's exit to the second rec_clear *)
Lemma lt_rest_0 : forall pl n, n = Z.of_nat (length pl) -> lt_rest pl n 0 = [].
Proof. intros pl n Hn. unfold lt_rest. apply skipn_all2. lia. Qed.
Lemma lt_len_range : forall pl n r, 0 < r -> 0 <= lt_len pl n r <= r - SlotSpec.hdr_n r.
Proof.
intros pl n r Hr. unfold lt_len, SlotSpec.msg_len, SlotSpec.hbyte, SlotSpec.hdr_n.
pose proof (bv_unsigned_in_range 8 (nth 1 (lt_hdr pl n r) (Z_to_bv 8 0))) as B1.
pose proof (bv_unsigned_in_range 8 (nth 2 (lt_hdr pl n r) (Z_to_bv 8 0))) as B2.
change (bv_modulus 8) with 256 in B1, B2. lia.
Qed.
(* one pass of the top loop, in the walk's carving *)
Lemma ev_from_S : forall f R pl n r,
  n = Z.of_nat (length pl) -> 0 < r <= n ->
  ev_from (Datatypes.S f) R (lt_rest pl n r) =
  lt_cost (lt_R0 pl n r R) (lt_D pl n r) (fst (fst (vr_runA (RecModel.rec_clear (lt_R0 pl n r R)) (lt_D pl n r))))
    (lt_ws pl n r) +
  ev_from f (fst (fst (vr_runA (RecModel.rec_clear (lt_R0 pl n r R)) (lt_D pl n r)))) (lt_rest pl n (lt_r' pl n r)).
Proof.
intros f R pl n r Hn Hr.
pose proof (lt_len_range pl n r ltac:(lia)) as HL.
assert (Hh : 0 < SlotSpec.hdr_n r <= r) by (unfold SlotSpec.hdr_n; lia).
assert (Hsk : skipn (Z.to_nat (SlotSpec.hdr_n r) + Z.to_nat (lt_len pl n r)) (lt_rest pl n r) =
  lt_rest pl n (lt_r' pl n r)).
{ unfold lt_rest, lt_r'. rewrite skipn_skipn. f_equal. lia. }
assert (Hlen : Z.of_nat (length (lt_rest pl n r)) = r) by (unfold lt_rest; rewrite length_skipn; lia).
rewrite <- Hsk. unfold lt_cost, lt_ws, lt_R0, lt_D, lt_len, lt_hdr. unfold lt_len, lt_hdr in Hsk.
remember (lt_rest pl n r) as l0 eqn:El. clear El Hsk.
destruct l0 as [|b l]; [cbn in Hlen; lia|].
unfold ev_from. cbn [ev_msgs]. rewrite !Hlen.
match goal with |- context [ev_msgs f ?R1 ?l1] => destruct (ev_msgs f R1 l1) as [k Rf] end.
cbn [fst snd]. unfold HarnessProps.hwords. ring.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* The entry's context: the state at BASE + 0 and the driver's arguments (cgif A/ACf5.v rtcx). *)
Record lcx := mkLCX {
  x_ly : alayout; x_S : astate; x_W : world SEGS; x_regs : bvmap 5 word; x_mem : word -> option byte; x_md : Model;
  x_ch : list (Z * Z * Z); x_p : Z; x_n : Z; x_pl : list byte; x_j : nat }.
Definition x_sp0 (cx : lcx) : Z := spZ (x_regs cx).
Definition x_sp1 (cx : lcx) : Z := spZ (x_regs cx) - LT_FRAME.
Definition x_bl0 (B : asyms) (cx : lcx) : list (Z * Z) := ablocks B (x_ly cx) (x_S cx).
Definition x_rest (cx : lcx) (r : Z) : list byte := lt_rest (x_pl cx) (x_n cx) r.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.

(* what the walk uses of tLLVMFuzzerTestOneInput_spec's premises, word for word but the rounding mode (every segment
   statement's own premise; statement pass 5 has no astack_pres: the chains at the program calls come from afn_pre,
   s0 = -1 at every call of the loop, the entry's chain at the first rec_clear); the per-binary facts
   (flag byte, errno cell, stack guard, zero shadow of the image objects) are the walk's Section hypotheses
   (RULING-STMT.md §2), not premises here *)
Definition lt_base (cx : lcx) : Prop :=
  let ly := x_ly cx in let S := x_S cx in let W := x_W cx in let regs := x_regs cx in let mem := x_mem cx in
  let md := x_md cx in let p := x_p cx in let n := x_n cx in let pl := x_pl cx in
  afn_pre SEGS B LTOI_STK ly S W regs mem md (x_ch cx) /\
  arodata_okP SEGS RLO RHI B (rdW W mem) /\
  cmd_ro_ok (rdW W mem) /\ cmd_val_objs /\
  getr regs 10 = w64 p /\ getr regs 11 = w64 n /\
  ((n = 0 /\ p = A_EMPTY) \/ (0 < n < 2 ^ 26 /\ In (p, n) (ablocks B ly S))) /\
  n = Z.of_nat (length pl) /\ garr8 SEGS (mrestrict (w_H W) mem) p (map (fun b : byte => bv_unsigned b) pl) /\
  frames S = [] /\
  GI_cmdA (x_j cx) (rdW W mem) /\
  st_nev S + EV_LTOI pl <= EV_MAX /\ blocks_bytes S + LIVE_LTOI <= LIVE_MAX /\
  mo_ok MT S (XM_LTOI MT pl).

(* a pass with bytes left reads a payload of 1 .. 2^26 - 1 bytes in its live block *)
Lemma lt_payload_live : forall cx r, lt_base cx -> 0 < r <= x_n cx ->
  0 < x_n cx < 2 ^ 26 /\ In (x_p cx, x_n cx) (ablocks B (x_ly cx) (x_S cx)).
Proof.
intros cx r HB Hr. destruct HB as (_ & _ & _ & _ & _ & _ & Hpn & _).
destruct Hpn as [[Hn _] | H]; [lia | exact H].
Qed.

(* the post-condition's own part, word for word the statement's *)
Definition lt_Q (cx : lcx) : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' W' regs' mem' md' =>
  getr regs' 10 = w64 0 /\
  Permutation (ablocks B ly' S') (ablocks B (x_ly cx) (x_S cx)) /\
  (forall i, 0 <= i < x_n cx -> rdW W' mem' (x_p cx + i) = rdW (x_W cx) (x_mem cx) (x_p cx + i)) /\
  (exists R : rstate,
     cmd_rec_invA B ly' S' (rdW W' mem') (ablocks B (x_ly cx) (x_S cx)) (RecModel.rec_clear R) [] 0) /\
  GI_cmdA (Datatypes.S (x_j cx)) (rdW W' mem') /\
  mo_le MT (x_S cx) S' (XM_LTOI MT (x_pl cx)) /\ blocks_bytes S' <= blocks_bytes (x_S cx) + LIVE_LTOI.
Definition lt_post (cx : lcx) : world SEGS -> config -> Prop :=
  apost_baseF SEGS B LTOI_STK cmd_PG (x_regs cx) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx)
    (EV_LTOI (x_pl cx)) (lt_Q cx).

(* the registers the entry saved, in its frame *)
Definition lt_saved (cx : lcx) (rd : reader) : Prop :=
  forall i r, nth_error LT_SAVED i = Some r ->
  rdword rd (x_sp0 cx - 8 * Z.of_nat (Datatypes.S i)) = Some (bv_unsigned (getr (x_regs cx) r)).
(* the part of every point inside the frame: the journal from the entry (footprint cmd_PG, no side-stack frame),
   the frame's sp, gp and tp kept, the saved registers *)
Definition lt_frame (cx : lcx) ly S (W : world SEGS) (regs : bvmap 5 word) mem md (k : Z) : Prop :=
  ajournal SEGS B LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [] ly S W mem md k /\
  spZ regs = x_sp1 cx /\ getr regs 3 = getr (x_regs cx) 3 /\ getr regs 4 = getr (x_regs cx) 4 /\
  lt_saved cx (rdW W mem).
(* the ten words below the struct, as the entry left them *)
Definition lt_slots (cx : lcx) (rd : reader) : Prop :=
  forall o v, In (o, v) LT_SLOTS -> rdword rd (x_sp1 cx + o) = Some v.
(* the meter and the events left: k spent, rem still to come, acc metered; every event is charged at most
   LT_U MT, the cost of the largest allocation of the program and a free (XM_LTOI's unit) *)
Definition LT_U : Z := mo_malloc MT 32784 + mo_free MT.
Definition lt_bud (cx : lcx) (S : astate) (k acc rem : Z) : Prop :=
  0 <= k /\ 0 <= rem /\ k + rem <= EV_LTOI (x_pl cx) /\
  mo_le MT (x_S cx) S acc /\ 0 <= acc /\ acc + rem * LT_U <= XM_LTOI MT (x_pl cx).
(* the live bytes: blocks_bytes is the sum of the live blocks' sizes, so a Permutation of the blocks gives it at
   every point (the recorder's part is at most LT_RECB, the words blocks' at most LT_WORDSB) *)
Fixpoint bsum (bl : list (Z * Z)) : Z := match bl with [] => 0 | b :: l => snd b + bsum l end.
Lemma bsum_app : forall l1 l2, bsum (l1 ++ l2) = bsum l1 + bsum l2.
Proof. induction l1 as [|b l1 IH]; intros l2; cbn [app bsum]; [reflexivity | rewrite IH; ring]. Qed.
Lemma bsum_perm : forall l1 l2, Permutation l1 l2 -> bsum l1 = bsum l2.
Proof. intros l1 l2 H. induction H; cbn [bsum]; [reflexivity | rewrite IHPermutation; reflexivity | ring | congruence]. Qed.
Lemma blocks_bytes_ablocks : forall ly S, blocks_bytes S = bsum (ablocks B ly S).
Proof.
intros ly S. unfold blocks_bytes, ablocks, blocks. induction (st_chunks S) as [|c cs IH]; [reflexivity|].
cbn [fold_right List.filter]. destruct (is_alloc c); cbn [map bsum snd fst]; [rewrite IH; reflexivity | exact IH].
Qed.
(* the recorder's blocks between messages: 2 calls of 6 arguments, the answer and the reply (RecInv.v's bound) *)
Definition LT_RECB : Z := 14 * (LMAX + 2).
(* the three words blocks of one message: text, copy, the pointer array (8193 + 8193 + 32,784) *)
Definition LT_WORDSB : Z := 8193 + 8193 + 32784.

(* every point of the top loop's body: the frame, the ten words, s0 = -1 (0x865f0), s1 = the pass m (0x865cc,
   the latch 0x86a54), s2 = the mask, s9 = the shadow base, s10 = &g_rec, s11 = 32, m < 32 *)
Definition lt_body (cx : lcx) ly S (W : world SEGS) (regs : bvmap 5 word) mem md (k : Z) (m : nat) : Prop :=
  lt_frame cx ly S W regs mem md k /\ lt_slots cx (rdW W mem) /\
  getr regs 8 = w64 (-1) /\ getr regs 9 = w64 (Z.of_nat m) /\ getr regs 18 = w64 LT_MASK /\
  getr regs 25 = w64 LT_SB /\ getr regs 26 = w64 A_G_REC /\ getr regs 27 = w64 32 /\
  (m < 32)%nat.
(* the message of a pass with r > 0 bytes left: s3 = its first byte, s4 = its length, s5 = g_rec.state and the
   frame word at sp + 112 = g_rec.host_settings as they were at the head (0x866e4, 0x8673c), s6 = the bytes left
   after the header *)
Definition lt_msg_regs (cx : lcx) (regs : bvmap 5 word) (rd : reader) (r : Z) (Rh : rstate) : Prop :=
  0 < r <= x_n cx /\
  getr regs 19 = w64 (x_p cx + (x_n cx - r) + SlotSpec.hdr_n r) /\
  getr regs 20 = w64 (lt_len (x_pl cx) (x_n cx) r) /\
  getr regs 21 = w64 (r_state Rh) /\ getr regs 22 = w64 (r - SlotSpec.hdr_n r) /\
  0 <= r_state Rh < 2 ^ 64 /\ 0 <= r_host Rh < 2 ^ 64 /\
  rdword rd (x_sp1 cx + LT_HOSTB) = Some (r_host Rh).
(* the recorder between two passes (cmd_rec_invA of the statement, and the reply/refusal facts the next send and
   the checks need) *)
Definition lt_rec (cx : lcx) ly S (W : world SEGS) mem (R : rstate) (O : list (Z * Z)) (q : Z) (extra : list (Z * Z)) :
  Prop :=
  rec_repA B ly S (rdW W mem) R O /\ r_spill R = (0, []) /\ (length (r_calls R) <= 2)%nat /\
  aval_mem (rdW W mem) A_G_QUITTING 4 q /\ 0 <= q < 2 ^ 32 /\
  Permutation (ablocks B ly S) (O ++ x_bl0 B cx ++ extra).

(* ---- the segment statements: from a point to the return, under the entry's context ---- *)

(* 0x86530: the function *)
Definition LT_ENTRY_stmt : Prop :=
  forall cx, lt_base cx -> Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
  SRr SEGS (x_W cx) (cfg_at SEGS (BASE + AF_LLVMFuzzerTestOneInput) (x_regs cx) (x_mem cx) (x_md cx)) (lt_post cx).

(* the entry of the first rec_clear (jal at 0x86584): s7 = p, s8 = n, s9 = the shadow base, s0 the caller's (the
   entry's chain), the recorder as GI_cmdA leaves it (no call, no answer, no reply, the spill empty) *)
Definition LT_RC1_stmt : Prop :=
  forall cx ly S W regs mem md (R : rstate),
  lt_base cx -> Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 -> lt_frame cx ly S W regs mem md 0 ->
  getr regs 1 = w64 (BASE + LO_RC1RA) ->
  getr regs 25 = w64 LT_SB -> getr regs 23 = w64 (x_p cx) -> getr regs 24 = w64 (x_n cx) ->
  getr regs 8 = getr (x_regs cx) 8 ->
  lt_rec cx ly S W mem R [] 0 [] -> r_calls R = [] -> r_answer R = None -> r_reply R = None -> r_nreplies R = 0 ->
  lt_bud cx S 0 0 (EV_LTOI (x_pl cx)) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_rec_clear)) mem (seg_rom SEGS)) md) (lt_post cx).

(* 0x86588: after the first rec_clear; the recorder is rec_clear of the entry's, with no block, g_quitting = 0;
   next the two inline zero stores, the frame words and the fall into the loop's head with m = 0, r = n *)
Definition LT_A_stmt : Prop :=
  forall cx ly S W regs mem md k acc (R : rstate),
  lt_base cx -> Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 -> lt_frame cx ly S W regs mem md k ->
  getr regs 25 = w64 LT_SB -> getr regs 23 = w64 (x_p cx) -> getr regs 24 = w64 (x_n cx) ->
  lt_rec cx ly S W mem R [] 0 [] -> r_calls R = [] -> r_answer R = None -> r_reply R = None -> r_nreplies R = 0 ->
  lt_bud cx S k acc (ev_from 32 R_ENTRY (x_pl cx)) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + LO_RC1RA)) mem (seg_rom SEGS)) md) (lt_post cx).

(* 0x86654: the head of pass m with r >= 0 bytes left (r = 0 leaves for the second rec_clear, beqz s8); s7 = the
   cursor, s8 = r, a5 = 1 (UBSan's p + 1 tests); the recorder R over blocks O *)
Definition LT_LH_stmt (m : nat) : Prop :=
  forall cx ly S W regs mem md k acc (r : Z) (R : rstate) (O : list (Z * Z)) (q : Z),
  lt_base cx -> Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 -> lt_body cx ly S W regs mem md k m ->
  0 <= r <= x_n cx ->
  getr regs 23 = w64 (x_p cx + (x_n cx - r)) -> getr regs 24 = w64 r -> getr regs 15 = w64 1 ->
  lt_rec cx ly S W mem R O q [] ->
  lt_bud cx S k acc (ev_from (32 - m) R (x_rest cx r)) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + LO_LH)) mem (seg_rom SEGS)) md) (lt_post cx).

(* the entry of send_message (jal at 0x8675c): a0 = the message, a1 = its length; g_rec.refuse and g_rec.code are
   set (rec_set_rc), the recorder's blocks are O *)
Definition LT_SM_stmt (m : nat) : Prop :=
  forall cx ly S W regs mem md k acc (r : Z) (Rh : rstate) (O : list (Z * Z)) (q : Z),
  lt_base cx -> Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 -> lt_body cx ly S W regs mem md k m ->
  lt_msg_regs cx regs (rdW W mem) r Rh ->
  getr regs 1 = w64 (BASE + LO_SMRA) ->
  getr regs 10 = w64 (x_p cx + (x_n cx - r) + SlotSpec.hdr_n r) -> getr regs 11 = w64 (lt_len (x_pl cx) (x_n cx) r) ->
  lt_rec cx ly S W mem (lt_R0 (x_pl cx) (x_n cx) r Rh) O q [] ->
  let R0 := lt_R0 (x_pl cx) (x_n cx) r Rh in let D := lt_D (x_pl cx) (x_n cx) r in
  let R1 := fst (fst (vr_runA (RecModel.rec_clear R0) D)) in
  lt_bud cx S k acc (lt_cost R0 D R1 (lt_ws (x_pl cx) (x_n cx) r) +
    ev_from (31 - m) R1 (x_rest cx (lt_r' (x_pl cx) (x_n cx) r))) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_send_message)) mem (seg_rom SEGS)) md) (lt_post cx).

(* 0x86760: after send_message; the recorder is verbs_receive's run on the cleared R0 (send_message's post) *)
Definition LT_W_stmt (m : nat) : Prop :=
  forall cx ly S W regs mem md k acc (r : Z) (Rh : rstate) (O1 : list (Z * Z)),
  lt_base cx -> Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 -> lt_body cx ly S W regs mem md k m ->
  lt_msg_regs cx regs (rdW W mem) r Rh ->
  let R0 := lt_R0 (x_pl cx) (x_n cx) r Rh in let D := lt_D (x_pl cx) (x_n cx) r in
  let '(R1, _, quit) := vr_runA (RecModel.rec_clear R0) D in
  lt_rec cx ly S W mem R1 O1 (if quit then 1 else 0) [] ->
  lt_bud cx S k acc ((3 + 3) + EV_CHECK_REPLY + EV_CHECK_ARITY + EV_CHECK_WORDS + EV_CHECK_REFUSAL +
    EV_CHECK_ROUND_TRIP R1 (lt_ws (x_pl cx) (x_n cx) r) +
    ev_from (31 - m) R1 (x_rest cx (lt_r' (x_pl cx) (x_n cx) r))) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + LO_SMRA)) mem (seg_rom SEGS)) md) (lt_post cx).

(* the words of the message, as words_of leaves them (plain lib/Prog/SlotSpec.v run_words_spec's post): at sp + 120
   the struct (text, copy, the array, the count), the three blocks live, the array's first length ws slots holding
   pointers into copy, each the start of its word and its NUL; B keeps the three pointers in the frame only *)
Definition lt_words (cx : lcx) (rd : reader) (D : list byte) (ws : list (list byte))
  (text copy arr : Z) (wp : list Z) : Prop :=
  let L0 := StrFun.strnlen_res (Z.of_nat (length D)) D in
  rdword rd (x_sp1 cx + LT_W) = Some text /\ rdword rd (x_sp1 cx + LT_W + 8) = Some copy /\
  rdword rd (x_sp1 cx + LT_W + 16) = Some arr /\ aval_mem rd (x_sp1 cx + LT_W + 24) 4 (Z.of_nat (length ws)) /\
  length wp = length ws /\
  (forall i pt, nth_error wp i = Some pt -> rdword rd (arr + 8 * Z.of_nat i) = Some pt) /\
  (forall i pt w, nth_error wp i = Some pt -> nth_error ws i = Some w ->
     copy <= pt /\ pt + Z.of_nat (length w) + 1 <= copy + L0 + 1 /\ astr_atR rd pt w).
Definition lt_wblocks (D : list byte) (text copy arr : Z) : list (Z * Z) :=
  let L0 := StrFun.strnlen_res (Z.of_nat (length D)) D in
  [(text, L0 + 1); (copy, L0 + 1); (arr, SlotSpec.arr_size L0)].

(* 0x86a04: the words are built; next s7 := the next cursor, s8 := the bytes left, and the five checks *)
Definition LT_K_stmt (m : nat) : Prop :=
  forall cx ly S W regs mem md k acc (r : Z) (Rh : rstate) (O1 : list (Z * Z)) text copy arr (wp : list Z),
  lt_base cx -> Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 -> lt_body cx ly S W regs mem md k m ->
  lt_msg_regs cx regs (rdW W mem) r Rh ->
  let R0 := lt_R0 (x_pl cx) (x_n cx) r Rh in let D := lt_D (x_pl cx) (x_n cx) r in
  let ws := lt_ws (x_pl cx) (x_n cx) r in
  let '(R1, _, quit) := vr_runA (RecModel.rec_clear R0) D in
  lt_words cx (rdW W mem) D ws text copy arr wp ->
  lt_rec cx ly S W mem R1 O1 (if quit then 1 else 0) (lt_wblocks D text copy arr) ->
  lt_bud cx S k acc (3 + EV_CHECK_REPLY + EV_CHECK_ARITY + EV_CHECK_WORDS + EV_CHECK_REFUSAL +
    EV_CHECK_ROUND_TRIP R1 ws + ev_from (31 - m) R1 (x_rest cx (lt_r' (x_pl cx) (x_n cx) r))) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + LO_K)) mem (seg_rom SEGS)) md) (lt_post cx).

(* the entry of check_round_trip (jal at 0x86a38): a0 = &w, a1 = s5 = g_rec.state and a2 = g_rec.host_settings
   (sp + 112) as they were before the send; s7 = the next cursor, s8 = the bytes left after the message *)
Definition LT_RT_stmt (m : nat) : Prop :=
  forall cx ly S W regs mem md k acc (r : Z) (Rh : rstate) (O1 : list (Z * Z)) text copy arr (wp : list Z),
  lt_base cx -> Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 -> lt_body cx ly S W regs mem md k m ->
  0 < r <= x_n cx ->
  getr regs 23 = w64 (x_p cx + (x_n cx - lt_r' (x_pl cx) (x_n cx) r)) ->
  getr regs 24 = w64 (lt_r' (x_pl cx) (x_n cx) r) ->
  getr regs 1 = w64 (BASE + LO_RTRA) ->
  getr regs 10 = w64 (x_sp1 cx + LT_W) -> getr regs 11 = w64 (r_state Rh) -> getr regs 12 = w64 (r_host Rh) ->
  0 <= r_state Rh < 2 ^ 64 -> 0 <= r_host Rh < 2 ^ 64 ->
  let R0 := lt_R0 (x_pl cx) (x_n cx) r Rh in let D := lt_D (x_pl cx) (x_n cx) r in
  let ws := lt_ws (x_pl cx) (x_n cx) r in
  let '(R1, _, quit) := vr_runA (RecModel.rec_clear R0) D in
  lt_words cx (rdW W mem) D ws text copy arr wp ->
  lt_rec cx ly S W mem R1 O1 (if quit then 1 else 0) (lt_wblocks D text copy arr) ->
  lt_bud cx S k acc (3 + EV_CHECK_ROUND_TRIP R1 ws + ev_from (31 - m) R1 (x_rest cx (lt_r' (x_pl cx) (x_n cx) r))) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_check_round_trip)) mem (seg_rom SEGS)) md) (lt_post cx).

(* 0x86a3c: after check_round_trip; the recorder R2 has R1's calls, spill, state and host (its post), so the events
   left are the same; next the three frees of the struct's blocks (reloaded from sp + 120 .. 136) and the latch
   (s1 + 1 <> 32 to the head, else to the second rec_clear) *)
Definition LT_F_stmt (m : nat) : Prop :=
  forall cx ly S W regs mem md k acc (r : Z) (R2 : rstate) (O2 : list (Z * Z)) (q2 : Z) text copy arr,
  lt_base cx -> Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 -> lt_body cx ly S W regs mem md k m ->
  0 < r <= x_n cx ->
  getr regs 23 = w64 (x_p cx + (x_n cx - lt_r' (x_pl cx) (x_n cx) r)) ->
  getr regs 24 = w64 (lt_r' (x_pl cx) (x_n cx) r) ->
  rdword (rdW W mem) (x_sp1 cx + LT_W) = Some text -> rdword (rdW W mem) (x_sp1 cx + LT_W + 8) = Some copy ->
  rdword (rdW W mem) (x_sp1 cx + LT_W + 16) = Some arr ->
  let D := lt_D (x_pl cx) (x_n cx) r in
  lt_rec cx ly S W mem R2 O2 q2 (lt_wblocks D text copy arr) ->
  lt_bud cx S k acc (3 + ev_from (31 - m) R2 (x_rest cx (lt_r' (x_pl cx) (x_n cx) r))) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + LO_RTRA)) mem (seg_rom SEGS)) md) (lt_post cx).

(* the entry of the second rec_clear (jal at 0x86af0), from the head with no byte left or after pass 31; s0 = -1
   (achain's empty case) *)
Definition LT_Z_stmt : Prop :=
  forall cx ly S W regs mem md k acc (R : rstate) (O : list (Z * Z)) (q : Z),
  lt_base cx -> Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 -> lt_frame cx ly S W regs mem md k ->
  getr regs 1 = w64 (BASE + LO_RC2RA) -> getr regs 25 = w64 LT_SB -> getr regs 8 = w64 (-1) ->
  lt_rec cx ly S W mem R O q [] ->
  lt_bud cx S k acc (EV_REC_CLEAR R) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_rec_clear)) mem (seg_rom SEGS)) md) (lt_post cx).

(* 0x86af4: after the second rec_clear; the recorder is rec_clear R and owns no block *)
Definition LT_Z2_stmt : Prop :=
  forall cx ly S W regs mem md k acc (R : rstate) (q : Z),
  lt_base cx -> Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 -> lt_frame cx ly S W regs mem md k ->
  getr regs 25 = w64 LT_SB ->
  lt_rec cx ly S W mem (RecModel.rec_clear R) [] q [] ->
  lt_bud cx S k acc 0 ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + LO_RC2RA)) mem (seg_rom SEGS)) md) (lt_post cx).

End e.
End f.
End d.

(* the segment statements at every FP state: a segment lemma takes its continuations in this form and concludes its
   own statement at the FP state of its start (statement pass 4: send_message, check_reply, check_words and
   check_round_trip return at an FP state of their own, apost_baseF) *)
Section lta. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg cmd_listing}.
Definition LTA_ENTRY (B : asyms) (MT : ameter_ops) : Prop := forall fx1 : YK11.FPState, LT_ENTRY_stmt (fx := fx1) B MT.
Definition LTA_RC1 (B : asyms) (MT : ameter_ops) : Prop := forall fx1 : YK11.FPState, LT_RC1_stmt (fx := fx1) B MT.
Definition LTA_A (B : asyms) (MT : ameter_ops) : Prop := forall fx1 : YK11.FPState, LT_A_stmt (fx := fx1) B MT.
Definition LTA_LH (B : asyms) (MT : ameter_ops) (m : nat) : Prop := forall fx1 : YK11.FPState, LT_LH_stmt (fx := fx1) B MT m.
Definition LTA_SM (B : asyms) (MT : ameter_ops) (m : nat) : Prop := forall fx1 : YK11.FPState, LT_SM_stmt (fx := fx1) B MT m.
Definition LTA_W (B : asyms) (MT : ameter_ops) (m : nat) : Prop := forall fx1 : YK11.FPState, LT_W_stmt (fx := fx1) B MT m.
Definition LTA_K (B : asyms) (MT : ameter_ops) (m : nat) : Prop := forall fx1 : YK11.FPState, LT_K_stmt (fx := fx1) B MT m.
Definition LTA_RT (B : asyms) (MT : ameter_ops) (m : nat) : Prop := forall fx1 : YK11.FPState, LT_RT_stmt (fx := fx1) B MT m.
Definition LTA_F (B : asyms) (MT : ameter_ops) (m : nat) : Prop := forall fx1 : YK11.FPState, LT_F_stmt (fx := fx1) B MT m.
Definition LTA_Z (B : asyms) (MT : ameter_ops) : Prop := forall fx1 : YK11.FPState, LT_Z_stmt (fx := fx1) B MT.
Definition LTA_Z2 (B : asyms) (MT : ameter_ops) : Prop := forall fx1 : YK11.FPState, LT_Z2_stmt (fx := fx1) B MT.
End lta.
