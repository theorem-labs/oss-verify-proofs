(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the boundary states of the inlined words_of of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86760 .. 0x86a04), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_s40.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (the CL_*_stmtX segment statements and the seed lemma cl_seedX) over the model of fuzz_command's released plain proof (lib/Prog/SlotWords.v, SlotWordsRun.v: tz, sw_found, sw_round). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaArt PaSB CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
rec_clear_c send_message_c check_reply_c check_arity_c check_words_c check_refusal_c check_round_trip_c
verbs_receive_c LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_defs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require SlotSpec HarnessProps SlotWords SlotWordsRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require strspn_c strcspn_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs StrFun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Local Open Scope Z_scope.

(* ---- the points of the listing this segment runs between (offsets from BASE = 0x86530) ---- *)
(* 0x86760, after send_message: LO_SMRA of the defs, where LT_W_stmt starts. Next: the strnlen wrapper on the
   message (a0 = s3, a1 = s4), s7 := L0, s8 := L0 + 1, the three wrapper mallocs (L0 + 1, L0 + 1,
   ((L0 << 2) & -8) + 16), their results stored at 120/128/136(sp), the three NULL tests reloaded from the frame *)
Definition AW_M : Z := 0x284.   (* 0x867b4: the three blocks are made and tested; next a0 := text (a1), a1 := s3,
                                    a2 := s7 = L0, jal __asan_memcpy, then the UBSan checks of text + L0 and its NUL *)
Definition AW_T : Z := 0x2d0.   (* 0x86800: the trim loop's head, ld a1,120(sp); s7 = the index of the byte to test *)
Definition AW_J : Z := 0x38c.   (* 0x868bc: the line is trimmed, a2 = its length + 1; next __asan_memcpy into copy,
                                    s7 := copy (128(sp)), w.n := 0 (144(sp)), the UBSan and load checks of copy *)
Definition AW_S : Z := 0x3b4.   (* 0x868e4: the split loop's head, lbu a0,0(s7) (the *t test, 0 -> LO_K) *)
Definition AW_S2 : Z := 0x45c.  (* 0x8698c: inside the split loop, the strcspn wrapper has returned *)
(* 0x86a04 = LO_K of the defs: every exit of the split loop lands there; AW_E_stmt is LT_K_stmt in this file's
   words (the words' facts in the form the loop carries them) *)

(* the byte values the trim loop treats as trailing, as the mask register s2 holds them *)
Definition aw_trail (z : Z) : bool := SlotWords.sw_trail_z z.
(* the separator set " \t" of the split loop, and the two wrappers' answers on it (the plain model's) *)
Module AwSpn := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.strspn_c.
Module AwCspn := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.strcspn_c.
Definition aw_spn (l : list byte) : nat := AwSpn.spn_len SlotWords.SEPS l.
Definition aw_cspn (l : list byte) : nat := AwCspn.cspn_len SlotWords.SEPS l.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Section e.
Variable B : asyms.
Variable MT : ameter_ops.

(* ---- the message of one pass of the top loop, and the model of its words ---- *)
Record awm : Type := mkAWM {
  q_m : nat;                 (* the pass *)
  q_r : Z;                   (* the payload bytes left when the pass began *)
  q_Rh : rstate;             (* the recorder at the head of the pass *)
  q_O1 : list (Z * Z) }.     (* the recorder's blocks after the send *)
Definition q_D (cx : lcx) (q : awm) : list byte := lt_D (x_pl cx) (x_n cx) (q_r q).
Definition q_R0 (cx : lcx) (q : awm) : rstate := lt_R0 (x_pl cx) (x_n cx) (q_r q) (q_Rh q).
Definition q_run (cx : lcx) (q : awm) := vr_runA (RecModel.rec_clear (q_R0 cx q)) (q_D cx q).
Definition q_R1 (cx : lcx) (q : awm) : rstate := fst (fst (q_run cx q)).
Definition q_quit (cx : lcx) (q : awm) : bool := snd (q_run cx q).
Definition q_ws (cx : lcx) (q : awm) : list (list byte) := lt_ws (x_pl cx) (x_n cx) (q_r q).
(* strnlen(msg, len): the message up to its first NUL, as the plain model reads it; L0 is its length, in the form
   lt_wblocks of the defs states it (q_L0_U: the two are the same number) *)
Definition q_U (cx : lcx) (q : awm) : list byte := Verbs.upto0 (q_D cx q).
Definition q_LN (cx : lcx) (q : awm) : list byte := Verbs.line (q_D cx q).
Definition q_L0 (cx : lcx) (q : awm) : Z := StrFun.strnlen_res (Z.of_nat (length (q_D cx q))) (q_D cx q).
Lemma q_L0_U : forall cx q, q_L0 cx q = Z.of_nat (length (q_U cx q)).
Proof. intros cx q. exact (SlotWords.sw_strnlen_upto0 (q_D cx q)). Qed.
(* the message's first byte in the payload block (s3, lt_msg_regs) *)
Definition q_src (cx : lcx) (q : awm) : Z := x_p cx + (x_n cx - q_r q) + SlotSpec.hdr_n (q_r q).
(* the events still to come once the three blocks are made: the three frees, the five checks, the rest of the
   top loop and the last rec_clear. It is LT_K_stmt's `rem`, and LT_W_stmt's is this plus the three mallocs. *)
Definition aw_rem (cx : lcx) (q : awm) : Z :=
  3 + EV_CHECK_REPLY + EV_CHECK_ARITY + EV_CHECK_WORDS + EV_CHECK_REFUSAL +
  EV_CHECK_ROUND_TRIP (q_R1 cx q) (q_ws cx q) +
  ev_from (31 - q_m q) (q_R1 cx q) (x_rest cx (lt_r' (x_pl cx) (x_n cx) (q_r q))).

(* ---- what holds at every point of this segment ---- *)
(* the part that names neither a register the inlined words_of writes nor the budget: B's words_of writes only
   a0 .. a5, s7, s8 and the frame words 120 .. 147, so the loop body's registers (lt_body: s0 = -1, s1 = m,
   s2 = the mask, s9 = SB, s10 = &g_rec, s11 = 32) and the message's (lt_msg_regs: s3 .. s6, the host word at
   112(sp)) hold at every point, word for word the statements' *)
Definition aw_ctx0 (cx : lcx) (q : awm) ly S (W : world SEGS) (regs : bvmap 5 word) mem md (k : Z) : Prop :=
  lt_base B MT cx /\ lt_body B cx ly S W regs mem md k (q_m q) /\
  lt_msg_regs cx regs (rdW W mem) (q_r q) (q_Rh q).
(* with the budget once the three blocks are made (every point after the third malloc) *)
Definition aw_ctx (cx : lcx) (q : awm) ly S (W : world SEGS) (regs : bvmap 5 word) mem md (k acc : Z) : Prop :=
  aw_ctx0 cx q ly S W regs mem md k /\ lt_bud MT cx S k acc (aw_rem cx q).
(* the recorder after the send, with the blocks `extra` above the entry's and the recorder's own *)
Definition aw_rec (cx : lcx) (q : awm) ly S (W : world SEGS) mem (extra : list (Z * Z)) : Prop :=
  lt_rec B cx ly S W mem (q_R1 cx q) (q_O1 q) (if q_quit cx q then 1 else 0) extra.
(* the three blocks of one message, in the order the three mallocs make them: the defs' lt_wblocks, so the
   recorder premise below is LT_K_stmt's word for word *)
Definition aw_blocks (cx : lcx) (q : awm) (text copy arr : Z) : list (Z * Z) := lt_wblocks (q_D cx q) text copy arr.
Lemma aw_blocks_eq : forall cx q text copy arr,
  aw_blocks cx q text copy arr = [(text, q_L0 cx q + 1); (copy, q_L0 cx q + 1); (arr, SlotSpec.arr_size (q_L0 cx q))].
Proof. reflexivity. Qed.
(* the message's bytes, where the payload block holds them *)
Definition aw_msg (cx : lcx) (q : awm) (rd : reader) : Prop := abytes_atR rd (q_src cx q) (q_D cx q).

(* the three words of the struct the three mallocs stored (B keeps text, copy and the array only there) *)
Definition aw_wslots (cx : lcx) (rd : reader) (text copy arr : Z) : Prop :=
  rdword rd (x_sp1 cx + LT_W) = Some text /\ rdword rd (x_sp1 cx + LT_W + 8) = Some copy /\
  rdword rd (x_sp1 cx + LT_W + 16) = Some arr.
(* w.n, the struct's fourth word (4 bytes at 144(sp)): the number of words found so far *)
Definition aw_wn (cx : lcx) (rd : reader) (n : Z) : Prop := aval_mem rd (x_sp1 cx + LT_W + 24) 4 n.

(* ---- the segment statements, each from a point of the listing to the function's post ---- *)

(* 0x867b4: the three blocks are live, stored at 120/128/136(sp) and tested; a1 = text (reloaded at 0x8679c),
   s7 = L0; the message is still only in the payload block. *)
Definition AW_M_stmt (m : nat) : Prop :=
  forall cx q ly S W regs mem md k acc text copy arr,
  q_m q = m ->
  Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
  aw_ctx cx q ly S W regs mem md k acc ->
  aw_rec cx q ly S W mem (aw_blocks cx q text copy arr) ->
  aw_msg cx q (rdW W mem) -> aw_wslots cx (rdW W mem) text copy arr ->
  getr regs 11 = w64 text -> getr regs 23 = w64 (q_L0 cx q) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + AW_M)) mem (seg_rom SEGS)) md) (lt_post B MT cx).

(* 0x86800: the trim loop's head, with j bytes of the line left to test (1 <= j <= L0). text holds the first j
   bytes of strnlen's prefix and zeros after them (SlotWordsRun's tz), and trimming the whole prefix is the same as
   trimming its first j bytes. s7 = j - 1, the index of the byte the round tests (text + s7 is rebuilt from
   120(sp)). *)
Definition AW_T_stmt (m : nat) (j : nat) : Prop :=
  forall cx q ly S W regs mem md k acc text copy arr,
  q_m q = m ->
  Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
  aw_ctx cx q ly S W regs mem md k acc ->
  aw_rec cx q ly S W mem (aw_blocks cx q text copy arr) ->
  aw_wslots cx (rdW W mem) text copy arr ->
  (1 <= j <= length (q_U cx q))%nat ->
  Verbs.trim (q_U cx q) = Verbs.trim (firstn j (q_U cx q)) ->
  abytes_atR (rdW W mem) text (SlotWordsRun.tz (q_U cx q) j) ->
  getr regs 23 = w64 (Z.of_nat j - 1) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + AW_T)) mem (seg_rom SEGS)) md) (lt_post B MT cx).

(* 0x868bc: the line is trimmed and NUL-terminated in text; a2 = its length + 1. *)
Definition AW_J_stmt (m : nat) : Prop :=
  forall cx q ly S W regs mem md k acc text copy arr,
  q_m q = m ->
  Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
  aw_ctx cx q ly S W regs mem md k acc ->
  aw_rec cx q ly S W mem (aw_blocks cx q text copy arr) ->
  aw_wslots cx (rdW W mem) text copy arr ->
  (exists T, abytes_atR (rdW W mem) text T /\ length T = Z.to_nat (q_L0 cx q + 1) /\
     firstn (length (q_LN cx q) + 1) T = q_LN cx q ++ [Z_to_bv 8 0]) ->
  getr regs 12 = w64 (Z.of_nat (length (q_LN cx q)) + 1) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + AW_J)) mem (seg_rom SEGS)) md) (lt_post B MT cx).

(* the copy buffer during the split loop: C holds the line and its NUL from the cursor on, the words found so
   far are at wp, and the pointer array holds them (the plain proof's sw_found, lib/Prog/SlotWords.v:457). *)
Definition aw_found (copy : Z) (ws : list (list byte)) (C : list byte) (wp : list Z) (i : nat) : Prop :=
  forall k' p w, nth_error wp k' = Some p -> nth_error ws k' = Some w ->
    copy <= p /\ p + Z.of_nat (length w) + 1 <= copy + Z.of_nat i /\
    (forall t, (t <= length w)%nat -> nth_error C (Z.to_nat (p - copy) + t) = nth_error (w ++ [Z_to_bv 8 0]) t).
(* the pointer array holds the k words found so far, one 8-byte pointer each *)
Definition aw_arr (rd : reader) (arr : Z) (wp : list Z) : Prop :=
  forall i p, nth_error wp i = Some p -> rdword rd (arr + 8 * Z.of_nat i) = Some p.

(* 0x868e4: the split loop's head, with the cursor t = s7 at byte i of the line and kw words found; w.n (144(sp))
   holds kw. The B loop keeps no register of its own but s7: the count is reloaded from 144(sp) and &w.v[n] is
   rebuilt from 136(sp) on every word. *)
Definition AW_S_stmt (m : nat) (nm : nat) : Prop :=
  forall cx q ly S W regs mem md k acc text copy arr (i kw : nat) (C : list byte) (wp : list Z),
  q_m q = m ->
  Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
  aw_ctx cx q ly S W regs mem md k acc ->
  aw_rec cx q ly S W mem (aw_blocks cx q text copy arr) ->
  aw_wslots cx (rdW W mem) text copy arr ->
  getr regs 23 = w64 (copy + Z.of_nat i) ->
  aw_wn cx (rdW W mem) (Z.of_nat kw) ->
  (* the invariant of the loop (the plain proof's sw_loop, lib/Prog/SlotWords.v:559) *)
  nm = (length (q_LN cx q) - i)%nat -> (i <= length (q_LN cx q))%nat -> (2 * kw <= i)%nat ->
  length wp = kw -> (kw <= length (q_ws cx q))%nat ->
  Verbs.words_acc [] (skipn i (q_LN cx q)) = skipn kw (q_ws cx q) ->
  abytes_atR (rdW W mem) copy C -> length C = Z.to_nat (q_L0 cx q + 1) ->
  (forall j, (i <= j <= length (q_LN cx q))%nat -> nth_error C j = nth_error (q_LN cx q ++ [Z_to_bv 8 0]) j) ->
  aw_arr (rdW W mem) arr wp -> aw_found copy (q_ws cx q) C wp i ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + AW_S)) mem (seg_rom SEGS)) md) (lt_post B MT cx).

(* 0x8698c: one round of the split loop half done. From the head with cursor i and kw words found, the byte at i
   is not the NUL, strspn has skipped s = aw_spn (skipn i LN) separators, the byte at i + s is not the NUL (so a
   word starts there), w.n is kw + 1 (stored at 0x86940, before the pointer), the word's address is stored at
   arr[kw] (0x86978), and the strcspn wrapper has returned c = aw_cspn (skipn (i+s) LN) in a0; s7 = copy + i + s.
   Memory is the head's but for w.n and arr[kw]. The rest of the round (0x8698c .. 0x869d8) either leaves to LO_K
   (AW_E_stmt) or returns to the head with i' = i + s + c + 1 and kw + 1. *)
Definition AW_S2_stmt (m : nat) (nm : nat) : Prop :=
  forall cx q ly S W regs mem md k acc text copy arr (i s kw : nat) (C : list byte) (wp : list Z),
  q_m q = m ->
  Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
  aw_ctx cx q ly S W regs mem md k acc ->
  aw_rec cx q ly S W mem (aw_blocks cx q text copy arr) ->
  aw_wslots cx (rdW W mem) text copy arr ->
  getr regs 23 = w64 (copy + Z.of_nat (i + s)) ->
  getr regs 10 = w64 (Z.of_nat (aw_cspn (skipn (i + s) (q_LN cx q)))) ->
  aw_wn cx (rdW W mem) (Z.of_nat (kw + 1)) ->
  (* the head's invariant at i and kw *)
  nm = (length (q_LN cx q) - i)%nat -> (2 * kw <= i)%nat ->
  length wp = kw -> (kw <= length (q_ws cx q))%nat ->
  Verbs.words_acc [] (skipn i (q_LN cx q)) = skipn kw (q_ws cx q) ->
  abytes_atR (rdW W mem) copy C -> length C = Z.to_nat (q_L0 cx q + 1) ->
  (forall j, (i <= j <= length (q_LN cx q))%nat -> nth_error C j = nth_error (q_LN cx q ++ [Z_to_bv 8 0]) j) ->
  aw_found copy (q_ws cx q) C wp i ->
  (* this round so far *)
  s = aw_spn (skipn i (q_LN cx q)) -> (i + s < length (q_LN cx q))%nat ->
  aw_arr (rdW W mem) arr (wp ++ [copy + Z.of_nat (i + s)]) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + AW_S2)) mem (seg_rom SEGS)) md) (lt_post B MT cx).

(* 0x86a04 (LO_K): every word is found; w.n holds their count, the array their addresses, copy the words and
   their NULs. The three exits of the split loop (the head's *t = 0 at 0x868e8, after strspn at 0x8691c, after
   strcspn at 0x869ac) land here with these facts. *)
Definition AW_E_stmt (m : nat) : Prop :=
  forall cx q ly S W regs mem md k acc text copy arr (C : list byte) (wp : list Z),
  q_m q = m ->
  Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
  aw_ctx cx q ly S W regs mem md k acc ->
  aw_rec cx q ly S W mem (aw_blocks cx q text copy arr) ->
  aw_wslots cx (rdW W mem) text copy arr ->
  aw_wn cx (rdW W mem) (Z.of_nat (length (q_ws cx q))) ->
  length wp = length (q_ws cx q) ->
  abytes_atR (rdW W mem) copy C -> length C = Z.to_nat (q_L0 cx q + 1) ->
  aw_arr (rdW W mem) arr wp -> aw_found copy (q_ws cx q) C wp (Z.to_nat (q_L0 cx q + 1)) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + LO_K)) mem (seg_rom SEGS)) md) (lt_post B MT cx).

(* ---- the two ends of the segment in this file's words ---- *)

(* 0x86760: LT_W_stmt with the pass's message as one record; its budget is aw_rem plus the three mallocs *)
Definition AW_W_stmt (m : nat) : Prop :=
  forall cx q ly S W regs mem md k acc,
  q_m q = m ->
  Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
  aw_ctx0 cx q ly S W regs mem md k ->
  aw_rec cx q ly S W mem [] ->
  lt_bud MT cx S k acc (aw_rem cx q + 3) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + LO_SMRA)) mem (seg_rom SEGS)) md) (lt_post B MT cx).

Lemma aw_bud_eq : forall cx S k acc X Y, lt_bud MT cx S k acc X -> X = Y -> lt_bud MT cx S k acc Y.
Proof. intros cx S k acc X Y H <-. exact H. Qed.

Lemma LT_W_of_AW_W : forall m, AW_W_stmt m -> LT_W_stmt B MT m.
Proof.
intros m HW cx ly S W regs mem md k acc r Rh O1 HB HFRM HBody HMR. cbv zeta.
assert (HC0 : aw_ctx0 cx (mkAWM m r Rh O1) ly S W regs mem md k) by (unfold aw_ctx0; cbn [q_m q_r q_Rh]; tauto).
generalize (HW cx (mkAWM m r Rh O1) ly S W regs mem md k acc eq_refl HFRM HC0). clear HW HC0.
unfold aw_rec, aw_rem, q_R1, q_quit, q_run, q_R0, q_D, q_ws. cbn [q_m q_r q_Rh q_O1].
destruct (vr_runA _ _) as [[R1 x] quit]. cbn [fst snd].
intros HW Hrec Hbud. apply (HW Hrec). apply (aw_bud_eq cx S k acc _ _ Hbud). ring.
Qed.

(* 0x86a04: LT_K_stmt from this file's context *)
Lemma aw_LT_K : forall m, LT_K_stmt B MT m ->
  forall cx q ly S W regs mem md k acc text copy arr (wp : list Z),
  q_m q = m ->
  Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
  aw_ctx cx q ly S W regs mem md k acc ->
  lt_words cx (rdW W mem) (q_D cx q) (q_ws cx q) text copy arr wp ->
  aw_rec cx q ly S W mem (aw_blocks cx q text copy arr) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + LO_K)) mem (seg_rom SEGS)) md) (lt_post B MT cx).
Proof.
intros m HK cx q ly S W regs mem md k acc text copy arr wp <- HFRM HC Hw Hrec.
destruct HC as ((HB & HBody & HMR) & Hbud).
generalize (HK cx ly S W regs mem md k acc (q_r q) (q_Rh q) (q_O1 q) text copy arr wp HB HFRM HBody HMR). clear HK.
cbv zeta. revert Hw Hrec Hbud.
unfold aw_blocks, aw_rec, aw_rem, q_R1, q_quit, q_run, q_R0, q_D, q_ws.
destruct (vr_runA _ _) as [[R1 x] quit]. cbn [fst snd].
intros Hw Hrec Hbud HK. exact (HK Hw Hrec Hbud).
Qed.

End e.
End f.
End d.
