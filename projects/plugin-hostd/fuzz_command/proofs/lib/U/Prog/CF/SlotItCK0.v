From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes MState.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import CommandModel CommandFP SlotSpec
  SlotRuns check_reply_c check_arity_c check_reply_answer_c rec_shape_of_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require SlotWords.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

(* The state at check_words' entry (pc 0x14bac, returning to 0x14390) after the splitter, check_reply and
   check_arity: the words of the message's line in copy, their addresses in arr, the struct words at sp + 24; the
   locals at sp (LOC0 jsv) and the callee-saved registers but s4 are those of the splitter's start. *)
Definition w_post (sp gp tp s2 s3 s5 s6 s7 s10 : word) (m0 : word -> option byte) (lo src len text copy arr : Z)
    (M : list byte) (jsv : list byte) : machine_state -> Prop := fun ms' =>
  exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' t3' t4' t5' t6' (Ft : bvmap 5 word) (fc' : bv 32) m' T C Aa
    (wp : list Z) jp,
    ms' = MS (mkR (Z_to_bv 64 0x14390) sp gp tp t0' t1' t2' (Z_to_bv 64 src) (Z_to_bv 64 len)
                  (Z_to_bv 64 (bv_unsigned sp + 24)) a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4' s5 s6 s7 (Z_to_bv 64 MASK) (Z_to_bv 64 32) s10 (Z_to_bv 64 (2 ^ 64 - 1))
                  t3' t4' t5' t6')
             Ft (Z_to_bv 64 0x14bac) fc' None m' (seg_rom rsegs) /\
    munch [(text, text + strnlen_res len M + 1); (copy, copy + strnlen_res len M + 1);
           (arr, arr + arr_size (strnlen_res len M)); (lo, bv_unsigned sp + 56)] m0 m' /\
    wmono rsegs m0 m' /\ mem_inv rsegs m' /\ frm0 fc' /\
    rw_cells rsegs m' (bv_unsigned sp) (LOC0 jsv) /\
    rw_cells rsegs m' (bv_unsigned sp + 24)
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

(* From check_reply's entry (the splitter's post CF.SlotWords.sw_post, pc 0x144d8, ra 0x14380) to check_words' entry:
   check_reply, 0x14380 .. check_arity, check_arity, 0x14388 .. check_words. The premises are those of the plain
   ck_spec (SlotItB2.v) with the ubsan image, frame (160) and the 8-aligned sp the ubsan checks need. *)
Definition ck_spec : Prop :=
  forall (sp gp tp s2 s3 s5 s6 s7 s10 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
    (lo src len text copy arr : Z) (M : list byte) (jsv : list byte) (can ans rep : word) (xr slack xa : list byte)
    (nc fn0 q : Z),
  let L0w := strnlen_res len M in
  let ws := Verbs.words (Verbs.line M) in
  let W0 := [(text, text + L0w + 1); (copy, copy + L0w + 1); (arr, arr + arr_size L0w);
             (bv_unsigned sp - 96, bv_unsigned sp + 56)] in
  0x54f98 <= lo -> lo + 6000 <= bv_unsigned sp -> bv_unsigned sp + 160 <= 2 ^ 63 ->
  bv_unsigned sp + 160 <= TASK_SIZE -> bv_unsigned sp mod 8 = 0 ->
  0 <= len <= 8192 -> 0 <= src /\ src + len <= lo -> 0 <= L0w <= len ->
  0 < text /\ text + L0w + 1 <= lo -> 0 < copy /\ copy + L0w + 1 <= lo -> 0 < arr /\ arr + arr_size L0w <= lo ->
  arr_size L0w = 8 * (L0w / 2) + 16 ->
  check_reply_contract -> check_arity_contract ->
  Z.of_nat (length M) = len ->
  text + L0w + 1 <= 0x10000 \/ 0x54f98 <= text ->
  copy + L0w + 1 <= 0x10000 \/ 0x54f98 <= copy ->
  arr + arr_size L0w <= 0x10000 \/ 0x54f98 <= arr ->
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
  forall ms, CF.SlotWords.sw_post sp gp tp s2 s3 s5 s6 s7 s10 F fc m0 lo src len text copy arr M jsv ms ->
  evt rsegs (w_post sp gp tp s2 s3 s5 s6 s7 s10 m0 lo src len text copy arr M jsv) ms.
