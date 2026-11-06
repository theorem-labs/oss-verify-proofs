(* The image-B (fuzz_reply.asan-ubsan) twin of
   part 1 of lib/A/ReplyLS3w.v (a working branch 1318828167d3, :73-125, the exit's count post:
   xcnt_post, xcnt_pre_post, fr_LS3c_exit_cnt, fr_LS3c_exit_cnt_ret), with A's names and statements, plus
   xcnt_ok_of_post (A: lib/A/ReplyLScap.v :595-601) and LS_exit_cnt_3c, B top_x's LS_exit_cnt at LSx := fr_LS3c.
   Part 2 of A's file (the long-input witness) is not ported here.  proves no function (kind: invariant lemma).
   A -> B SWAPS (as row G-BLS3-port's lib/B/ReplyB3LS3c.v makes them):
   - the Require header is lib/B/ReplyB3LS3c.v's, plus ReplyB3LS3c itself and lib/B/ReplyCnt.v (cand13's, Required
     only: its xcnt_ok is the cut's XCNT name); A's ReplyLSCntL / ReplyLS3c -> lib/B/ReplyB3LSCntL.v / ReplyB3LS3c.v;
   - fr_LS3c B -> fr_LS3c B CALL_ROOM_B (the call room is a Section variable of lib/B/ReplyB3LS3.v); the Section takes
     {SK : YI16.sink_head} as ReplyB3LS3c.v's does.
   A's header follows. *)
(* The count half of LS v3, part 6: the exit's count post and a long-input witness (a Theorem Labs lane's FREE-PIECES row B1c,
   a Theorem Labs lane).  proves no function (kind: invariant lemma).

   1. The exit's count post (a Theorem Labs lane 23:56Z).  The blocks one call leaves live are the next call's entry blocks, so the
      exit must give back the entry's count bound: xcnt_pre (ReplyLS3c.v) bounds the entry's blocks other than the
      input, the kept table and g_out.  xcnt_post is the same bound at any (ly, S); xcnt_pre is xcnt_post at the
      entry's (c_ly, c_S) (xcnt_pre_post).  fr_LS3c_exit_cnt: at the premises of LS_exit_end (the model rule of
      lib/A/W_LLVMFuzzerTestOneInput_exit_x.v:158-167 at a working branch bb9dae5d905: LS at S3 with
      ablocks S3 ~ input ++ model ++ rest, and ablocks S' ~ input ++ (lm_G m, ATABLE) :: aout_blks cap out ++ rest,
      the same rest), xcnt_post holds at S' with T0 := lm_G m: what S' holds besides the input, the table and g_out is
      fr_LS3's rest, and fr_CNT bounds the rest.  The one added premise is the block law's address bound (every live
      block's address is >= 4096), which gives lm_G m <> 0, so the table is the xcnt form's [(T0, ATABLE)]; the exit
      arm has it at S' as exit_x.v:360-362 lxk_blk_x (from the laws' alx_blocks; the cf law AR_blocks_law_cf,
      Reusable/YG0dcf.v:576).  fr_LS3c_exit_cnt_ret: the same at the returned state stack_free_state 1 fpos S' (it
      keeps the chunks).
   2. A long-input witness (a Theorem Labs lane's acceptance for the room round: an input of >= 72,687 BEGIN lines).  One open
      source (slot 0, the first head's) whose relay entry holds 72,687 keys of 22, 23 and 24 bytes (24,229 of each; a
      key block is its text and the NUL, 23..25 bytes), its 16,384-byte line buffer and its key-pointer array of
      8 * 72,688 = 581,504 bytes; the table; the source's partial buffer; no out buffer.  The 72,687 lines carry
      1,671,801 key bytes and 72,687 newlines = 1,744,488 bytes, which 27 writes of at most 65,535 bytes carry
      (t = 27); the input is those bytes and 4 header bytes per write (op, source, two length bytes:
      W_LLVMFuzzerTestOneInput_write.v:169-178), 1,744,596 bytes, all consumed.  The allocator state holds exactly the
      input block and the model's blocks (ablocks = input ++ model ++ [], as ReplyLS3.v sat3 builds ls3_S from chunks;
      the 72,687 key chunks come from a Fixpoint), and the call's entry state holds only the input block.
      w_fr_LS3c proves fr_LS3c there; w_sec_cut evaluates ReplyLSCntM.fr_LS3c_sec_cut (106); w_counts computes the
      state's counts (secondary 2, class 2: 72,687, classes 18, 24, 27: 1 each, cnt24 = 1); w_classes names each
      block's class.  Every computed fact is a
      vm-checked equation (assert (E : f x = v) by (vm_compute; reflexivity)).  The key texts are distinct by
      construction (three index bytes) and NUL-free; the witness proves fr_LS3c only (not RINV or amodel_at). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame W_op_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_head W_LLVMFuzzerTestOneInput_small W_LLVMFuzzerTestOneInput_write
W_LLVMFuzzerTestOneInput_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSB ReplyB3Base.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyB3LS3 ReplyB3LSCntL.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyB3LS3c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyCnt.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ================================================================== 1. the exit's count post *)
Section xpost.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* the call room of fr_LS3 (lib/B/ReplyB3LS3.v, a Section variable as ReplyLSB.fr_LS takes it) *)
Variable CALL_ROOM_B : Z.

(* xcnt_pre's bound at a state (ly, S): the blocks of S other than the input, the kept table (when T0 <> 0) and g_out *)
Definition xcnt_post (cx : lfcx) (ly : alayout) (S : astate) (T0 cap out : Z) : Prop :=
  cnt_sec (ablocks B ly S) - cnt_sec (input_blks cx ++ (if T0 =? 0 then [] else [(T0, ATABLE)]) ++
    aout_blks cap out) <= SEC0 /\
  forall c, cnt_cls c (ablocks B ly S) - cnt_cls c (input_blks cx ++
    (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out) <= CLS0.

(* the entry's bound is the post's form at the entry's state *)
Lemma xcnt_pre_post : forall cx T0 cap out,
  xcnt_pre B cx T0 cap out <-> xcnt_post cx (c_ly cx) (c_S cx) T0 cap out.
Proof. intros cx T0 cap out. unfold xcnt_pre, xcnt_post. split; intros H; exact H. Qed.

(* the exit: S' holds the input, the table, g_out and fr_LS3's rest; fr_CNT bounds the rest *)
Lemma fr_LS3c_exit_cnt : forall cx t m ly3 S3 rest (ly' : alayout) (S' : astate) cap out,
  fr_LS3c B CALL_ROOM_B cx t m ly3 S3 ->
  Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
  Permutation (ablocks B ly' S') (input_blks cx ++ (lm_G m, ATABLE) :: aout_blks cap out ++ rest) ->
  (forall p n, In (p, n) (ablocks B ly' S') -> 4096 <= p) ->
  xcnt_post cx ly' S' (lm_G m) cap out.
Proof.
  intros cx t m ly3 S3 rest ly' S' cap out (_ & (C1 & C2 & _)) HP3 HP' HA.
  assert (HG : (lm_G m =? 0) = false).
  { apply Z.eqb_neq. intros E.
    assert (Hin : In (lm_G m, ATABLE) (ablocks B ly' S')).
    { apply (Permutation_in _ (Permutation_sym HP')). apply in_or_app. right. left. reflexivity. }
    pose proof (HA _ _ Hin). lia. }
  unfold xcnt_post. rewrite HG. cbv beta iota. split.
  - rewrite (cnt_sec_perm _ _ HP3), !cnt_sec_app in C1.
    rewrite (cnt_sec_perm _ _ HP').
    repeat progress rewrite ?cnt_sec_app, ?cnt_sec_cons, ?cnt_sec_nil. lia.
  - intros c. specialize (C2 c).
    rewrite (cnt_cls_perm _ _ _ HP3), !cnt_cls_app in C2.
    rewrite (cnt_cls_perm _ _ _ HP').
    repeat progress rewrite ?cnt_cls_app, ?cnt_cls_cons, ?cnt_cls_nil. lia.
Qed.

(* the same at the state the call returns (stack_free_state keeps the chunks) *)
Lemma fr_LS3c_exit_cnt_ret : forall cx t m ly3 S3 rest (ly' : alayout) (S' : astate) fpos cap out,
  fr_LS3c B CALL_ROOM_B cx t m ly3 S3 ->
  Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
  Permutation (ablocks B ly' S') (input_blks cx ++ (lm_G m, ATABLE) :: aout_blks cap out ++ rest) ->
  (forall p n, In (p, n) (ablocks B ly' S') -> 4096 <= p) ->
  xcnt_post cx ly' (stack_free_state 1 fpos S') (lm_G m) cap out.
Proof.
  intros cx t m ly3 S3 rest ly' S' fpos cap out H HP3 HP' HA.
  assert (E : ablocks B ly' (stack_free_state 1 fpos S') = ablocks B ly' S') by reflexivity.
  unfold xcnt_post. rewrite E. exact (fr_LS3c_exit_cnt cx t m ly3 S3 rest ly' S' cap out H HP3 HP' HA).
Qed.
(* ---- the cut's XCNT name (lib/B/ReplyCnt.v xcnt_ok, cand13) is xcnt_post with the class bound restricted to
   1 <= c <= 30: both count over xcnt_kept's list.  lib/B/ReplyCnt.v's cnt_sec / cnt_cls / SEC0 / CLS0 and
   lib/B/ReplyB3LSCntL.v's / ReplyB3LS3c.v's are the same terms up to unfolding (ReplyCnt.cnt_cls_ccnt is reflexivity).
   (A: lib/A/ReplyLScap.v :595-601, s5-r9.) ---- *)
Lemma xcnt_ok_of_post : forall cx (ly : alayout) (S : astate) T0 cap out,
  xcnt_post cx ly S T0 cap out -> ReplyCnt.xcnt_ok B S ly (input_blks cx) T0 cap out.
Proof.
  intros cx ly S T0 cap out (H1 & H2). unfold ReplyCnt.xcnt_ok, ReplyCnt.xcnt_kept. split.
  - exact H1.
  - intros c _. exact (H2 c).
Qed.

(* ---- B top_x's LS_exit_cnt (lib/B/W_LLVMFuzzerTestOneInput_top_x.v :341 at W8's room branch 33adc98d051c; the same
   text as a Theorem Labs lane's lib/B/W_LLVMFuzzerTestOneInput_exit_x.v :192) at LSx := fr_LS3c B CALL_ROOM_B, TfibB := B ---- *)
Lemma LS_exit_cnt_3c : forall cx t m ly3 S3 rest (ly' : alayout) (S' : astate) cap out,
  fr_LS3c B CALL_ROOM_B cx t m ly3 S3 ->
  Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
  Permutation (ablocks B ly' S') (input_blks cx ++ (lm_G m, ATABLE) :: aout_blks cap out ++ rest) ->
  (forall p n, In (p, n) (ablocks B ly' S') -> 4096 <= p) ->
  ReplyCnt.xcnt_ok B S' ly' (input_blks cx) (lm_G m) cap out.
Proof.
  intros cx t m ly3 S3 rest ly' S' cap out H HP3 HP' HA.
  exact (xcnt_ok_of_post cx ly' S' (lm_G m) cap out (fr_LS3c_exit_cnt cx t m ly3 S3 rest ly' S' cap out H HP3 HP' HA)).
Qed.
End xpost.
