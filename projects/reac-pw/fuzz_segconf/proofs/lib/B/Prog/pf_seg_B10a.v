(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3): segment B10a of reac_segconf_parse_file's
   walk, the theorem S_B10a_holds : S_B10a B of lib/B/Prog/pf_pieces.v (ROLE 0x88630 -> INTENT 0x888e4). The
   B10a segment lane of the image-B G3 walk owner, 2026-10-30.
   proves function reac_segconf_parse_file (segment B10a; reuse search and CONFIRM:
   the rule-24 lookup record, the rule-24 checker 2026-10-30T16:55:47Z; reuse verdict none).
   ADAPTED from a working branch (the image-A G3 walk owner's image-A lane of the same segment, lib/A/Prog/pf_a10a_k.v
   73bafa8e5cd9) and the UBSan piece walk of the same fold (a working branch's lib/U/Prog/pf_p6.v);
   closed against G3 FINAL at 6f783602b5e3 (B kit 694f3575dda2).
   The segment (61 instructions: 0x88630-0x886d4, 0x888bc-0x888e4, the slow arms 0x88fb4-0x88fcc and the error
   calls 0x8923c-0x89244, 0x89280-0x89288), in four runs (lib/B/Prog/pf_seg_B10a_s.v):
     P0  low's eight shadow cells in scope (plain run)                        pf_seg_B10a_p.v b10_role_ok
     P1  val (slot 0x70), check B#16, val[0], `beqz`                          pf_seg_B10a_p.v b10_p1_ok
     LOOP the fold, low[li] = fold(val[li]), T17, check B#17, val[li + 1]    pf_seg_B10a_l.v b10_loop_ok
     EXIT T20, s7 = low, check B#25, low[li] = 0, then INTENT (H_INTENT)      pf_seg_B10a_x.v b10_exit_ok
   UBSan trap branches (to the `unimp` 0x891c8), the fact that keeps each one not taken:
     T17 0x8869c `beq a3,s10` (a3 = val + li, s10 = -1): val + li < buf + 512 <= 0x7fffff800000 < 2 ^ 64 - 1
         (val lies in buf, INV_KV's pf_kv / pf_inb; the frame below alloc_ceiling, the journal's class-5 frame).
     T20 0x888c4 `bltu a0,a3` (a0 = slot 0x30 = ~low = 2 ^ 64 - 1 - (F + 0x280), a3 = li <= 63): ~low >= 2 ^ 64 - 1 -
         2 ^ 47 > 63 (PF_SL's slot 0x30, the same frame bound).
   Inline ASan checks, each covered by a shadow entry, so no error call (0x89240, 0x89280, 0x89284) is reached:
     B#16 0x8865c load1 at val (buf's 64 cells 0 inside a line, pf_fsh PF_SC_LINE);
     B#17 0x886ac load1 at val + li + 1 (li + 1 <= |val|, inside buf);
     B#25 0x888d8 store1 at low + li (low's 8 cells zeroed by P0).
   Section hypotheses: none beyond pf_pieces.v's Section s (rc, SK, PI, B); AR_laws is the base lemma
   YG0q.AR_laws_ok. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YP09 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable SegSyms SegList SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces pf_seg_B10a_s pf_seg_B10a_x
  pf_seg_B10a_l pf_seg_B10a_p.
Import ListNotations.
Open Scope Z_scope.

Section s.
Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
Variable B : asyms.

Theorem S_B10a_holds : S_B10a B.
Proof.
unfold S_B10a. intros f0 n HI.
pose proof (YG0q.AR_laws_ok (@pa_segs _ seg_listing PI) B) as LAWS.
apply (b10_role_ok (fx := f0) B LAWS n).
apply (b10_p1_ok (fx := f0) B LAWS n).
- exact (b10_exit_ok (fx := f0) B LAWS n (HI f0)).
- exact (b10_loop_ok (fx := f0) B LAWS n (b10_exit_ok (fx := f0) B LAWS n (HI f0))).
Qed.
End s.
