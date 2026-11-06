(* strip (fuzz_segconf.c:118-125, static; fuzz_segconf.asan-ubsan 0x879cc, 420 bytes, 105 instructions; frame 16
   bytes (`addi sp,sp,-16` / `sd ra,8(sp)` 0x879cc-0x879d0), no side-stack frame; program.asan-ubsan.tsv line 37):
   the contract of image B's code, in plugin-hostd/fuzz_command's lib/A/Prog form (afn_pre at the entry, SRr of
   apost_base at the return), in the image-A owner's image-independent vocabulary (lib/B/Prog/SegABase.v, image B's copy of
   lib/A/Prog/SegABase.v). Image A has no
   such function (clang inlines strip into m_file there), so this text has no lib/A twin; m_file is its only caller.
   Functional content: the segconf porter's UBSan contract lib/U/Prog/strip_c.v:10-67 (strip_pre :47-53, the post :64-65),
   restated over the ASan reader. The post is the U one: the cell sc holds s0 + strip_lead l and the cell ec holds
   e0 - strip_trail l, l the bytes [s0, e0) (seg_spec.zs). strip_lead, strip_trail and the pure lemmas strip_mid
   (the bytes between the two new pointers are SegModel.h_strip l) and strip_le are U's (lib/U/Prog/strip_c.v:44-45,
   :70-97), restated below with the same bodies and proofs: the U file Requires the UBSan image module Img0, so it
   cannot be Required here.
   What the code does (listing strip.fuzz_segconf.asan-ubsan.s, 0x879cc-0x87b6c): (sc | ec) & 7 <> 0 traps
   (0x879dc); the shadow base is loaded through the GOT word 0xa3210 (ld 0x879e4, ld 0x879e8); s = *sc, e = *ec
   (ld 0x87a0c, 0x87a10); s >= e goes to the back part (bgeu 0x87a14). Forward loop 0x87a30-0x87a80: s = 0 traps;
   the byte at s (lbu 0x87a44) is blank when it is <= 32 and bit (byte) of 0x100002200 is set (space, tab, CR:
   SegModel.blank); not blank leaves the loop; else s + 1 <=u 1 traps, s + 1 is stored at sc (sd 0x87a6c), e is
   reloaded (ld 0x87a78) and the loop goes on while s < e. Back part 0x87a94-0x87b1c: e = *ec, s = *sc (ld 0x87aa4,
   0x87aa8); s >= e returns; else (loop 0x87acc) e = 1 traps; the byte at e - 1 (lbu 0x87ae0) not blank returns;
   else e <u 2 traps, e - 1 is stored at ec (sd 0x87b04), s is reloaded (ld 0x87b10) and the loop goes on while
   s < e. The return is 0x87b30-0x87b38.
   It reads the two cells and bytes of [s0, e0) only. It writes its frame (ra at sp - 8) and the two cells: its
   footprint is [(sc, sc + 8); (ec, ec + 8)]. A leaf: it calls nothing but the error path.
   What it reads besides: the shadow base, through the GOT word as_got_shadow B (image B 0xa3210), whose value and
   target AR gives (AR_const_law, lib/B/YG0d.v:474-480), so the contract names neither. It calls no
   interceptor and loads no other image cell: no arodata_okP and no RLO / RHI (as reac_box_catalogue_c.v).
   ASAN FACTS ADDED over the U contract. Ten instrumented checks (program.asan-ubsan.tsv: _load1:2 _load8:6
   _store8:2), each a load of the shadow byte at (a >> 3) + the shadow base and a compare; the error path (a call of
   an errpath_* entry) is not reached:
   - the cell sc: load8 0x879f4 (error path 0x87b58), store8 0x87a60 (0x87b40), load8 0x87a9c (0x87b6c), load8
     0x87b08 (0x87b4c); the cell ec: load8 0x87a04 (0x87b5c), load8 0x87a70 (0x87b44), load8 0x87a94 (0x87b64),
     store8 0x87af8 (0x87b50). Each goes to the error path when the shadow byte is <> 0 (no slow path): killed by
     sc mod 8 = 0 and sa_addr rd sc 8 (one granule: saddr_ok at sc + 7 forces the shadow byte 0), the same for ec.
   - load1 of the byte at s (0x87a34-0x87a40, slow path 0x87a84-0x87a88, error path 0x87a90 with a0 = s) and of the
     byte at e - 1 (0x87ad0-0x87adc, slow path 0x87b20-0x87b24, error path 0x87b2c with a0 = e - 1): in both loops
     s0 <= s < e <= e0, so every address lies in [s0, e0): killed by sa_addr rd s0 (e0 - s0).
   - where each cell lies: each cell is a present slot at or above strip's sp and below the layout's top
     (spZ regs <= c, c + 8 <= ly_top ly, its 8 bytes apresent), in place of U's rw_cells and apart-from-[lo, sp).
     The top bound is what the two stores need: awr_byte admits a store to a caller's real-stack slot only by its
     arm `inFP FP a /\ sp0 <= a < ly_top ly` (lib/B/YCbq.v:598-605; found by the strip walk lane).
     This is NOT sa_dst's real-stack arm: that arm also
     asks astack_pres, which exists for a caller that keeps the pointer in s0 across a call (SegABase.v, the comment
     on sa_dst); strip is a leaf, keeps sc / ec in a0 / a1 and calls nothing, so it needs only the 16 bytes it loads
     and stores to be present, and m_file_c.v carries no astack_pres (the segconf porter's statement of 17:02Z). The cells'
     shadow is NOT in the slot shape: the eight cell checks above need it, so sa_addr rd c 8 stays (m_file's walk
     gives it from AR, below). The bytes by sa_loc: U's leaf had no frame; this one stores ra at sp - 8 before it
     reads a byte, so the bytes must lie outside strip's stack window [sp - STK_strip, sp), which every arm of
     sa_loc gives. The bytes stay apart from the cells (sa_disj), as in U, because strip stores to the cells before
     it reads the next byte.
   - U's e0 < 2 ^ 64 follows from sa_addr rd s0 (e0 - s0) (s0 + (e0 - s0) <= 2 ^ 63) and is not restated.
   - no side-stack frame, no interceptor, no printf: apost_base, EV_strip = 0, post tail sa_noalloc.
   - sa_kept segs W mem W' mem' regs STK_strip (the two cells) in the post: every byte outside the stack window and
     the two cells reads as at the entry, the shadow of image objects included (SegABase.v's sa_kept). True of the
     code: no side-stack frame, no set_shadow entry, and its stores are ra into its frame (0x879d0) and the two cells
     (0x87a6c, 0x87b04).
   UBSAN TRAPS (trap mode: a compare and a branch to the `unimp` at 0x87b3c; each branch is not taken):
   - 0x879dc `bnez` of (sc | ec) & 7: killed by sc mod 8 = 0 and ec mod 8 = 0.
   - 0x87a30 `beqz a6` (s = 0, forward loop): s >= s0 > 0 (s only grows).
   - 0x87a5c `bgeu t1,a2` (t1 = 1, a2 = s + 1, forward loop): s0 <= s < e <= e0 <= 2 ^ 63, so 2 <= s + 1 < 2 ^ 64.
   - 0x87acc `beq a6,a7` (e = 1) and 0x87af4 `bltu a6,t2` (t2 = 2, e <u 2), back loop: e > s >= s0 >= 1, so e >= 2.
   Call sites (all in m_file, listing m_file.fuzz_segconf.asan-ubsan.s; segA/evidence/callsites.asan-ubsan.tsv lines
   94, 96, 98, 102, 103). m_file (0x86140, frame 320, STK_m_file 8,592 at image B): `addi sp,sp,-320` (0x86140),
   saves at sp0 - 8 .. sp0 - 104, s1 = (sp0 - 320) & -32 (0x86180-0x86184); its class-1 side-stack frame is requested
   with a0 = 128 at 0x861b4 (AR's use-after-return cell is 1: lib/B/YG0f.v:193-195 aso_const_law), so every callee
   runs at sp = s1 (in the real-stack fallback 0x861cc-0x861e4, sp is lower still, and the slots stay above it). At
   each site a0 = s1 + X, a1 = s1 + Y:
   - the cells: two distinct slots, 8-aligned (s1 is 32-aligned, X and Y multiples of 8), inside m_file's real frame
     (s1 + 216 <= sp0 - 104, below the saves), so at or above strip's sp, below m_file's entry sp0 and so below
     ly_top (afn_pre's astk_ok gives sp0 <= ly_top ly, lib/B/YCbq.v:452-454), and inside m_file's own window
     [sp0 - STK_m_file, sp0), which m_file's afn_pre gives present (lib/B/YCbq.v:460) and m_file's own `sd`
     to each slot writes before the call; their shadow is zero by AR's zshadow_ok over [ly_stk_lo, ly_stk_hi)
     (lib/B/YG0n.v:193-196; the route lib/B/Prog/reac_segconf_role_c.v:25-28 takes for its real-stack out),
     which with X mod 8 = 0 gives sa_addr rd c 8. No premise of m_file_c.v is added.
   - the values: s0 and e0 point into m_file's text block t (a heap block: m_file_pre's sa_heap, sa_addr and sa_str
     of t, lib/B/Prog/m_file_c.v:218-219, image B's copy of the image-A owner's FINAL 6f783602b5e3) with
     t <= s0 <= e0 <= t + |text|, which gives sa_bytes, sa_addr, sa_loc (its heap arm) and 0 < s0 (t <> 0, sa_addr's
     0 <= t). The block lies below alloc_ceiling and the real frame above it: sa_disj of the bytes and each cell.
   - 0x864c0 (c:285, the line after the comment cut): a0 = s1 + 176 (`sd s10,176(s1)` 0x86384, the line start), a1 =
     s1 + 168 (the line end: strchr's '\n' 0x8638c, or start + strlen 0x863bc, or the comment mark 0x864b0); each end
     is found from the start by a forward search, so s0 <= e0.
   - 0x86530 (c:167, the header between '[' and ']'): a0 = s1 + 208 holding b + 1 (0x86520; b the stripped line
     start, whose byte is '[', 0x864f0), a1 = s1 + 200 holding memchr's ']' (0x86524), the last byte (`bne` 0x86510);
     the byte at b is not ']', so memchr's answer is >= b + 1 = s0.
   - 0x865a0 (c:173, the name after "segment"): a0 = s1 + 192 holding h1 + 7 (0x86590), a1 = s1 + 184 holding h2
     (0x86594), h1 / h2 the cells after the strip at 0x86530 (this contract's post), h2 - h1 >= 8 (`blt` 0x86544).
   - 0x86658 (c:205, the key): a0 = s1 + 208 holding b (0x86634), a1 = s1 + 200 holding memchr's '=' (0x86638;
     `beqz` 0x86630 refuses NULL), which lies in [b, e) (row 20's post).
   - 0x86664 (c:206, the value): a0 = s1 + 192 holding '=' + 1 (0x86648), a1 = s1 + 184 holding e (0x8664c; s4, the
     e cell after the strip at 0x864c0, loaded at 0x864c8); '=' < e.
   image B: A_strip = 0x879cc (twin .symtab); STK_strip = 16 (its frame; the error path is dead).
   IMAGE-INDEPENDENT: no image module is Required; A_strip and STK_strip are parameters, and the shadow-base cells
   are fields of B.
   KIT: image B's copies (the segconf porter's image-B kit derivation, commit 694f3575dda2, and
   the image-B kit name map): YA0n YG0f YG0n YG0d YCbq from lib.B, SegPgBase / SegABase from
   lib.B.Prog; no lib/A file and none of the 44 B kit modules from lib.Reusable.
   The WALK takes no runtime entry as a Section hypothesis: the function calls none on its good path. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* The leading blanks, and the trailing blanks of what is left after them (U's lib/U/Prog/strip_c.v:44-45, the same
   bodies). *)
Definition strip_lead (l : list Z) : nat := length (takewhile blank l).
Definition strip_trail (l : list Z) : nat := length (takewhile blank (rev (dropwhile blank l))).

(* What strip reads and writes, through a reader rd (the U strip_pre, lib/U/Prog/strip_c.v:47-53, without its stack
   conjuncts): two distinct 8-aligned cells, addressable, holding s0 and e0; the bytes l of [s0, e0), addressable,
   0 < s0 <= e0; the bytes apart from both cells. *)
Definition strip_args (rd : reader) (sc ec s0 e0 : Z) (l : list byte) : Prop :=
sc mod 8 = 0 /\ ec mod 8 = 0 /\ sa_disj sc 8 ec 8 /\
sa_val rd sc 8%nat s0 /\ sa_addr rd sc 8 /\ sa_val rd ec 8%nat e0 /\ sa_addr rd ec 8 /\
0 < s0 <= e0 /\ sa_bytes rd s0 l /\ Z.of_nat (length l) = e0 - s0 /\ sa_addr rd s0 (e0 - s0) /\
sa_disj s0 (e0 - s0) sc 8 /\ sa_disj s0 (e0 - s0) ec 8.

(* Where each cell lies: a present 8-byte slot at or above the entry sp and below the layout's top (the segconf porter's slot
   shape for strip, 17:02Z, with the top bound found by the strip walk lane: the stores at 0x87a6c and
   0x87b04 need awr_ok, and awr_byte admits a store to a caller's real-stack slot only by its arm
   `inFP FP a /\ sp0 <= a < ly_top ly`, lib/B/YCbq.v:598-605). Not sa_dst's real-stack arm: strip is a leaf, so it
   needs no astack_pres (see the head comment). *)
Definition strip_slot (ly : alayout) (H : word -> bool) (mem : word -> option byte) (sp c : Z) : Prop :=
sp <= c /\ c + 8 <= ly_top ly /\ forall i, 0 <= i < 8 -> apresent H mem (c + i).

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Section d.
Variable B : asyms.
(* What strip asks of its caller over the reader rd = aview segs (w_H W) mem: strip_args, each cell a present slot at
   or above this call's entry sp (strip_slot; regs are this call's entry registers), the bytes in a heap block, a
   side-stack frame or the image (sa_loc). The U stack_ok / apart-from-[lo, sp) / mem_inv conjuncts are afn_pre's,
   strip_slot's and sa_loc's here. Outside the sections: strip_pre segs B ly S W mem regs sc ec s0 e0 l. *)
Definition strip_pre (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte)
(regs : bvmap 5 word) (sc ec s0 e0 : Z) (l : list byte) : Prop :=
strip_args (aview segs (w_H W) mem) sc ec s0 e0 l /\
strip_slot ly (w_H W) mem (spZ regs) sc /\ strip_slot ly (w_H W) mem (spZ regs) ec /\
sa_loc segs B ly S s0 (e0 - s0).
(* the events this call spends: 0, it reaches no allocator entry *)
Definition EV_strip : Z := 0.
Definition strip_contract (A_strip STK_strip : Z) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (sc ec s0 e0 : Z) (l : list byte),
afn_pre segs B STK_strip ly S W regs mem md ch ->
getr regs 10 = w64 sc -> 0 <= sc < 2 ^ 64 -> getr regs 11 = w64 ec -> 0 <= ec < 2 ^ 64 ->
strip_pre ly S W mem regs sc ec s0 e0 l ->
st_nev S + EV_strip <= EV_MAX ->
SRr segs W (cfg_at segs A_strip regs mem md)
(apost_base segs B STK_strip [(sc, sc + 8); (ec, ec + 8)] regs ly S W mem md EV_strip
(fun ly' S' W' regs' mem' md' =>
 sa_val (aview segs (w_H W') mem') sc 8%nat (s0 + Z.of_nat (strip_lead (seg_spec.zs l))) /\
 sa_val (aview segs (w_H W') mem') ec 8%nat (e0 - Z.of_nat (strip_trail (seg_spec.zs l))) /\
 sa_kept segs W mem W' mem' regs STK_strip (fun a => sc <= a < sc + 8 \/ ec <= a < ec + 8) /\
 sa_noalloc B ly S ly' S')).
End d.
End c.
End b.

(* ================================ facts about the post (pure lists) ================================ *)
(* U's lib/U/Prog/strip_c.v:70-97, statements and proofs unchanged. *)
Lemma dropwhile_skipn (P : Z -> bool) (l : list Z) : dropwhile P l = skipn (length (takewhile P l)) l.
Proof. induction l as [|b r IH]; cbn; [reflexivity|]. destruct (P b); cbn; [exact IH | reflexivity]. Qed.

Lemma takewhile_le (P : Z -> bool) (l : list Z) : (length (takewhile P l) <= length l)%nat.
Proof. induction l as [|b r IH]; cbn; [lia|]. destruct (P b); cbn; lia. Qed.

Lemma dropwhile_length (P : Z -> bool) (l : list Z) :
  length (dropwhile P l) = (length l - length (takewhile P l))%nat.
Proof. rewrite dropwhile_skipn, length_skipn. reflexivity. Qed.

(* The bytes between the two new pointers are h_strip of the bytes. *)
Lemma strip_mid (l : list Z) :
  firstn (length l - strip_lead l - strip_trail l) (skipn (strip_lead l) l) = h_strip l.
Proof.
  unfold strip_lead, strip_trail, h_strip.
  rewrite (dropwhile_skipn blank (rev (dropwhile blank l))).
  rewrite skipn_rev, rev_involutive.
  remember (length (takewhile blank (rev (dropwhile blank l)))) as t eqn:Et. clear Et.
  rewrite (dropwhile_skipn blank l), length_skipn. reflexivity.
Qed.

(* The new s is at most the new e. *)
Lemma strip_le (l : list Z) : (strip_lead l + strip_trail l <= length l)%nat.
Proof.
  unfold strip_lead, strip_trail.
  pose proof (takewhile_le blank (rev (dropwhile blank l))) as H1. rewrite length_rev in H1.
  pose proof (dropwhile_length blank l) as H2. pose proof (takewhile_le blank l) as H3. lia.
Qed.
