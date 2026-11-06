(* fold (fuzz_segconf.c:140-148, static; fuzz_segconf.asan-ubsan 0x87c94, 280 bytes, 70 instructions; frame 16 bytes
   (`addi sp,sp,-16` / `sd ra,8(sp)` 0x87c94-0x87c98), no side-stack frame; program.asan-ubsan.tsv line 38): the
   contract of image B's code, in plugin-hostd/fuzz_command's lib/A/Prog form (afn_pre at the entry, SRr of
   apost_base at the return), in the image-A owner's image-independent vocabulary (lib/B/Prog/SegABase.v, image B's copy of
   lib/A/Prog/SegABase.v). Image A has no
   such function (clang inlines fold into m_file there), so this text has no lib/A twin; m_file is its only caller.
   Functional content: the segconf porter's UBSan contract lib/U/Prog/fold_c.v:10-60 (fold_out :38, fold_pre :40-46, the post
   :53-58), restated over the ASan reader. The post is the U one: a0 = length (fold_out l cap) and the bytes at out
   are fold_out l cap = SegModel.h_fold (zs l) cap and a NUL, l the n bytes at s (cap >= 1, so cap - 1 is exact and
   h_fold's firstn (cap - 1) has k = min(n, cap - 1) bytes). fold_out is U's Definition (lib/U/Prog/fold_c.v:38),
   restated below with the same body: the U file Requires the UBSan image module Img0, so it cannot be Required here.
   What the code does (listing fold.fuzz_segconf.asan-ubsan.s, 0x87c94-0x87da8): the GOT word 0xa3210 (ld 0x87ca0)
   then the shadow base (ld 0x87cb0); k = n when n <u cap - 1, else cap - 1 (`addi a3,a3,-1`, `bltu`, `mv`
   0x87ca4-0x87cac); k = 0 goes to 0x87d64 (a6 = ~out); else for i = 0 .. k-1 (a3 = s + i, a4 = t2 = out + i,
   t1 = s + i, t3 counts k down; loop head 0x87cd8): the trap tests below, the byte s[i] (lbu 0x87d0c), plus 32 when
   s[i] - 'A' <u 26 (0x87d14-0x87d30: SegModel.lower), stored at out + i (sb 0x87d34); then (0x87d68) the out + k
   trap test, `sb zero` at out + k (0x87d80), a0 = k (0x87d84), return 0x87d88-0x87d90.
   It reads the first k bytes at s; it writes its frame (ra at sp - 8) and [out, out + k + 1), k = length
   (fold_out l cap): that range is its footprint. A leaf: it calls nothing but the error path.
   What it reads besides: the shadow base, through the GOT word as_got_shadow B (image B 0xa3210), whose value and
   target AR gives (AR_const_law, lib/B/YG0d.v:474-480), so the contract names neither. It calls no
   interceptor and loads no other image cell: no arodata_okP and no RLO / RHI (as reac_box_catalogue_c.v).
   ASAN FACTS ADDED over the U contract. Three instrumented checks (program.asan-ubsan.tsv: _load1:1 _store1:2), each a
   load of the shadow byte at (a >> 3) + the shadow base and a compare; the error path (a call of an errpath_* entry)
   is not reached:
   - load1 of s + i (0x87cf0-0x87cfc, slow path 0x87d48-0x87d4c, error path 0x87da8 with a0 = s + i), i < k:
     killed by sa_addr rd s k.
   - store1 of out + i (0x87d00-0x87d10, slow path 0x87d54-0x87d58, error path 0x87d60 with a0 = out + i) and of
     out + k (0x87d70-0x87d7c, slow path 0x87d98-0x87d9c, error path 0x87da0): killed by range_addressable rd
     SHADOW_OFF out (k + 1), half of sa_dst's frame arm.
   - ONLY THE k BYTES READ ARE ASKED (the segconf porter's statement of 17:02Z): l still has U's length n, so the post is U's
     h_fold (zs l) cap word for word, but the reader must give only firstn k l at s (h_fold reads no byte past k);
     the caller instantiates l with all n bytes it knows. s <> 0 is asked only when k > 0: the k = 0 path never
     touches s.
   - where each object lies: s's k bytes by sa_loc; out's k + 1 bytes by sa_dst's FRAME ARM only (sa_fframe and
     range_addressable; the segconf porter's statement), in place of U's wr_at. Both keep them outside fold's stack window
     [sp - STK_fold, sp), which replaces U's apart premises from [lo, sp) (U's leaf had no frame; this one stores ra
     at sp - 8). s's bytes stay apart from out's (sa_disj), as in U, because fold stores out[i] before it reads
     s[i + 1].
   - no side-stack frame, no interceptor, no printf: apost_base, EV_fold = 0, post tail sa_noalloc.
   - sa_kept segs W mem W' mem' regs STK_fold [out, out + k + 1) in the post: every byte outside the stack window and
     that range reads as at the entry, the shadow of image objects included (SegABase.v's sa_kept). True of the code:
     no side-stack frame, no set_shadow entry, and its stores are ra into its frame (0x87c98), out + i (0x87d34) and
     out + k (0x87d80).
   UBSAN TRAPS (trap mode: a compare and a branch to the `unimp` at 0x87d94; each branch is not taken), at each i < k:
   - 0x87cd8 `bltu a3,a0` (s + i <u s, the add wraps): s + i < s + k <= 2 ^ 63 (sa_addr rd s k).
   - 0x87ce4 `beqz t4` with t4 = (s <> 0) xor (s + i = 0) (`snez` 0x87cc0, `seqz` / `xor` 0x87cdc-0x87ce0): s <> 0
     and, with no wrap, s + i <> 0, so t4 = 1.
   - 0x87ce8 `beqz a0` (s = 0): the premise 0 < k -> s <> 0 (the loop runs only when k > 0).
   - 0x87cec `bltu a6,a7` (a6 = ~out, a7 = i: out + i wraps), and after the loop or on the k = 0 path 0x87d68
     `bltu a6,a1` (out + k wraps): out + k + 1 <= frame_addr + fs_frame_bytes cid <= alloc_ceiling < 2 ^ 64, from
     sa_fframe and AR (lib/B/YCbq.v:587-589).
   Call sites (both in m_file, listing m_file.fuzz_segconf.asan-ubsan.s; segA/evidence/callsites.asan-ubsan.tsv lines
   105, 113), in m_key after the value [v, v + vn) has been stripped (the strip at 0x86664) and unquoted
   (0x86690-0x866d8):
   - 0x86738 (c:219, the role): a0 = ld 192(s1) = v (0x86728), a1 = s10 = 184(s1) - 192(s1) = vn (`sub` 0x86700),
     a2 = ld 144(s1) = low (0x86734), a3 = 64 (`li` 0x8672c).
   - 0x8686c (c:229, the model): a0 = ld 192(s1) = v (0x86858), a1 = s10 = vn, a2 = s4 = ld 144(s1) = low
     (0x86864-0x86868), a3 = 24 (`li` 0x8685c).
   Why each premise holds there (m_file 0x86140, frame 320, STK_m_file 8,592 at image B): cap = 64 or 24 >= 1. v and
   vn: [v, v + vn) lies in m_file's text block t (strip's post gives t <= v <= e' <= t + |text|; the unquote moves v
   up by one and e' down by one only when vn >= 2, `blt` 0x86678), so m_file_pre's sa_heap / sa_addr / sa_str of t
   (lib/B/Prog/m_file_c.v:218-219, image B's copy of the image-A owner's FINAL 6f783602b5e3) give l := the vn bytes, and
   for its first k bytes sa_bytes, sa_addr, sa_loc (its heap arm) and v <> 0 (t <> 0). low: 144(s1) = FB + 32
   (0x86308-0x86310, FB = 120(s1) the side-stack frame base), the 64-byte buffer low of m_file's class-1 side-stack
   frame (requested with a0 = 128 at 0x861b4; the shadow bytes (FB >> 3) + 0x7fff8000 + 4 .. + 11 of [FB + 32, FB + 96) are marked
   unusable at 0x8624c-0x86268 and usable at 0x866ec-0x86710, just before both calls); k + 1 <= cap <= 64, so
   [low, low + k + 1) lies in [FB + 32, FB + 96): sa_fframe (the frame (1, pos) in frames S, fs_frame_bytes 1 = 128)
   and range_addressable (shadow 0). AR's use-after-return cell is 1, so the real-stack fallback 0x861cc-0x861e4 is
   not taken and the frame arm is the only one m_file needs. The heap block and the side-stack frame are apart:
   sa_disj. No premise of m_file_c.v is added.
   image B: A_fold = 0x87c94 (twin .symtab); STK_fold = 16 (its frame; the error path is dead).
   IMAGE-INDEPENDENT: no image module is Required; A_fold and STK_fold are parameters, and the shadow-base cells are
   fields of B.
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

(* The folded text fold stores, without its NUL (U's lib/U/Prog/fold_c.v:38, the same body). *)
Definition fold_out (l : list byte) (cap : Z) : list Z := SegModel.h_fold (seg_spec.zs l) (Z.to_nat cap).

(* What fold reads and writes, through a reader rd (the U fold_pre, lib/U/Prog/fold_c.v:40-46, without its stack
   conjuncts), with k = length (fold_out l cap) = min(n, cap - 1) (fold_out_length below): cap >= 1; l has n bytes,
   of which the k fold reads are at s, addressable; s nonzero when k > 0; the k + 1 bytes at out addressable (the
   shadow half of sa_dst's frame arm); the k bytes at s apart from out's k + 1. *)
Definition fold_args (rd : reader) (s n out cap : Z) (l : list byte) : Prop :=
1 <= cap /\ Z.of_nat (length l) = n /\
(0 < Z.of_nat (length (fold_out l cap)) -> s <> 0) /\
sa_bytes rd s (firstn (length (fold_out l cap)) l) /\ sa_addr rd s (Z.of_nat (length (fold_out l cap))) /\
range_addressable rd SHADOW_OFF out (Z.of_nat (length (fold_out l cap)) + 1) /\
sa_disj s (Z.of_nat (length (fold_out l cap))) out (Z.of_nat (length (fold_out l cap)) + 1).

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Section d.
Variable B : asyms.
(* What fold asks of its caller over the reader rd = aview segs (w_H W) mem: fold_args, s's k bytes in a heap block,
   a side-stack frame or the image (sa_loc), out's k + 1 bytes inside a live side-stack frame (sa_fframe: with
   fold_args' range_addressable, sa_dst's frame arm). The U stack_ok / apart-from-[lo, sp) / mem_inv conjuncts are
   afn_pre's and the locations' here. Outside the sections: fold_pre segs B ly S W mem s n out cap l. *)
Definition fold_pre (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte)
(s n out cap : Z) (l : list byte) : Prop :=
fold_args (aview segs (w_H W) mem) s n out cap l /\
sa_loc segs B ly S s (Z.of_nat (length (fold_out l cap))) /\
sa_fframe ly S out (Z.of_nat (length (fold_out l cap)) + 1).
(* the events this call spends: 0, it reaches no allocator entry *)
Definition EV_fold : Z := 0.
Definition fold_contract (A_fold STK_fold : Z) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (s n out cap : Z) (l : list byte),
afn_pre segs B STK_fold ly S W regs mem md ch ->
getr regs 10 = w64 s -> 0 <= s < 2 ^ 64 -> getr regs 11 = w64 n -> 0 <= n < 2 ^ 64 ->
getr regs 12 = w64 out -> 0 <= out < 2 ^ 64 -> getr regs 13 = w64 cap -> 0 <= cap < 2 ^ 64 ->
fold_pre ly S W mem s n out cap l ->
st_nev S + EV_fold <= EV_MAX ->
SRr segs W (cfg_at segs A_fold regs mem md)
(apost_base segs B STK_fold [(out, out + Z.of_nat (length (fold_out l cap)) + 1)] regs ly S W mem md EV_fold
(fun ly' S' W' regs' mem' md' =>
 getr regs' 10 = w64 (Z.of_nat (length (fold_out l cap))) /\
 sa_bytes (aview segs (w_H W') mem') out (seg_spec.zb (fold_out l cap ++ [0])) /\
 sa_kept segs W mem W' mem' regs STK_fold (fun a => out <= a < out + Z.of_nat (length (fold_out l cap)) + 1) /\
 sa_noalloc B ly S ly' S')).
End d.
End c.
End b.

(* k = min(n, cap - 1): the bytes fold stores before its NUL (U's lib/U/Prog/fold.v:144-145 fo_Kmin, stated for any
   cap >= 1). *)
Lemma fold_out_length (l : list byte) (cap : Z) : 1 <= cap ->
  Z.of_nat (length (fold_out l cap)) = Z.min (Z.of_nat (length l)) (cap - 1).
Proof.
  intros Hc. unfold fold_out, SegModel.h_fold, seg_spec.zs.
  rewrite length_map, length_firstn, length_map. lia.
Qed.
