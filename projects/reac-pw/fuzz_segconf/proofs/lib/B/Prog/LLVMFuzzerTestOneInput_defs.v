(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the boundary states and segment statements of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86530), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (the CL_*_stmtX statements: from a point of the function to its return, under the entry's context) and A/ACf5.v (rtcx, rt_base: the entry's facts bundled once). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths, module names, addresses and numbers changed; 479 of its 533 lines of code are new or changed and 284 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan+UBSan image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3): the cut statements
   of the walk of the test harness's entry function LLVMFuzzerTestOneInput (0x84dc0, 1,248 instructions), and the
   statement of every segment lemma between them. Statement text only: no function of the binary is proved here.

   THE FORM: the image-B twin of lib/A/Prog/LLVMFuzzerTestOneInput_defs.v (image A's cut-statement commit
   6888a1bad128), with the same definition and lemma names, so that an image-A segment proof becomes an image-B
   one by renaming registers, slots and pcs; only the cut names carry image B's pcs. Image A's form is
   plugin-hostd/fuzz_command's lib/A/Prog/LLVMFuzzerTestOneInput_defs.v; its image-B twin there
   (lib/B/Prog/LLVMFuzzerTestOneInput_defs.v at origin/ossv/recipes 3abc3740de97) differs from its A file only in
   the registers, the frame slots and the LO_* offsets, as this file differs from image A's. The context record
   lcx, lt_base (the contract's premises word for word, so lt_adapter is exact), lt_post / lt_Q (its post word
   for word), and one LT_<cut>_stmt per cut: "from this point of the function to its return, under the entry's
   context", concluding SRr of lt_post at the FP state of the point; LTA_<cut> is the same at every FP state. The
   side-stack frame part is chain_words' (journal from the entry with own = [(3, x_fpos)]).
   The cuts and segments are the image-B map's PLAN-asanubsan-main.md (sha256 c4fad638c3a4) section 2.3
   (map/out/segments.tsv sha256 a8f1556c42b1) and section 9.1 (each image-A cut at its image-B pc; every LO_*
   below checked against the listing: the slot LO / 4 of SegList.seg_listing holds the instruction word the
   excerpt dis/LLVMFuzzerTestOneInput.fuzz_segconf.asan-ubsan.s (sha256 be3c0d79cc92) has at that pc, 22 of 22);
   the registers and s1 slots each cut states are the live sets of map/out/live.tsv (sha256 c633980a566d,
   section 6), each value checked against the excerpt's code; the frame's shadow states section 3.4; the model
   content is image A's (the image-B owner's plain lib/Prog/seg_cuts.v read through the ASan reader with SegABase's sa_
   forms). Register numbers: ra 1, sp 2, gp 3, tp 4, t0 5, s0 8, s1 9, a0-a7 10-17, s2-s11 18-27.

   NAMES (PLAN-asanubsan-main's): SP0 = x_sp0 the entry sp; S1 = x_s1 = (SP0 - 352) & ~31, the base register s1;
   FR = x_fr the side-stack frame of class 3 (frame_addr of x_fpos), FL = x_fl its flag byte; SH(a) the shadow
   byte of a, shadow_addr a = 0x7fff8000 + a / 8 (the code: (a >> 3) + the base read from the cell 0xac7b8, which
   the frame keeps at 200(s1)); c, m, t, tab, mt the blocks of the reader state, the model state, the file text
   and the two VLAN tables. Only the side-stack branch is stated (the flag cell is the record's constant 1 and the
   class-3 frame contract returns a frame): the real-stack fallback at 0x84e50 and its probe loop are dead. The
   early return (0x84f48, n >= 2 ^ 26) is refuted at ENTRY from lt_base's n < 2 ^ 26.

   WHAT DIFFERS FROM IMAGE A'S STATEMENTS, AND WHY (every item from the image-B code):
   - The frame: 352 bytes (`addi sp,sp,-352` at 0x84dc0), S1 = (SP0 - 352) & ~31. lt_frame keeps the shadow base
     at 200(s1) (the store `sd t0,200(s1)` at 0x84e28) and adds SH(FR) at 184(s1) as its last conjunct: image B
     keeps SH(FR) in that slot only (`sd a5,184(s1)` at 0x84f3c, read by 12 loads, the release's 0x85edc among
     them), where image A kept it in a register too; so no cut states a register = SH(FR).
   - Every s1 slot moves (map section 11, the A -> B slot map). Image B keeps returned in 176(s1) (image A in a
     register), f + 1 in s9 at K85338 (image A in a slot), and adds m + 0x10 (80), M & 3 (96), ~M (208), the
     take's end P1 + NP (144), NP (152) and N1 (160).
     The slot list of each cut is that cut's live set (out/live.tsv), not image A's one list LT_L for every cut
     of the file loop and the checks: image B overwrites 104, 112, 128 .. 160 in the refusal loop (S10) and 88,
     96, 120 in S13, so one list cannot hold from K85110 to K85994. LT_L (the file loop), LT_LH (the header slots),
     LT_LC (the checks and the tables), LT_LV and LT_LD (m_declared) and LT_LF (the frees) are those live sets.
   - The UBSan trap branches (map section 10, out/traps.tsv sha256 49b1208a6d43): 38 branches to the trap
     instruction 0x85ff8. Each is refuted by a fact a cut states or that follows from its premises:
     * pointer sums over a heap block do not wrap: lt_hblk's sa_addr gives a + n <= 2 ^ 63 for c, m, t, tab, mt
       (the journal's AR gives a + n <= alloc_ceiling as well, YG0d.AR_blocks_law, lib/B/YG0s.v:615); over the
       payload, lt_base's block (n > 0) with the entry's AR; over the frame, the journal's AR with FR in frames
       (YG0d.AR_frames_law);
     * alignment (traps 10, 11, 14 M & 3; 17 C & 7; 25 TAB & 1; 26, 35 MT & 3): lt_hblk's `a mod 16 = 0` (the
       allocator posts give 4096 <= res, the alignment comes from AR_blocks_law at the post state);
       lt_land_a16 turns it into the low-bit values. The values the code keeps for these tests are stated as
       their values: s5 = 96(s1) = M & 3 = 0 (K85110 .. K855c8), 160(s1) = ((MT & 3) = 0) = 1 (K85b0c, K85d04);
     * the complements the code keeps in slots for the later tests: 208(s1) = ~M (K85110 .. K85d04), 96(s1) =
       ~(FR + 32) and 152(s1) = ~MT (K85b0c, K85d04), as lt_not;
     * the index bounds (traps 12, 15, 22, 27: i < m->n <= 32; 20: i < n_kept <= 8; 32: pn < 16) are model facts
       of sa_mconf; trap 38 (added++ as a signed 32-bit add) needs added <= i, which K85b0c and K85d04 state.
   - Checks: image B has 34 instrumented checks, two fewer than image A: one load serves both arms of the role
     test in m_cross, and the store v.parent[pn] = 0 has none (traps 32 / 33 at 0x85ce4 / 0x85cf0 guard it). No
     cut statement changes for it.
   - Registers at each cut: out/live.tsv's (map section 11 lists A -> B); e.g. K85110 has a4 = 1 (UBSan's p + 1
     tests), s5 = M & 3 and s6 = m; K85b0c has a6 = SHB; K85d04 adds s8 = m.

   SATISFIABILITY, one reason per cut (no premise contradicts another; checked by reading):
   - ENTRY: lt_base is the contract's premises and sa_frm0 its frm clause (the contract's own pre, nothing more).
   - K84f4c: the journal with own = [(3, pos)] is what frame_alloc_3's post gives from frames S = []; the frame
     words, the 36 entry shadow bytes, 200(s1) and 184(s1) are the stores 0x84e28 and 0x84e94-0x84f40; k = 0, no
     block; a6 = a7 = FR (the side-stack branch: frame_alloc_3 returned FR <> 0).
   - K85068 / K8507c: one / two fresh blocks (malloc's and calloc's posts: 4096 <= res, appended; 16-aligned and
     below 2 ^ 63 by AR_blocks_law at the post state, addressable by AR_shadow_law); flags / cap / nfiles and
     24(s1) = FR are functions of the payload and FR, the stores 0x84f4c-0x85058.
   - K85110 f: f < nfiles <= 4 (lt_nfiles_range in _s02.v); c, m hold seg_run of the payload at f; M & 3 = 0
     for the 16-aligned m; the counters' bounds hold of seg_run (gen + 1 per turn, refused and overflow by at
     most a text's length plus 64 per turn).
   - K85210 f: as K85110 f with the fresh text block of n + 1 bytes, n = seg_txt_n <= 65535; 152 / 160 the
     stores 0x851f8 / 0x851d8.
   - K85338 f / K854d4 f: the last turn (f + 1 = nfiles); m holds m_file (resp. m_cross of it) of the turn's
     text, the text block its C string; the label usable (0x85254-0x85268); 128 / 136 / 144 the stores 0x85344 /
     0x8533c / 0x85324.
   - K85530 f: c, m hold seg_after f; the label still usable (released at 0x85538, after the cut).
   - K855c8 / K856f4 / K85868: c, m hold SegModel.run of the payload; the checks and queries write neither;
     176(s1) = SH(m + 0x2000) from 0x855e4 on.
   - K85984 / K85994: one / two fresh zeroed 16-aligned tables of 18 (cap + 1) and 20 (cap + 1) bytes (cap <= 39).
   - K85b0c i: i < m->n; tab holds vlan_init's entries and the guard, mt the model's table after seg[0 .. i)
     (m_decl_go over firstn i, which has not failed), n usable holding length tab; added <= i (at most one
     append per turn, 0 at i = 0); 160(s1) = 1 (both stores, 0x85a70 and 0x85a90's seqz of the 16-aligned mt).
   - K85d04 i: as K85b0c i, with seg[i] not ignored, m_split of its name Some (p, vid), v usable holding (p, vid).
   - K85e50: mt holds m_declared's table, 112(s1) its answer (-1 when the table filled up, 0x85ff0).
   - K85e9c .. K85eb4: the blocks freed newest first, n still usable (released at 0x85ebc).
   - K85ec8: no harness block, the entry shadow pattern (both arrivals: the normal exit and the refuted early
     return), a6 = a7 = FR.
   - RET: the journal with own = [] (the frame released by meta_fill_f5 and the flag store), the callee-saved
     registers restored, a0 = 0, the entry's blocks. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI00.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable SegSyms SegList SegPa SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import LLVMFuzzerTestOneInput_c SegInstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ===================================== the frame (PLAN-asanubsan-main section 3) ===================================== *)
(* the real frame (addi sp,sp,-352 at 0x84dc0) and the registers it saves at SP0 - 8, - 16, ..., - 104
   (0x84dc8 .. 0x84df8): ra, s0, s1, s2, ..., s11 *)
Definition LT_FRAME : Z := 352.
Definition LT_SAVED : list (bv 5) := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
(* the side-stack frame: class 3 (li a0,288; jal frame_alloc_3 at 0x84e30 / 0x84e34), its header words (0x84e94 ..
   0x84e9c: the magic, the description string 0x16fd5, this function 0x84dc0), the magic the release writes
   (0x85ed0), and the word at frame + 504 that holds the flag byte's address (ld a0,504(s2) at 0x85ee8) *)
Definition LT_FCLS : Z := 3.
Definition LT_HDR0 : Z := 0x41b58ab3.
Definition LT_HDR0_DONE : Z := 0x45e0360e.
Definition LT_FLAGW : Z := 504.
(* the frame's objects (the description `5 32 20 7 v.i:357 96 40 9 label:602 176 4 5 r:625 192 18 9 probe:640
   256 4 8 n181:655` at 0x16fd5, PLAN-asanubsan-main section 3.3: image A's offsets and sizes) *)
Definition FO_V : Z := 32.
Definition FO_VID : Z := 48.
Definition FO_LABEL : Z := 96.
Definition FO_R : Z := 176.
Definition FO_PROBE : Z := 192.
Definition FO_N : Z := 256.
(* m_split's byte-class mask kept at 144(s1) (0x85ae4 .. 0x85afc: '-', '.', ':', '_' as bits 0, 1, 13, 50) and the
   vid bound at 136(s1) (0x85ae8, 0x85b08) *)
Definition LT_MASK : Z := 0x4000000002003.
Definition LT_VIDMAX : Z := 4094.
(* the 64-bit word of `not a` for 0 <= a < 2 ^ 64: the complements the UBSan pointer-overflow tests compare
   against (~M at 208(s1), ~(FR + 32) at 96(s1), ~MT at 152(s1)) *)
Definition lt_not (a : Z) : Z := 2 ^ 64 - 1 - a.
(* a 16-aligned block's low bits: what refutes the alignment traps and gives the values M & 3 and (MT & 3) = 0 *)
Lemma lt_land_a16 : forall a, a mod 16 = 0 -> Z.land a 1 = 0 /\ Z.land a 3 = 0 /\ Z.land a 7 = 0.
Proof.
intros a H. apply (proj1 (Z.mod_divide a 16 ltac:(lia))) in H. destruct H as [q ->].
rewrite (Z.land_ones (q * 16) 1 ltac:(lia) : Z.land (q * 16) 1 = (q * 16) mod 2).
rewrite (Z.land_ones (q * 16) 2 ltac:(lia) : Z.land (q * 16) 3 = (q * 16) mod 4).
rewrite (Z.land_ones (q * 16) 3 ltac:(lia) : Z.land (q * 16) 7 = (q * 16) mod 8).
split; [|split].
- replace (q * 16) with ((q * 8) * 2) by ring. apply Z.mod_mul. lia.
- replace (q * 16) with ((q * 4) * 4) by ring. apply Z.mod_mul. lia.
- replace (q * 16) with ((q * 2) * 8) by ring. apply Z.mod_mul. lia.
Qed.

(* the state of each frame object's shadow: true = usable (its bytes 00 / partial), false = out of scope (0xf8) *)
Record lfo := mkLFO { fo_v : bool; fo_label : bool; fo_r : bool; fo_probe : bool; fo_n : bool }.
Definition LFO0 : lfo := mkLFO false false false false false.
Definition LFO_L : lfo := mkLFO false true false false false.
Definition LFO_N : lfo := mkLFO false false false false true.
Definition LFO_NV : lfo := mkLFO true false false false true.
(* the 36 shadow bytes SH(FR) + 0 .. 35 (PLAN-asanubsan-main section 3.4, the entry's stores 0x84ea8-0x84f40):
   the left guard f1 x 4, v (20 bytes: 00 00 04), f2 x 5, label (40 bytes: 00 x 5), f2 x 5, r (4 bytes: 04), f2,
   probe (18 bytes: 00 00 02), f2 x 5, n (4 bytes: 04), the right guard f3 x 3; each object 0xf8 when out of
   scope *)
Definition lt_fsh (o : lfo) : list Z :=
  [0xf1; 0xf1; 0xf1; 0xf1] ++ (if fo_v o then [0; 0; 4] else [0xf8; 0xf8; 0xf8]) ++ repeat 0xf2 5 ++
  (if fo_label o then repeat 0 5 else repeat 0xf8 5) ++ repeat 0xf2 5 ++
  (if fo_r o then [4] else [0xf8]) ++ [0xf2] ++ (if fo_probe o then [0; 0; 2] else [0xf8; 0xf8; 0xf8]) ++
  repeat 0xf2 5 ++ (if fo_n o then [4] else [0xf8]) ++ [0xf3; 0xf3; 0xf3].
Lemma lt_fsh_len : forall o, length (lt_fsh o) = 36%nat.
Proof. intros [[] [] [] [] []]; reflexivity. Qed.

(* ================================= the cut points (offsets from BASE = 0x84dc0) ================================= *)
Definition LO_K84f4c : Z := 0x18c.  (* after the frame set-up and the size test: `sd a6,24(s1)` *)
Definition LO_K85068 : Z := 0x2a8.  (* malloc(16616) returned: c *)
Definition LO_K8507c : Z := 0x2bc.  (* calloc(1, 9236) returned: m *)
Definition LO_K85110 : Z := 0x350.  (* the file loop's head, turn f *)
Definition LO_K85210 : Z := 0x450.  (* malloc(n + 1) returned: the text *)
Definition LO_K85338 : Z := 0x578.  (* the last turn's m_file(m, text, NULL) returned *)
Definition LO_K854d4 : Z := 0x714.  (* after m_cross, before reac_segconf_parse *)
Definition LO_K85530 : Z := 0x770.  (* free(text) returned *)
Definition LO_K855c8 : Z := 0x808.  (* after the file loop *)
Definition LO_K856f4 : Z := 0x934.  (* after the per-segment checks *)
Definition LO_K85868 : Z := 0xaa8.  (* after the refusal checks *)
Definition LO_K85984 : Z := 0xbc4.  (* calloc(cap + 1, 18) returned: tab *)
Definition LO_K85994 : Z := 0xbd4.  (* calloc(cap + 1, 20) returned: mt *)
Definition LO_K85b0c : Z := 0xd4c.  (* the head of the inlined m_declared loop, turn i *)
Definition LO_K85d04 : Z := 0xf44.  (* m_split succeeded, v built *)
Definition LO_K85e50 : Z := 0x1090. (* after m_declared *)
Definition LO_K85e9c : Z := 0x10dc. (* free(mt) returned *)
Definition LO_K85ea4 : Z := 0x10e4. (* free(tab) returned *)
Definition LO_K85eac : Z := 0x10ec. (* free(m) returned *)
Definition LO_K85eb4 : Z := 0x10f4. (* free(c) returned *)
Definition LO_K85ec8 : Z := 0x1108. (* the frame release, reached from the normal exit *)
Definition LO_RET : Z := 0x1208.    (* ret *)

(* the counters' bounds at turn f: gen goes up by one per turn and refused / overflow by less than 2 ^ 20 per
   turn (m_file: at most one per line, m_file_c.v:296-310; m_cross: one per segment; the reader alike, cross_check
   at most 64), so at most 4 turns keep every callee's room (m_file_pre, reader_pre, m_refuse_pre) *)
Definition lt_cnt (f : nat) (rc0 : SegModel.rconf) (mc0 : SegModel.mconf) : Prop :=
  SegModel.rc_gen rc0 <= Z.of_nat f /\ SegModel.rc_refused rc0 <= Z.of_nat f * 2 ^ 20 /\
  SegModel.rc_overflow rc0 <= Z.of_nat f * 2 ^ 20 /\
  SegModel.mc_gen mc0 <= Z.of_nat f /\ SegModel.mc_refused mc0 <= Z.of_nat f * 2 ^ 20 /\
  SegModel.mc_overflow mc0 <= Z.of_nat f * 2 ^ 20.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the entry's context: the state at BASE + AF_LLVMFuzzerTestOneInput and the driver's arguments, and the position
   of the class-3
   side-stack frame frame_alloc_3 hands back (x_fpos; any value before that call) *)
Record lcx := mkLCX {
  x_ly : alayout; x_S : astate; x_W : world SEGS; x_regs : bvmap 5 word; x_mem : word -> option byte; x_md : Model;
  x_ch : list (Z * Z * Z); x_p : Z; x_n : Z; x_pl : list byte; x_j : nat; x_fpos : Z }.
Definition lt_setpos (cx : lcx) (f : Z) : lcx :=
  mkLCX (x_ly cx) (x_S cx) (x_W cx) (x_regs cx) (x_mem cx) (x_md cx) (x_ch cx) (x_p cx) (x_n cx) (x_pl cx)
    (x_j cx) f.
Definition x_sp0 (cx : lcx) : Z := spZ (x_regs cx).
Definition x_s1 (cx : lcx) : Z := (x_sp0 cx - LT_FRAME) - (x_sp0 cx - LT_FRAME) mod 32.
Definition x_fr (cx : lcx) : Z := frame_addr (x_ly cx) LT_FCLS (x_fpos cx).
Definition x_fl (cx : lcx) : Z := flag_addr (x_ly cx) LT_FCLS (x_fpos cx).
Definition x_sh (cx : lcx) : Z := shadow_addr (x_fr cx).
Definition x_bl0 (B : asyms) (cx : lcx) : list (Z * Z) := ablocks B (x_ly cx) (x_S cx).
(* the payload's quantities (seg_spec over SegModel.decode of the input bytes) *)
Definition x_cap (cx : lcx) : Z := seg_spec.seg_cap (x_pl cx).
Definition x_flags (cx : lcx) : Z := seg_spec.seg_flags (x_pl cx).
Definition x_nf (cx : lcx) : Z := seg_spec.seg_nfiles (x_pl cx).
Definition x_cur (cx : lcx) (k : nat) : Z := seg_spec.seg_cur_at (x_pl cx) (x_p cx) k.
Definition x_curn (cx : lcx) (k : nat) : Z := seg_spec.seg_cur_n (x_pl cx) k.
Definition x_tn (cx : lcx) (f : nat) : Z := seg_spec.seg_txt_n (x_pl cx) f + 1.
(* turn f's take (image B keeps its three numbers apart): P1 the address of the bytes fuzz_take takes (the cursor
   after lb and the u16), NP = n' their count, N1 the bytes left after the turn's header *)
Definition x_at (cx : lcx) (f : nat) : Z := seg_spec.seg_turn_at (x_pl cx) (x_p cx) f.
Definition x_np (cx : lcx) (f : nat) : Z := seg_spec.seg_turn_np (x_pl cx) f.
Definition x_n1 (cx : lcx) (f : nat) : Z := Z.of_nat (length (seg_spec.seg_turn_tail (x_pl cx) f)).
(* the reader's state, the model's state and returned after f turns, after turn f, and after the whole run *)
Definition x_st (cx : lcx) (f : nat) : SegModel.rconf * SegModel.mconf * bool := seg_spec.seg_run (x_pl cx) f.
Definition x_af (cx : lcx) (f : nat) : SegModel.rconf * SegModel.mconf * bool := seg_spec.seg_after (x_pl cx) f.
Definition x_run (cx : lcx) : SegModel.rconf * SegModel.mconf * bool := SegModel.run (seg_spec.seg_pay (x_pl cx)).
Definition x_rcF (cx : lcx) : SegModel.rconf := seg_spec.seg_rc (x_run cx).
Definition x_mcF (cx : lcx) : SegModel.mconf := seg_spec.seg_mc (x_run cx).
(* the VLAN tables: their sizes (cap + 1 entries) and the entries the harness seeds (vlan_init) *)
Definition x_tabn (cx : lcx) : Z := seg_spec.RVLAN_SIZE * (x_cap cx + 1).
Definition x_mtn (cx : lcx) : Z := seg_spec.MVLAN_SIZE * (x_cap cx + 1).
Definition x_tab0 (cx : lcx) : list (list Z * Z) := seg_spec.seg_tab0 (x_pl cx).
(* the inlined m_declared after seg[0 .. i): (added, the table) *)
Definition x_decl (cx : lcx) (i : nat) : Z * list (list Z * Z) :=
  SegModel.m_decl_go (firstn i (SegModel.mc_seg (x_mcF cx))) (x_tab0 cx) (x_cap cx) 0.
Definition x_seg (cx : lcx) (i : nat) : SegModel.mseg := nth i (SegModel.mc_seg (x_mcF cx)) SegModel.mseg_d.

(* the s1 slots, each list the live set of out/live.tsv at its cuts (184 SH(FR) and 200 SHB are lt_frame's).
   K85068, K8507c: 24 FA0 = FR (0x84f4c), 32 flags (0x84fd0 / 0x84ff4 / 0x85008), 56 cap (0x84f98 / 0x84ff0),
   104 nfiles (0x84fdc / 0x85010 / 0x85058) *)
Definition LT_LH (cx : lcx) : list (Z * Z) := [(24, x_fr cx); (32, x_flags cx); (56, x_cap cx); (104, x_nf cx)].
(* K85110 .. K85530 (the file loop): LT_LH's and 16 FR (0x850b4), 40 cap (0x850c4, the byte of 56(s1)), 48 &n
   (0x850bc), 64 &v (0x85098), 72 m + 0x20 (0x850f4), 80 m + 0x10 (0x850ec), 88 &label (0x850a0), 96 M & 3 = 0
   (0x8510c, s5 = andi m,3 at 0x850dc), 112 &r (0x850a8), 120 &probe (0x850b0), 168 c (0x8507c), 192 m
   (0x85104), 208 ~M (0x850e4), 216 &m->n (0x850cc); 176 returned is each cut's own *)
Definition LT_L (cx : lcx) (c m : Z) : list (Z * Z) :=
  [(16, x_fr cx); (24, x_fr cx); (32, x_flags cx); (40, x_cap cx); (48, x_fr cx + FO_N); (56, x_cap cx);
   (64, x_fr cx + FO_V); (72, m + 0x20); (80, m + 0x10); (88, x_fr cx + FO_LABEL); (96, 0); (104, x_nf cx);
   (112, x_fr cx + FO_R); (120, x_fr cx + FO_PROBE); (168, c); (192, m); (208, lt_not m);
   (216, m + seg_spec.MC_N)].
(* K855c8 .. K85994 (the checks and the tables): the slots of LT_L the code still reads; 112, 120 and 176 are
   each cut's own *)
Definition LT_LC (cx : lcx) (c m : Z) : list (Z * Z) :=
  [(16, x_fr cx); (24, x_fr cx); (32, x_flags cx); (40, x_cap cx); (48, x_fr cx + FO_N); (56, x_cap cx);
   (64, x_fr cx + FO_V); (168, c); (192, m); (208, lt_not m); (216, m + seg_spec.MC_N)].
(* K85b0c, K85d04 (the m_declared loop): the slots of LT_LC the loop and the frees read *)
Definition LT_LV (cx : lcx) (c m : Z) : list (Z * Z) :=
  [(16, x_fr cx); (24, x_fr cx); (40, x_cap cx); (48, x_fr cx + FO_N); (64, x_fr cx + FO_V); (168, c);
   (192, m); (208, lt_not m); (216, m + seg_spec.MC_N)].
(* and the loop's own at turn i: 88 mt + 16 (0x85abc), 96 ~(FR + 32) (0x85ad0), 104 tab (0x85ab0), 112 added
   (0x85ac0, 0x85e08), 120 mt (0x85ab4), 128 mn (0x85a7c / 0x85a84, 0x85e04), 136 4094 (0x85b08), 144 the mask
   (0x85afc), 152 ~MT (0x85ad8), 160 (MT & 3) = 0 as 1 (0x85a70 / 0x85a90), 176 SH(m + 0x2000) (0x855e4) *)
Definition LT_LD (cx : lcx) (m tab mt : Z) (i : nat) : list (Z * Z) :=
  [(88, mt + 16); (96, lt_not (x_fr cx + FO_V)); (104, tab); (112, fst (x_decl cx i)); (120, mt);
   (128, Z.of_nat (length (snd (x_decl cx i)))); (136, LT_VIDMAX); (144, LT_MASK); (152, lt_not mt); (160, 1);
   (176, shadow_addr (m + seg_spec.MC_N))].
(* K85e9c .. K85eb4 (the frees): FR and FA0 for the release (0x85ec0 / 0x85ec4) *)
Definition LT_LF (cx : lcx) : list (Z * Z) := [(16, x_fr cx); (24, x_fr cx)].
Definition lt_slots (cx : lcx) (rd : reader) (L : list (Z * Z)) : Prop :=
  forall o v, In (o, v) L -> rdword rd (x_s1 cx + o) = Some v.
(* the registers the entry saved, in its frame *)
Definition lt_saved (cx : lcx) (rd : reader) : Prop :=
  forall i r, nth_error LT_SAVED i = Some r ->
  rdword rd (x_sp0 cx - 8 * Z.of_nat (Datatypes.S i)) = Some (bv_unsigned (getr (x_regs cx) r)).
(* the reader state and the model state of a point: c and m hold them *)
Definition lt_cm (rd : reader) (c m : Z) (st : SegModel.rconf * SegModel.mconf * bool) : Prop :=
  sa_rconf rd c (seg_spec.seg_rc st) /\ sa_mconf rd m (seg_spec.seg_mc st).

Section e.
Variable B : asyms.
Variable MT : ameter_ops.

(* LLVMFuzzerTestOneInput_contract's premises at image B's instance (lib/B/Prog/SegInstB.v), word for word
   and in its order, but the rounding-mode premise sa_frm0, which is about the FP state of the configuration and is
   each statement's second premise (the adapter in _s02.v packs them) *)
Definition lt_base (cx : lcx) : Prop :=
  let ly := x_ly cx in let S := x_S cx in let W := x_W cx in let regs := x_regs cx in let mem := x_mem cx in
  let md := x_md cx in let p := x_p cx in let n := x_n cx in let pl := x_pl cx in
  afn_pre SEGS B STK_LLVMFuzzerTestOneInput ly S W regs mem md (x_ch cx) /\
  astack_pres ly (w_H W) mem (spZ regs) /\
  arodata_okP SEGS RLO_A RHI_A B (rdW W mem) /\
  seg_himg SEGS B longlA mod40A catA wordsA rolesA gotwA guardA seg_litA_fz seg_litA_rc (rdW W mem) /\
  getr regs 10 = w64 p /\ getr regs 11 = w64 n /\
  ((n = 0 /\ p = emptyA) \/ (0 < n < 2 ^ 26 /\ In (p, n) (ablocks B ly S))) /\
  n = Z.of_nat (length pl) /\
  garr8 SEGS (mrestrict (w_H W) mem) p (map (fun b : byte => bv_unsigned b) pl) /\
  frames S = [] /\
  ltoi_GI longlA (x_j cx) (rdW W mem) /\
  st_nev S + EV_LTOI pl <= EV_MAX /\ blocks_bytes S + LIVE_LTOI <= LIVE_MAX /\
  mo_ok MT S (XM_LTOI MT pl).

(* the post-condition's own part, word for word the contract's *)
Definition lt_Q (cx : lcx) : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' W' regs' mem' md' =>
  getr regs' 10 = w64 0 /\
  Permutation (ablocks B ly' S') (ablocks B (x_ly cx) (x_S cx)) /\
  (forall i, 0 <= i < x_n cx -> rdW W' mem' (x_p cx + i) = rdW (x_W cx) (x_mem cx) (x_p cx + i)) /\
  ltoi_GI longlA (Datatypes.S (x_j cx)) (rdW W' mem') /\
  mo_le MT (x_S cx) S' (XM_LTOI MT (x_pl cx)) /\ blocks_bytes S' <= blocks_bytes (x_S cx) + LIVE_LTOI.
Definition lt_post (cx : lcx) : world SEGS -> config -> Prop :=
  apost_baseF SEGS B STK_LLVMFuzzerTestOneInput (ltoi_PG longlA) (x_regs cx) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx)
    (EV_LTOI (x_pl cx)) (lt_Q cx).

Lemma lt_base_setpos : forall cx f, lt_base (lt_setpos cx f) = lt_base cx.
Proof. reflexivity. Qed.
Lemma lt_post_setpos : forall cx f, lt_post (lt_setpos cx f) = lt_post cx.
Proof. reflexivity. Qed.

(* the frame part of every cut from K84f4c to K85ec8 (chain_words_d.v:141-155 with segconf's image-B slots):
   the journal from the entry with the class-3 frame as its own frame and footprint longl, sp = s1 = S1, gp and
   tp kept, s0 = SP0, the 13 saved registers, the frame's three header words and its flag-byte word, the shadow
   base at 200(s1), the 36 shadow bytes of the frame with each object as o says, and SH(FR) at 184(s1) *)
Definition lt_frame (cx : lcx) ly S (W : world SEGS) (regs : bvmap 5 word) mem md (k : Z) (o : lfo) : Prop :=
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx)
    [(LT_FCLS, x_fpos cx)] ly S W mem md k /\
  getr regs 2 = w64 (x_s1 cx) /\ getr regs 3 = getr (x_regs cx) 3 /\ getr regs 4 = getr (x_regs cx) 4 /\
  getr regs 8 = w64 (x_sp0 cx) /\ getr regs 9 = w64 (x_s1 cx) /\
  lt_saved cx (rdW W mem) /\
  rdword (rdW W mem) (x_fr cx) = Some LT_HDR0 /\
  rdword (rdW W mem) (x_fr cx + 8) = Some (@pa_val _ seg_listing PI (A_OBJ 2)) /\
  rdword (rdW W mem) (x_fr cx + 16) = Some (@pa_val _ seg_listing PI (A_OBJ 3)) /\
  rdword (rdW W mem) (x_fr cx + LT_FLAGW) = Some (x_fl cx) /\
  rdword (rdW W mem) (x_s1 cx + 200) = Some SHADOW_OFF /\
  sa_zs (rdW W mem) (x_sh cx) (lt_fsh o) /\
  rdword (rdW W mem) (x_s1 cx + 184) = Some (x_sh cx).
(* the image facts at the point: the read-only view, the contract's seg_himg (literals, table, m_key's words and
   roles, the stack-protector cells, longl) and longl[120] = 0, at the point's reader *)
Definition lt_img (cx : lcx) (rd : reader) : Prop :=
  arodata_okP SEGS RLO_A RHI_A B rd /\
  seg_himg SEGS B longlA mod40A catA wordsA rolesA gotwA guardA seg_litA_fz seg_litA_rc rd /\
  ltoi_GI longlA (x_j cx) rd.
(* the live blocks: the harness's own O (newest first) and the entry's *)
Definition lt_blocks (cx : lcx) ly S (O : list (Z * Z)) : Prop := Permutation (ablocks B ly S) (O ++ x_bl0 B cx).
(* a harness block: live, at or above 4096, 16-aligned (the alignment traps), addressable and below 2 ^ 63 (sa_addr:
   the pointer-overflow traps), established at the allocator's return *)
Definition lt_hblk ly S (rd : reader) (a n : Z) : Prop :=
  In (a, n) (ablocks B ly S) /\ 4096 <= a /\ a mod 16 = 0 /\ sa_addr rd a n.
(* the meter and the events: k spent (the journal's count), rem still to come, acc metered; every event is
   charged at most LT_U, XM_LTOI's unit *)
Definition LT_U : Z := mo_malloc MT 65536 + mo_free MT.
Definition lt_bud (cx : lcx) (S : astate) (k acc rem : Z) : Prop :=
  0 <= k /\ 0 <= rem /\ k + rem <= EV_LTOI (x_pl cx) /\
  mo_le MT (x_S cx) S acc /\ 0 <= acc /\ acc + rem * LT_U <= XM_LTOI MT (x_pl cx).
(* the part every cut from K84f4c to K85ec8 shares *)
Definition lt_core (cx : lcx) ly S (W : world SEGS) (regs : bvmap 5 word) mem md (k acc rem : Z) (o : lfo)
  (O : list (Z * Z)) : Prop :=
  lt_frame cx ly S W regs mem md k o /\ lt_img cx (rdW W mem) /\ lt_blocks cx ly S O /\ lt_bud cx S k acc rem.

(* ---------------- the cut statements: from a point to the return, under the entry's context ---------------- *)

(* 0x84dc0: the function *)
Definition LT_ENTRY_stmt : Prop :=
  forall cx, lt_base cx -> sa_frm0 ->
  SRr SEGS (x_W cx) (cfg_at SEGS (BASE + AF_LLVMFuzzerTestOneInput) (x_regs cx) (x_mem cx) (x_md cx)) (lt_post cx).

(* 0x84f4c: the frame taken (a6 = FA0 = FR, a7 = FR), its header and 36 shadow bytes written, SH(FR) at 184(s1),
   the size test passed; t0 = the shadow base, s4 = n, s8 = p; no block, no allocator event *)
Definition LT_K84f4c_stmt : Prop :=
  forall cx ly S W regs mem md acc,
  lt_base cx -> sa_frm0 ->
  lt_core cx ly S W regs mem md 0 acc (EV_LTOI (x_pl cx)) LFO0 [] ->
  getr regs 5 = w64 SHADOW_OFF -> getr regs 16 = w64 (x_fr cx) -> getr regs 17 = w64 (x_fr cx) ->
  getr regs 20 = w64 (x_n cx) -> getr regs 24 = w64 (x_p cx) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_K84f4c) regs mem md) (lt_post cx).

(* 0x85068: malloc(16616) returned c in a0; the three header bytes read: s3 = FR, s4 / s8 the cursor; 24(s1) FR,
   32(s1) flags, 56(s1) cap, 104(s1) nfiles *)
Definition LT_K85068_stmt : Prop :=
  forall cx ly S W regs mem md k acc (c : Z),
  lt_base cx -> sa_frm0 ->
  lt_core cx ly S W regs mem md k acc (7 + 2 * x_nf cx) LFO0 [(c, seg_spec.SEG_C_SIZE)] ->
  lt_hblk ly S (rdW W mem) c seg_spec.SEG_C_SIZE ->
  getr regs 10 = w64 c -> getr regs 19 = w64 (x_fr cx) -> getr regs 20 = w64 (x_curn cx 0) ->
  getr regs 24 = w64 (x_cur cx 0) ->
  lt_slots cx (rdW W mem) (LT_LH cx) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_K85068) regs mem md) (lt_post cx).

(* 0x8507c: calloc(1, 9236) returned m in a0, all zero; s2 = 0x2000, s5 = c *)
Definition LT_K8507c_stmt : Prop :=
  forall cx ly S W regs mem md k acc (c m : Z),
  lt_base cx -> sa_frm0 ->
  lt_core cx ly S W regs mem md k acc (6 + 2 * x_nf cx) LFO0 [(m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] ->
  lt_hblk ly S (rdW W mem) c seg_spec.SEG_C_SIZE -> lt_hblk ly S (rdW W mem) m seg_spec.SEG_M_SIZE ->
  zero_atA (rdW W mem) m seg_spec.SEG_M_SIZE ->
  getr regs 10 = w64 m -> getr regs 18 = w64 seg_spec.MC_N -> getr regs 19 = w64 (x_fr cx) ->
  getr regs 20 = w64 (x_curn cx 0) -> getr regs 21 = w64 c -> getr regs 24 = w64 (x_cur cx 0) ->
  lt_slots cx (rdW W mem) (LT_LH cx) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_K8507c) regs mem md) (lt_post cx).

(* 0x85110: the head of file turn f < nfiles: a4 = 1, s2 = nfiles, s4 / s8 the cursor after f records, s5 = M & 3
   = 0, s6 = m, s9 = f; 176(s1) returned; c and m hold the reader and model states after f turns (plain
   P_K138e8) *)
Definition LT_K85110_stmt (f : nat) : Prop :=
  forall cx ly S W regs mem md k acc (c m : Z),
  lt_base cx -> sa_frm0 -> Z.of_nat f < x_nf cx ->
  lt_core cx ly S W regs mem md k acc (6 + 2 * (x_nf cx - Z.of_nat f)) LFO0
    [(m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] ->
  lt_hblk ly S (rdW W mem) c seg_spec.SEG_C_SIZE -> lt_hblk ly S (rdW W mem) m seg_spec.SEG_M_SIZE ->
  getr regs 14 = w64 1 -> getr regs 18 = w64 (x_nf cx) -> getr regs 20 = w64 (x_curn cx f) ->
  getr regs 21 = w64 0 -> getr regs 22 = w64 m -> getr regs 24 = w64 (x_cur cx f) ->
  getr regs 25 = w64 (Z.of_nat f) ->
  lt_slots cx (rdW W mem) (LT_L cx c m ++ [(176, seg_spec.b2z (seg_spec.seg_ret (x_st cx f)))]) ->
  lt_cm (rdW W mem) c m (x_st cx f) ->
  lt_cnt f (seg_spec.seg_rc (x_st cx f)) (seg_spec.seg_mc (x_st cx f)) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_K85110) regs mem md) (lt_post cx).

(* 0x85210: malloc(n + 1) returned the text block t in a0 (plain P_K13984): s2 = nfiles, s3 = P1, s4 = n, s5 = 0,
   s6 = m, s8 = P1 + NP, s9 = f, s10 = lb; 152(s1) = NP, 160(s1) = N1 *)
Definition LT_K85210_stmt (f : nat) : Prop :=
  forall cx ly S W regs mem md k acc (c m t : Z),
  lt_base cx -> sa_frm0 -> Z.of_nat f < x_nf cx ->
  lt_core cx ly S W regs mem md k acc (5 + 2 * (x_nf cx - Z.of_nat f)) LFO0
    [(t, x_tn cx f); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] ->
  lt_hblk ly S (rdW W mem) c seg_spec.SEG_C_SIZE -> lt_hblk ly S (rdW W mem) m seg_spec.SEG_M_SIZE ->
  lt_hblk ly S (rdW W mem) t (x_tn cx f) ->
  getr regs 10 = w64 t -> getr regs 18 = w64 (x_nf cx) -> getr regs 19 = w64 (x_at cx f) ->
  getr regs 20 = w64 (seg_spec.seg_txt_n (x_pl cx) f) -> getr regs 21 = w64 0 -> getr regs 22 = w64 m ->
  getr regs 24 = w64 (x_at cx f + x_np cx f) -> getr regs 25 = w64 (Z.of_nat f) ->
  getr regs 26 = w64 (seg_spec.seg_lb (x_pl cx) f) ->
  lt_slots cx (rdW W mem) (LT_L cx c m ++
    [(152, x_np cx f); (160, x_n1 cx f); (176, seg_spec.b2z (seg_spec.seg_ret (x_st cx f)))]) ->
  lt_cm (rdW W mem) c m (x_st cx f) ->
  lt_cnt f (seg_spec.seg_rc (x_st cx f)) (seg_spec.seg_mc (x_st cx f)) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_K85210) regs mem md) (lt_post cx).

(* 0x85338: the last turn (f + 1 = nfiles), after m_file(m, text, NULL): s5 = 0, s7 = t, s9 = f + 1, s10 =
   (m + 0x2000) >> 3; 144(s1) P1 + NP, 152(s1) NP, 160(s1) N1, 176(s1) returned; the label usable; t holds the
   turn's text *)
Definition LT_K85338_stmt (f : nat) : Prop :=
  forall cx ly S W regs mem md k acc (c m t : Z),
  lt_base cx -> sa_frm0 -> Z.of_nat f + 1 = x_nf cx ->
  lt_core cx ly S W regs mem md k acc (5 + 2 * (x_nf cx - Z.of_nat f)) LFO_L
    [(t, x_tn cx f); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] ->
  lt_hblk ly S (rdW W mem) c seg_spec.SEG_C_SIZE -> lt_hblk ly S (rdW W mem) m seg_spec.SEG_M_SIZE ->
  lt_hblk ly S (rdW W mem) t (x_tn cx f) ->
  getr regs 21 = w64 0 -> getr regs 23 = w64 t -> getr regs 25 = w64 (Z.of_nat f + 1) ->
  getr regs 26 = w64 ((m + seg_spec.MC_N) / 8) ->
  lt_slots cx (rdW W mem) (LT_L cx c m ++
    [(144, x_at cx f + x_np cx f); (152, x_np cx f); (160, x_n1 cx f);
     (176, seg_spec.b2z (seg_spec.seg_ret (x_st cx f)))]) ->
  sa_rconf (rdW W mem) c (seg_spec.seg_rc (x_st cx f)) ->
  sa_mconf (rdW W mem) m (SegModel.m_file (seg_spec.seg_mc (x_st cx f)) (seg_spec.seg_txt (x_pl cx) f) None) ->
  sa_str (rdW W mem) t (seg_spec.seg_txt (x_pl cx) f) ->
  lt_cnt (Datatypes.S f) (seg_spec.seg_rc (x_st cx f))
    (SegModel.m_file (seg_spec.seg_mc (x_st cx f)) (seg_spec.seg_txt (x_pl cx) f) None) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_K85338) regs mem md) (lt_post cx).

(* 0x854d4: the last turn after m_cross: s2 = SH(m + 0x2000), s7 = t; 128(s1) = (m + 0x2000) >> 3, 136(s1) =
   f + 1; m holds m_cross of K85338's model *)
Definition LT_K854d4_stmt (f : nat) : Prop :=
  forall cx ly S W regs mem md k acc (c m t : Z),
  lt_base cx -> sa_frm0 -> Z.of_nat f + 1 = x_nf cx ->
  lt_core cx ly S W regs mem md k acc (5 + 2 * (x_nf cx - Z.of_nat f)) LFO_L
    [(t, x_tn cx f); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] ->
  lt_hblk ly S (rdW W mem) c seg_spec.SEG_C_SIZE -> lt_hblk ly S (rdW W mem) m seg_spec.SEG_M_SIZE ->
  lt_hblk ly S (rdW W mem) t (x_tn cx f) ->
  getr regs 18 = w64 (shadow_addr (m + seg_spec.MC_N)) -> getr regs 23 = w64 t ->
  lt_slots cx (rdW W mem) (LT_L cx c m ++
    [(128, (m + seg_spec.MC_N) / 8); (136, Z.of_nat f + 1); (144, x_at cx f + x_np cx f); (152, x_np cx f);
     (160, x_n1 cx f); (176, seg_spec.b2z (seg_spec.seg_ret (x_st cx f)))]) ->
  sa_rconf (rdW W mem) c (seg_spec.seg_rc (x_st cx f)) ->
  sa_mconf (rdW W mem) m
    (SegModel.m_cross (SegModel.m_file (seg_spec.seg_mc (x_st cx f)) (seg_spec.seg_txt (x_pl cx) f) None)) ->
  sa_str (rdW W mem) t (seg_spec.seg_txt (x_pl cx) f) ->
  lt_cnt (Datatypes.S f) (seg_spec.seg_rc (x_st cx f))
    (SegModel.m_cross (SegModel.m_file (seg_spec.seg_mc (x_st cx f)) (seg_spec.seg_txt (x_pl cx) f) None)) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_K854d4) regs mem md) (lt_post cx).

(* 0x85530: turn f done, free(text) returned (plain P_K13ad8): s2 = nfiles, s4 / s8 the cursor after f + 1
   records, s5 = 0, s6 = m, s9 = f + 1, s10 = (m + 0x2000) >> 3; 176(s1) returned; the label still usable
   (released after the cut, 0x85538); c and m hold seg_after f *)
Definition LT_K85530_stmt (f : nat) : Prop :=
  forall cx ly S W regs mem md k acc (c m : Z),
  lt_base cx -> sa_frm0 -> Z.of_nat f < x_nf cx ->
  lt_core cx ly S W regs mem md k acc (6 + 2 * (x_nf cx - Z.of_nat (Datatypes.S f))) LFO_L
    [(m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] ->
  lt_hblk ly S (rdW W mem) c seg_spec.SEG_C_SIZE -> lt_hblk ly S (rdW W mem) m seg_spec.SEG_M_SIZE ->
  getr regs 18 = w64 (x_nf cx) -> getr regs 20 = w64 (x_curn cx (Datatypes.S f)) -> getr regs 21 = w64 0 ->
  getr regs 22 = w64 m -> getr regs 24 = w64 (x_cur cx (Datatypes.S f)) ->
  getr regs 25 = w64 (Z.of_nat (Datatypes.S f)) -> getr regs 26 = w64 ((m + seg_spec.MC_N) / 8) ->
  lt_slots cx (rdW W mem) (LT_L cx c m ++ [(176, seg_spec.b2z (seg_spec.seg_ret (x_af cx f)))]) ->
  lt_cm (rdW W mem) c m (x_af cx f) ->
  lt_cnt (Datatypes.S f) (seg_spec.seg_rc (x_af cx f)) (seg_spec.seg_mc (x_af cx f)) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_K85530) regs mem md) (lt_post cx).

(* 0x855c8: after the file loop (plain P_K13ae0): s5 = 0, s6 = m, s10 = (m + 0x2000) >> 3; 112(s1) &r, 120(s1)
   &probe, 176(s1) returned; c and m hold SegModel.run of the payload *)
Definition LT_K855c8_stmt : Prop :=
  forall cx ly S W regs mem md k acc (c m : Z),
  lt_base cx -> sa_frm0 ->
  lt_core cx ly S W regs mem md k acc 6 LFO0 [(m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] ->
  lt_hblk ly S (rdW W mem) c seg_spec.SEG_C_SIZE -> lt_hblk ly S (rdW W mem) m seg_spec.SEG_M_SIZE ->
  getr regs 21 = w64 0 -> getr regs 22 = w64 m -> getr regs 26 = w64 ((m + seg_spec.MC_N) / 8) ->
  lt_slots cx (rdW W mem) (LT_LC cx c m ++
    [(112, x_fr cx + FO_R); (120, x_fr cx + FO_PROBE); (176, seg_spec.b2z (seg_spec.seg_ret (x_run cx)))]) ->
  lt_cm (rdW W mem) c m (x_run cx) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_K855c8) regs mem md) (lt_post cx).

(* 0x856f4: after check_segments and the per-segment checks: 120(s1) &probe, 176(s1) = SH(m + 0x2000) *)
Definition LT_K856f4_stmt : Prop :=
  forall cx ly S W regs mem md k acc (c m : Z),
  lt_base cx -> sa_frm0 ->
  lt_core cx ly S W regs mem md k acc 6 LFO0 [(m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] ->
  lt_hblk ly S (rdW W mem) c seg_spec.SEG_C_SIZE -> lt_hblk ly S (rdW W mem) m seg_spec.SEG_M_SIZE ->
  lt_slots cx (rdW W mem) (LT_LC cx c m ++
    [(120, x_fr cx + FO_PROBE); (176, shadow_addr (m + seg_spec.MC_N))]) ->
  lt_cm (rdW W mem) c m (x_run cx) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_K856f4) regs mem md) (lt_post cx).

(* 0x85868: after check_refusals and the refusal checks: as K856f4 *)
Definition LT_K85868_stmt : Prop :=
  forall cx ly S W regs mem md k acc (c m : Z),
  lt_base cx -> sa_frm0 ->
  lt_core cx ly S W regs mem md k acc 6 LFO0 [(m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] ->
  lt_hblk ly S (rdW W mem) c seg_spec.SEG_C_SIZE -> lt_hblk ly S (rdW W mem) m seg_spec.SEG_M_SIZE ->
  lt_slots cx (rdW W mem) (LT_LC cx c m ++
    [(120, x_fr cx + FO_PROBE); (176, shadow_addr (m + seg_spec.MC_N))]) ->
  lt_cm (rdW W mem) c m (x_run cx) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_K85868) regs mem md) (lt_post cx).

(* 0x85984: calloc(cap + 1, 18) returned tab in a0, all zero: s3 = cap + 1; 176(s1) = SH(m + 0x2000) *)
Definition LT_K85984_stmt : Prop :=
  forall cx ly S W regs mem md k acc (c m tab : Z),
  lt_base cx -> sa_frm0 ->
  lt_core cx ly S W regs mem md k acc 5 LFO0
    [(tab, x_tabn cx); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] ->
  lt_hblk ly S (rdW W mem) c seg_spec.SEG_C_SIZE -> lt_hblk ly S (rdW W mem) m seg_spec.SEG_M_SIZE ->
  lt_hblk ly S (rdW W mem) tab (x_tabn cx) -> zero_atA (rdW W mem) tab (x_tabn cx) ->
  getr regs 10 = w64 tab -> getr regs 19 = w64 (x_cap cx + 1) ->
  lt_slots cx (rdW W mem) (LT_LC cx c m ++ [(176, shadow_addr (m + seg_spec.MC_N))]) ->
  lt_cm (rdW W mem) c m (x_run cx) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_K85984) regs mem md) (lt_post cx).

(* 0x85994: calloc(cap + 1, 20) returned mt in a0, all zero (plain P_K13cac): s2 = tab *)
Definition LT_K85994_stmt : Prop :=
  forall cx ly S W regs mem md k acc (c m tab mt : Z),
  lt_base cx -> sa_frm0 ->
  lt_core cx ly S W regs mem md k acc 4 LFO0
    [(mt, x_mtn cx); (tab, x_tabn cx); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] ->
  lt_hblk ly S (rdW W mem) c seg_spec.SEG_C_SIZE -> lt_hblk ly S (rdW W mem) m seg_spec.SEG_M_SIZE ->
  lt_hblk ly S (rdW W mem) tab (x_tabn cx) -> lt_hblk ly S (rdW W mem) mt (x_mtn cx) ->
  zero_atA (rdW W mem) tab (x_tabn cx) -> zero_atA (rdW W mem) mt (x_mtn cx) ->
  getr regs 10 = w64 mt -> getr regs 18 = w64 tab ->
  lt_slots cx (rdW W mem) (LT_LC cx c m ++ [(176, shadow_addr (m + seg_spec.MC_N))]) ->
  lt_cm (rdW W mem) c m (x_run cx) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_K85994) regs mem md) (lt_post cx).

(* the tables at the m_declared loop: tab holds vlan_init's entries and the guard tab[cap] (0x859c0, 0x85a08,
   0x85a2c), n (frame + 256, usable) the count, mt the model's table after seg[0 .. i), 128(s1) its length mn,
   112(s1) the entries added *)
Definition lt_tabs (cx : lcx) (rd : reader) (tab mt : Z) (t : list (list Z * Z)) : Prop :=
  Z.of_nat (length (x_tab0 cx)) <= x_cap cx < 40 /\
  sa_rtab rd tab (x_tab0 cx) /\ sa_guardtab rd tab (x_cap cx) /\
  sa_val rd (x_fr cx + FO_N) 4 (Z.of_nat (length (x_tab0 cx))) /\
  sa_mtab rd mt t /\ Z.of_nat (length t) <= x_cap cx.

(* 0x85b0c: the head of m_declared's turn i < m->n: a6 = the shadow base, s4 = i, s6 = s11 = &m->seg[i], s10 =
   -&m->seg[i]; the loop's slots LT_LD; added <= i (trap 0x85df8); n usable, v out of scope *)
Definition LT_K85b0c_stmt (i : nat) : Prop :=
  forall cx ly S W regs mem md k acc (c m tab mt : Z),
  lt_base cx -> sa_frm0 -> (i < length (SegModel.mc_seg (x_mcF cx)))%nat ->
  lt_core cx ly S W regs mem md k acc 4 LFO_N
    [(mt, x_mtn cx); (tab, x_tabn cx); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] ->
  lt_hblk ly S (rdW W mem) c seg_spec.SEG_C_SIZE -> lt_hblk ly S (rdW W mem) m seg_spec.SEG_M_SIZE ->
  lt_hblk ly S (rdW W mem) tab (x_tabn cx) -> lt_hblk ly S (rdW W mem) mt (x_mtn cx) ->
  getr regs 16 = w64 SHADOW_OFF -> getr regs 20 = w64 (Z.of_nat i) ->
  getr regs 22 = w64 (seg_spec.mseg_addr m i) -> getr regs 26 = w64 (- seg_spec.mseg_addr m i) ->
  getr regs 27 = w64 (seg_spec.mseg_addr m i) ->
  0 <= fst (x_decl cx i) <= Z.of_nat i ->
  lt_slots cx (rdW W mem) (LT_LV cx c m ++ LT_LD cx m tab mt i) ->
  lt_cm (rdW W mem) c m (x_run cx) ->
  lt_tabs cx (rdW W mem) tab mt (snd (x_decl cx i)) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_K85b0c) regs mem md) (lt_post cx).

(* 0x85d04: turn i, seg[i] not ignored and m_split of its name gave (p, vid): v = frame + 32 usable, holding p
   and its NUL (memcpy 0x85cdc, sb 0x85cfc) and vid at frame + 48 (sw 0x85d00); s5 = vid, s8 = m *)
Definition LT_K85d04_stmt (i : nat) : Prop :=
  forall cx ly S W regs mem md k acc (c m tab mt : Z) (par : list Z) (vid : Z),
  lt_base cx -> sa_frm0 -> (i < length (SegModel.mc_seg (x_mcF cx)))%nat ->
  lt_core cx ly S W regs mem md k acc 4 LFO_NV
    [(mt, x_mtn cx); (tab, x_tabn cx); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] ->
  lt_hblk ly S (rdW W mem) c seg_spec.SEG_C_SIZE -> lt_hblk ly S (rdW W mem) m seg_spec.SEG_M_SIZE ->
  lt_hblk ly S (rdW W mem) tab (x_tabn cx) -> lt_hblk ly S (rdW W mem) mt (x_mtn cx) ->
  SegModel.ms_ignore (x_seg cx i) = false ->
  SegModel.m_split (SegModel.ms_name (x_seg cx i)) = Some (par, vid) ->
  getr regs 16 = w64 SHADOW_OFF -> getr regs 20 = w64 (Z.of_nat i) -> getr regs 21 = w64 vid ->
  getr regs 22 = w64 (seg_spec.mseg_addr m i) -> getr regs 24 = w64 m ->
  getr regs 26 = w64 (- seg_spec.mseg_addr m i) -> getr regs 27 = w64 (seg_spec.mseg_addr m i) ->
  0 <= fst (x_decl cx i) <= Z.of_nat i ->
  lt_slots cx (rdW W mem) (LT_LV cx c m ++ LT_LD cx m tab mt i) ->
  lt_cm (rdW W mem) c m (x_run cx) ->
  lt_tabs cx (rdW W mem) tab mt (snd (x_decl cx i)) ->
  sa_strz (rdW W mem) (x_fr cx + FO_V) par -> sa_val (rdW W mem) (x_fr cx + FO_VID) 4 vid ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_K85d04) regs mem md) (lt_post cx).

(* 0x85e50: after m_declared: s8 = m; 104(s1) tab, 112(s1) the answer (want; -1 as its 64-bit word when the table
   filled up), 120(s1) mt, 128(s1) mn; mt holds m_declared's table *)
Definition LT_K85e50_stmt : Prop :=
  forall cx ly S W regs mem md k acc (c m tab mt : Z),
  lt_base cx -> sa_frm0 ->
  lt_core cx ly S W regs mem md k acc 4 LFO_N
    [(mt, x_mtn cx); (tab, x_tabn cx); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] ->
  lt_hblk ly S (rdW W mem) c seg_spec.SEG_C_SIZE -> lt_hblk ly S (rdW W mem) m seg_spec.SEG_M_SIZE ->
  lt_hblk ly S (rdW W mem) tab (x_tabn cx) -> lt_hblk ly S (rdW W mem) mt (x_mtn cx) ->
  getr regs 24 = w64 m ->
  lt_slots cx (rdW W mem)
    [(16, x_fr cx); (24, x_fr cx); (40, x_cap cx); (48, x_fr cx + FO_N); (104, tab);
     (112, fst (SegModel.m_declared (x_mcF cx) (x_tab0 cx) (x_cap cx)) mod 2 ^ 64); (120, mt);
     (128, Z.of_nat (length (snd (SegModel.m_declared (x_mcF cx) (x_tab0 cx) (x_cap cx))))); (168, c)] ->
  lt_cm (rdW W mem) c m (x_run cx) ->
  lt_tabs cx (rdW W mem) tab mt (snd (SegModel.m_declared (x_mcF cx) (x_tab0 cx) (x_cap cx))) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_K85e50) regs mem md) (lt_post cx).

(* 0x85e9c: free(mt) returned (plain P_K13f40 after the first free): s2 = c, s5 = tab, s8 = m *)
Definition LT_K85e9c_stmt : Prop :=
  forall cx ly S W regs mem md k acc (c m tab : Z),
  lt_base cx -> sa_frm0 ->
  lt_core cx ly S W regs mem md k acc 3 LFO_N [(tab, x_tabn cx); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] ->
  lt_hblk ly S (rdW W mem) c seg_spec.SEG_C_SIZE -> lt_hblk ly S (rdW W mem) m seg_spec.SEG_M_SIZE ->
  lt_hblk ly S (rdW W mem) tab (x_tabn cx) ->
  getr regs 18 = w64 c -> getr regs 21 = w64 tab -> getr regs 24 = w64 m ->
  lt_slots cx (rdW W mem) (LT_LF cx) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_K85e9c) regs mem md) (lt_post cx).

(* 0x85ea4: free(tab) returned: s2 = c, s8 = m *)
Definition LT_K85ea4_stmt : Prop :=
  forall cx ly S W regs mem md k acc (c m : Z),
  lt_base cx -> sa_frm0 ->
  lt_core cx ly S W regs mem md k acc 2 LFO_N [(m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] ->
  lt_hblk ly S (rdW W mem) c seg_spec.SEG_C_SIZE -> lt_hblk ly S (rdW W mem) m seg_spec.SEG_M_SIZE ->
  getr regs 18 = w64 c -> getr regs 24 = w64 m ->
  lt_slots cx (rdW W mem) (LT_LF cx) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_K85ea4) regs mem md) (lt_post cx).

(* 0x85eac: free(m) returned: s2 = c *)
Definition LT_K85eac_stmt : Prop :=
  forall cx ly S W regs mem md k acc (c : Z),
  lt_base cx -> sa_frm0 ->
  lt_core cx ly S W regs mem md k acc 1 LFO_N [(c, seg_spec.SEG_C_SIZE)] ->
  lt_hblk ly S (rdW W mem) c seg_spec.SEG_C_SIZE ->
  getr regs 18 = w64 c ->
  lt_slots cx (rdW W mem) (LT_LF cx) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_K85eac) regs mem md) (lt_post cx).

(* 0x85eb4: free(c) returned: no harness block, every event spent; n still usable *)
Definition LT_K85eb4_stmt : Prop :=
  forall cx ly S W regs mem md k acc,
  lt_base cx -> sa_frm0 ->
  lt_core cx ly S W regs mem md k acc 0 LFO_N [] ->
  lt_slots cx (rdW W mem) (LT_LF cx) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_K85eb4) regs mem md) (lt_post cx).

(* 0x85ec8: the release, with a6 = a7 = FR (SH(FR) is lt_frame's 184(s1)); the frame's shadow the entry pattern *)
Definition LT_K85ec8_stmt : Prop :=
  forall cx ly S W regs mem md k acc,
  lt_base cx -> sa_frm0 ->
  lt_core cx ly S W regs mem md k acc 0 LFO0 [] ->
  getr regs 16 = w64 (x_fr cx) -> getr regs 17 = w64 (x_fr cx) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_K85ec8) regs mem md) (lt_post cx).

(* 0x85fc8: the ret: the frame released (the journal's own frames []), the callee-saved registers and ra as at
   the entry, a0 = 0, the entry's blocks *)
Definition LT_RET_stmt : Prop :=
  forall cx ly S W regs mem md k acc,
  lt_base cx -> sa_frm0 ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx)
    [] ly S W mem md k ->
  aregs_preserved (x_regs cx) regs -> getr regs 1 = getr (x_regs cx) 1 -> getr regs 10 = w64 0 ->
  lt_img cx (rdW W mem) -> lt_blocks cx ly S [] -> lt_bud cx S k acc 0 ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_RET) regs mem md) (lt_post cx).

End e.
End f.
End d.

(* the cut statements at every FP state: a segment lemma takes its continuations in this form and concludes its
   own statement at the FP state of its start (a callee that reaches printf returns at an FP state of its own,
   apost_baseF) *)
Section lta. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
Definition LTA_ENTRY (B : asyms) (MT : ameter_ops) : Prop := forall fx1 : YK11.FPState, LT_ENTRY_stmt (fx := fx1) B MT.
Definition LTA_K84f4c (B : asyms) (MT : ameter_ops) : Prop := forall fx1 : YK11.FPState, LT_K84f4c_stmt (fx := fx1) B MT.
Definition LTA_K85068 (B : asyms) (MT : ameter_ops) : Prop := forall fx1 : YK11.FPState, LT_K85068_stmt (fx := fx1) B MT.
Definition LTA_K8507c (B : asyms) (MT : ameter_ops) : Prop := forall fx1 : YK11.FPState, LT_K8507c_stmt (fx := fx1) B MT.
Definition LTA_K85110 (B : asyms) (MT : ameter_ops) (f : nat) : Prop :=
  forall fx1 : YK11.FPState, LT_K85110_stmt (fx := fx1) B MT f.
Definition LTA_K85210 (B : asyms) (MT : ameter_ops) (f : nat) : Prop :=
  forall fx1 : YK11.FPState, LT_K85210_stmt (fx := fx1) B MT f.
Definition LTA_K85338 (B : asyms) (MT : ameter_ops) (f : nat) : Prop :=
  forall fx1 : YK11.FPState, LT_K85338_stmt (fx := fx1) B MT f.
Definition LTA_K854d4 (B : asyms) (MT : ameter_ops) (f : nat) : Prop :=
  forall fx1 : YK11.FPState, LT_K854d4_stmt (fx := fx1) B MT f.
Definition LTA_K85530 (B : asyms) (MT : ameter_ops) (f : nat) : Prop :=
  forall fx1 : YK11.FPState, LT_K85530_stmt (fx := fx1) B MT f.
Definition LTA_K855c8 (B : asyms) (MT : ameter_ops) : Prop := forall fx1 : YK11.FPState, LT_K855c8_stmt (fx := fx1) B MT.
Definition LTA_K856f4 (B : asyms) (MT : ameter_ops) : Prop := forall fx1 : YK11.FPState, LT_K856f4_stmt (fx := fx1) B MT.
Definition LTA_K85868 (B : asyms) (MT : ameter_ops) : Prop := forall fx1 : YK11.FPState, LT_K85868_stmt (fx := fx1) B MT.
Definition LTA_K85984 (B : asyms) (MT : ameter_ops) : Prop := forall fx1 : YK11.FPState, LT_K85984_stmt (fx := fx1) B MT.
Definition LTA_K85994 (B : asyms) (MT : ameter_ops) : Prop := forall fx1 : YK11.FPState, LT_K85994_stmt (fx := fx1) B MT.
Definition LTA_K85b0c (B : asyms) (MT : ameter_ops) (i : nat) : Prop :=
  forall fx1 : YK11.FPState, LT_K85b0c_stmt (fx := fx1) B MT i.
Definition LTA_K85d04 (B : asyms) (MT : ameter_ops) (i : nat) : Prop :=
  forall fx1 : YK11.FPState, LT_K85d04_stmt (fx := fx1) B MT i.
Definition LTA_K85e50 (B : asyms) (MT : ameter_ops) : Prop := forall fx1 : YK11.FPState, LT_K85e50_stmt (fx := fx1) B MT.
Definition LTA_K85e9c (B : asyms) (MT : ameter_ops) : Prop := forall fx1 : YK11.FPState, LT_K85e9c_stmt (fx := fx1) B MT.
Definition LTA_K85ea4 (B : asyms) (MT : ameter_ops) : Prop := forall fx1 : YK11.FPState, LT_K85ea4_stmt (fx := fx1) B MT.
Definition LTA_K85eac (B : asyms) (MT : ameter_ops) : Prop := forall fx1 : YK11.FPState, LT_K85eac_stmt (fx := fx1) B MT.
Definition LTA_K85eb4 (B : asyms) (MT : ameter_ops) : Prop := forall fx1 : YK11.FPState, LT_K85eb4_stmt (fx := fx1) B MT.
Definition LTA_K85ec8 (B : asyms) (MT : ameter_ops) : Prop := forall fx1 : YK11.FPState, LT_K85ec8_stmt (fx := fx1) B MT.
Definition LTA_RET (B : asyms) (MT : ameter_ops) : Prop := forall fx1 : YK11.FPState, LT_RET_stmt (fx := fx1) B MT.
End lta.

(* ---- the segment statements (PLAN-asanubsan-main section 2.3, the same segment numbers as image A for the same
   source spans): each segment file of the walk proves one of these, with the callee contracts, the runtime entries
   and the walk hypotheses as Section hypotheses of its own file; the continuation at every FP state, the conclusion
   at the FP state of the segment's start ---- *)
Section st. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
Variable B : asyms.
Variable MT : ameter_ops.
(* S00 0x84dc0 .. 0x84f48: the prologue, the cells, frame_alloc_3(288), the header and the 36 shadow bytes, SH(FR)
   to 184(s1), the size test (its taken edge to 0x85ec8 refuted by n < 2 ^ 26; the real-stack fallback dead) *)
Definition lt_seg_S00_stmt : Prop := LTA_K84f4c B MT -> LT_ENTRY_stmt B MT.
(* S01 0x84f4c .. 0x85064: the three header bytes (checks 1-3, traps 0x84f60 0x84fac 0x85028) and malloc(16616) *)
Definition lt_seg_S01_stmt : Prop := LTA_K85068 B MT -> LT_K84f4c_stmt B MT.
(* S02 0x85068 .. 0x85078: calloc(1, 9236) *)
Definition lt_seg_S02_stmt : Prop := LTA_K8507c B MT -> LT_K85068_stmt B MT.
(* S03 0x8507c .. 0x8510c: the NULL tests of c and m (refuted), the slots, reac_segconf_init(c), to turn 0 *)
Definition lt_seg_S03_stmt : Prop := LTA_K85110 B MT 0 -> LT_K8507c_stmt B MT.
(* S04 0x85110 .. 0x8520c: lb, the u16, the take (checks 4-6, traps 0x8511c .. 0x851d4), memchr, malloc(n + 1) *)
Definition lt_seg_S04_stmt : Prop := forall f, LTA_K85210 B MT f -> LT_K85110_stmt B MT f.
(* S05 0x85210 .. 0x85334 and 0x85520 .. 0x8552c: the NULL test (refuted), memcpy, the NUL (check 7, trap
   0x85230), the label (snprintf or memset of longl), and either m_file / parse_file (check 8, trap 0x852e8) /
   free(text) to K85530 f, or, on the last turn, m_file(m, text, NULL) to K85338 f *)
Definition lt_seg_S05_stmt : Prop := forall f, LTA_K85338 B MT f -> LTA_K85530 B MT f -> LT_K85210_stmt B MT f.
(* S06 0x85338 .. 0x854d0: the inlined m_cross loop with its m_refuse calls (checks 9-16, traps 0x85338 0x85374
   0x8537c) *)
Definition lt_seg_S06_stmt : Prop := forall f, LTA_K854d4 B MT f -> LT_K85338_stmt B MT f.
(* S07 0x854d4 .. 0x8552c: reac_segconf_parse (check 17), returned, free(text) *)
Definition lt_seg_S07_stmt : Prop := forall f, LTA_K85530 B MT f -> LT_K854d4_stmt B MT f.
(* S08 0x85530 .. 0x85554: the label out of scope and the latch, to the next turn or out of the loop *)
Definition lt_seg_S08_stmt : Prop :=
  forall f, LTA_K85110 B MT (Datatypes.S f) -> LTA_K855c8 B MT -> LT_K85530_stmt B MT f.
(* S09 0x855c8 .. 0x856f0: check_segments and the per-segment loop of nine calls (checks 18, 19, traps 0x855dc
   0x85630 0x85638) *)
Definition lt_seg_S09_stmt : Prop := LTA_K856f4 B MT -> LT_K855c8_stmt B MT.
(* S10 0x856f4 .. 0x85864: check_refusals and the refusal loop (checks 20-23, traps 0x857ac .. 0x857f0) *)
Definition lt_seg_S10_stmt : Prop := LTA_K85868 B MT -> LT_K856f4_stmt B MT.
(* S11 0x85868 .. 0x85980: the probe loop, the "nosuch0" pair (checks 24, 25, traps 0x858c0 0x858c8),
   calloc(cap + 1, 18) *)
Definition lt_seg_S11_stmt : Prop := LTA_K85984 B MT -> LT_K85868_stmt B MT.
(* S12 0x85984 .. 0x85990: calloc(cap + 1, 20) *)
Definition lt_seg_S12_stmt : Prop := LTA_K85994 B MT -> LT_K85984_stmt B MT.
(* S13 0x85994 .. 0x85b08 and 0x85e4c: the NULL tests (refuted), the guard memset, n in scope, the "enp1s0"
   entries (checks 26-28, traps 0x859b0 0x859f4 0x85a30), the loop's slots, to m_declared's turn 0 or, m->n <= 0,
   past it *)
Definition lt_seg_S13_stmt : Prop := LTA_K85b0c B MT 0 -> LTA_K85e50 B MT -> LT_K85994_stmt B MT.
(* S14 0x85b0c .. 0x85d00 with the continue join and latch 0x85b58 .. 0x85b94: v in scope, ignore, strrchr, the
   digit and parent loops, memcpy (checks 29-33, traps 0x85b24 .. 0x85cf0), to K85d04 i, or the next turn, or past
   the loop *)
Definition lt_seg_S14_stmt : Prop :=
  forall i, LTA_K85d04 B MT i -> LTA_K85b0c B MT (Datatypes.S i) -> LTA_K85e50 B MT -> LT_K85b0c_stmt B MT i.
(* S15 0x85d04 .. 0x85e14, the join and latch 0x85b58 .. 0x85b94 and the -1 exit 0x85fd8 .. 0x85ff4: the dup
   loop with strcmp, memcpy of v (checks 30, 34, traps 0x85d34 .. 0x85df8) *)
Definition lt_seg_S15_stmt : Prop :=
  forall i, LTA_K85b0c B MT (Datatypes.S i) -> LTA_K85e50 B MT -> LT_K85d04_stmt B MT i.
(* S16 0x85e50 .. 0x85e98: reac_segconf_declared, check_declared, free(mt) *)
Definition lt_seg_S16_stmt : Prop := LTA_K85e9c B MT -> LT_K85e50_stmt B MT.
(* S17 0x85e9c .. 0x85ea0: free(tab) *)
Definition lt_seg_S17_stmt : Prop := LTA_K85ea4 B MT -> LT_K85e9c_stmt B MT.
(* S18 0x85ea4 .. 0x85ea8: free(m) *)
Definition lt_seg_S18_stmt : Prop := LTA_K85eac B MT -> LT_K85ea4_stmt B MT.
(* S19 0x85eac .. 0x85eb0: free(c) *)
Definition lt_seg_S19_stmt : Prop := LTA_K85eb4 B MT -> LT_K85eac_stmt B MT.
(* S20 0x85eb4 .. 0x85ec4: n out of scope, a6 / a7 reloaded from 24(s1) / 16(s1) *)
Definition lt_seg_S20_stmt : Prop := LTA_K85ec8 B MT -> LT_K85eb4_stmt B MT.
(* S21 0x85ec8 .. 0x85fc4: the frame-done word, meta_fill_f5(SH(FR), 64) with SH(FR) from 184(s1), the flag
   store, a0 = 0, the epilogue (the real-stack release 0x85ef4 .. 0x85f84 dead) *)
Definition lt_seg_S21_stmt : Prop := LTA_RET B MT -> LT_K85ec8_stmt B MT.
(* the ret at 0x85fc8, to the post *)
Definition lt_seg_RET_stmt : Prop := LT_RET_stmt B MT.
End st.
