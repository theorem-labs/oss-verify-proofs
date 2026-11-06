(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the shape join of check_reply's walk (fuzz_command.asan, 0x86fcc .. 0x86ff8),
   ported from proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v..ACh8.v, AChc.v and ACke.v (cgif_close's segments and
   their program calls, cl_callS then a fresh seed at the return) at c8557374ad2e.

   From CR_JOIN (a0 = the shape string q) the code re-checks the shadow of g_rec.reply, loads the reply into s3 and
   calls syntax_reply_matches(q, reply) (0x86fdc). A match goes to the epilogue CR_EPI; otherwise it calls
   syntax_reply_matches("resp 0" @ 0x210e0, reply) (0x86ff0), and a second miss would abort, which reply_okA's
   second conjunct refutes (0 <= code: one of the two shapes matches). Each run starts from the mid-walk seed
   (check_reply_sd.v cr_seed) with the frame header read-only, so the run changes no byte the walk reads. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply_s7.v, with its module paths and module names changed; 1313 of its 1367 lines of code are new or changed and 489 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/m_file_k.v, with its module paths, module names and numbers changed; 326 of its 365 lines of code are new or changed and 1328 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3, twin 80e82127e8ca; 0x86140, 3,608 bytes, 902
   instructions, 26 UBSan trap branches to the one `unimp` 0x86e84, 30 instrumented checks, strip and fold called):
   the segment statements of its walk, one MF_<cut>_stmt per cut of the image-B m_file cut map (sha256
   f0e97728f090), the image-B twin of the image-A m_file-family lane's lib/A/Prog/m_file_m.v (commit dd4bb5fb2f90,
   its version 3) in the same form (plugin-hostd/fuzz_command's lib/A/Prog/check_reply_m.v, origin/ossv/recipes
   501c0d516c69; the walk-form survey 2.9): the bundle of the contract's variables (mfv), the entry facts (mf_cx), the post
   (MF_POST), the mid-walk invariant (mf_core, mf_cells), the registers at a program point (mf_regs_at, and
   mf_regs_ex at EXIT), and the configuration at BASE + pc realizing the post (mf_at). Statement text and the logic
   that chains the segments (no instruction is executed here). A walk lane of the image-B m_file-family owner's G2B
   (the cut-statement lane). The contract is image B's copy lib/B/Prog/m_file_c.v (the image-A owner's text, accepted for image B).
   CHANGE LOG (newest first; the segment lanes rebase on each):
   - 1: the first text. Same names and the same logical content as image A's version 3 (the line terms, mf_loop,
     mh_find, mk_disp, mk_kv, MF_POST, the model equation of every cut); registers, frame cells and cut pcs are
     image B's (the image-B m_file cut map table C.1 and the cut map); what differs in shape from A is listed under DIFFERENCES.

   IMAGE B'S PURE PARAMETERS come from lib/B/Prog/SegInstB.v (the image-B harness lane, 1f771e2f2066; SegInstA's names, every
   value measured on B's pin): SegInstB.STK_m_file (= 320 + 16 + max STK_fuzz_catalogue_row STK_m_find = 8,592),
   RLO_A, RHI_A, seg_litA_fz, wordsA (0xa2040), rolesA (0x211e0), catA (0xa20a0), gotwA (0xa3e98), guardA
   (0x5ff838), named in this file by the local notations MF_STK, RLO, RHI, lit, WORDS, ROLES, CAT, GOTW, GUARD.
   Every MF_<cut>_stmt and MF_<cut>_F takes B (and n) only, as image A's version 3: `MF_HEAD_stmt (fx := fx0) B n`,
   `MF_HEAD_F B n`. Entries and call targets stay listing terms (BASE + AF_<F>, SIGMA SS_<x>).

   LOGICAL CONTENT: as image A's file (the segconf porter's plain cuts lib/Prog/m_file_c.v H_MF_HEAD / H_MF_TAIL / H_MF_EXIT
   and lib/Prog/mf_cuts.v H_MF_LONG / HDR / KEY / HFIND / KAT restated over the reader; the line loop's invariant
   m_file_loop as mf_loop; the post fixed by the bundle, each cut stating the plain post's model as an equation with
   mf_final v = SegModel.m_file mc s lab). The line terms mf_line / mf_rest / mf_next / mf_fin and mh_find / mk_disp
   / mk_kv are image A's text word for word (the segconf porter's lib/Prog/mfu_facts.v:228-271, mf_cuts.v:168-170 at
   dec616e11c2f).

   THE CUTS (B pc; listing offset = AF_m_file + (pc - 0x86140), AF_m_file = 0x1380 in lib/B/Prog/SegList.v:12, so
   BASE + AF_m_file = 0x84dc0 + 0x1380 = 0x86140; the entries into each, the image-B m_file cut map):
     ENTRY  0x86140 (+0x000)  the call
     HEAD   0x86378 (+0x238)  0x86374 (the set-up's fall-through), 0x86838 (the tail's `bnez`)
     LONG   0x863d4 (+0x294)  0x863d0 (`bge s4,a1`, s4 = 511, a1 = e - p, not taken)
     HDR    0x864f4 (+0x3b4)  0x864f0 (`bne a0,a1`, a1 = '[', not taken)
     HFIND  0x865c0 (+0x480)  0x865bc (`bgeu s10,a0`, a0 = 16, not taken)
     KEY    0x8661c (+0x4dc)  0x864f0 (taken)
     KDISP  0x86714 (+0x5d4)  0x86710 (after low.i is marked usable, 0x866ec-0x866f8 and 0x86704-0x86710)
     TAIL   0x86820 (+0x6e0)  0x8681c (LONGP), 0x867e8 (the join 0x867e0-0x867e8), 0x86c44 (KDONE)
     KMODEL 0x86840 (+0x700)  0x86724 (ieq "role" = 0)
     KIGN   0x86968 (+0x828)  0x86854 (ieq "model" = 0)
     KKNOCK 0x86a7c (+0x93c)  0x86980 (ieq "ignore" = 0)
     KDONE  0x86c1c (+0xadc)  0x86c18 (`li s4,511`, reached from 0x867bc, 0x868c4, 0x86a78, 0x86c14), 0x86964,
                              0x86b00: m_key's common end, `ld s10,152(s1)` (one instruction after A's place)
     EXIT   0x86da0 (+0xc60)  0x862fc (empty text), 0x8683c (the tail, *p = 0)

   PLACEMENTS (the image-B m_file cut map table C.1 and the B-only invariants under it): s1 = (sp0 - 320) & -32 (mf_s1; frame
   320 bytes, A 288); every frame cell is s1-relative: 16 ~c, 24 c + 0x2004, 32 &kept_knock[0] = c + 0x238c, 40
   ~(c + 0x238c), 48 c + 0x23ac, 56 c + 0x23b0, 64 &c->reading = c + 0x23b4, 72 shadow(WORDS), 80 WORDS, 88
   shadow(FB), 96 FAKE, 104 shadow(c + 0x23b0), 112 c, 120 FB, 128 c + 0x2000, 136 cur, 144 the low buffer FB + 32,
   and 152 the next line's address from 0x86420 on (HDR, KEY, HFIND, the K cuts, KDONE); the per-line scratch cells
   176 / 168 (s / e), 208 / 200 (b / be, k / ke), 192 / 184 (nm / ne, v / ve), which strip reads and writes; 160 =
   FB (0x861e8) is never read and is not stated. shadow(x) = SHADOW_OFF + x / 8. Only 64, 72, 80 and 136 keep image
   A's offset and meaning. The registers at every cut after the entry (mf_regs_at): sp = s1, gp, tp, s0 = sp0, s1,
   s2 = SHADOW_OFF, s3 = the blank mask 0x100002200, s6 = c + 0x2000, s7 = FAKE, s8 = shadow(FB), s9 = c (no
   register holds ' ' across lines; KROLE borrows s6 .. s9 and restores them before every exit). At EXIT only what
   the epilogue reads and the empty-text path has set (mf_regs_ex: sp, gp, tp, s0, s1, s2, s7, s8; s3 is set at
   0x86354, after the empty-text test 0x862fc). The cut's own registers are named at each statement. low.i's 8
   shadow bytes (shadow(FB) + 4 .. + 11) are 0xf8 at HEAD, LONG, HDR, KEY, HFIND, TAIL, EXIT and 0 at the K cuts
   and KDONE (marked usable 0x866ec, unusable again 0x86c20). The saved registers ra, s0 .. s11 at sp0 - 8 .. sp0 -
   104 (mf_saved; the same sp0-relative places as image A).
   THE SIDE-STACK FRAME ONLY: FB = FAKE = frame_addr lyc 1 pos, sp = s1. The real-stack fallback (FAKE = 0, FB =
   s1 - 128, sp = FB; 0x861cc-0x861e4) is not stated: the use-after-return option is AR's constant cell 1 (image B's
   kit copy lib/B/YG0f.v:193-195 aso_const_law, the same text as A's) and astack_malloc_realizes 1 returns a frame,
   as image A's file and check_reply_m state only that branch. On that path AR's zshadow_ok (lib/B/YG0n.v:193-196,
   ARm's am_zshadow) keeps the thread stack's shadow 0, which is what strip's checked accesses to the scratch cells
   need (m_file_sd.v).
   UBSAN TRAPS (the image-B m_file cut map section 1): each of the 26 is refuted from a fact these statements carry: c mod 16 = 0
   and gen + 1 < 2^31 (mf_cx's m_file_pre: 0x8626c, 0x862d4); the text facts of mf_loop and the strip / strchr /
   strlen / memchr posts (0x86398, 0x863b4, 0x8645c, 0x864d0, 0x86508, 0x86518, 0x86568, 0x86640, 0x8667c,
   0x866a8, 0x866cc, 0x869c4, 0x86be8); 0 <= line, line + |rest| <= 65,535 (mf_loop: 0x863c8); g = c + 256 i
   (m_find's post, or cur = mf_cur_ptr c (Some gi) in 136(s1), with c mod 16 = 0: 0x865d4, 0x86ba4, 0x8688c,
   0x868f0, 0x86a20); 0 <= n, n_kept (sa_mconf of mf_core: 0x86b68, 0x86abc); the block's bounds (mf_core's sa_addr)
   with 16(s1) = ~c and 40(s1) = ~(c + 0x238c) (mf_cells: 0x86b74, 0x86ac8); m_key.role in the image (the listing's
   object: 0x868e4).
   THE FP STATE, STACK: as image A's file (every statement takes sa_frm0 at its own fx; the post is apost_baseF;
   the deepest callee window below s1 is fuzz_catalogue_row's).

   DIFFERENCES FROM IMAGE A'S TEXT (shape, not content):
   - mf_regs_at holds s3, s6 .. s9 (s9 = c at every cut, so no cut names c separately); mf_regs_ex is new and EXIT
     takes it instead of mf_regs_at. (Image A's MF_EXIT_stmt asks mf_regs_at, whose s3 = 0x20 and s9 = the blank
     mask are set at A:0x86094 / A:0x860b8, after its empty-text test A:0x86060, so A's ENTRY lane cannot give it on
     the empty-text path; B's EXIT asks only what that path has.)
   - The FAKE premise (A: `getr regs1 24`, s8) is inside mf_regs_ex (s7).
   - mf_core's FB cell is 120(s1) (A 112(s1)); mf_cells has 16 cells (A 14); mf_np is 152(s1) (A 144(s1));
     mf_slot names any 8-byte frame cell (the scratch cells at HFIND and the K cuts).
   - MF_KAT_stmt takes ka0 : bool: at KDISP the key's address is also in a0 (0x866e0; 0x86714 calls ieq without
     reloading it); the other K cuts reload it from 208(s1).
   - The K cuts do not state the value's end (A: s7): image B keeps it only in 184(s1) and no instruction after
     KDISP reads it (fold takes v and |v|). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable SegSyms SegList SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* ===================================== the cut points ===================================== *)
Definition MF_HEAD : Z := AF_m_file + 0x238.     (* 0x86378, the line-loop head *)
Definition MF_LONG : Z := AF_m_file + 0x294.     (* 0x863d4, a line of 512 bytes or more *)
Definition MF_HDR : Z := AF_m_file + 0x3b4.      (* 0x864f4, a stripped line that starts with '[' *)
Definition MF_HFIND : Z := AF_m_file + 0x480.    (* 0x865c0, the header passed its checks: m_find *)
Definition MF_KEY : Z := AF_m_file + 0x4dc.      (* 0x8661c, a stripped line that does not *)
Definition MF_KDISP : Z := AF_m_file + 0x5d4.    (* 0x86714, m_key's dispatch on the key *)
Definition MF_TAIL : Z := AF_m_file + 0x6e0.     (* 0x86820, the end of every line *)
Definition MF_KMODEL : Z := AF_m_file + 0x700.   (* 0x86840, the key is not "role" *)
Definition MF_KIGN : Z := AF_m_file + 0x828.     (* 0x86968, nor "model" *)
Definition MF_KKNOCK : Z := AF_m_file + 0x93c.   (* 0x86a7c, nor "ignore" *)
Definition MF_KDONE : Z := AF_m_file + 0xadc.    (* 0x86c1c, m_key's common end *)
Definition MF_EXIT : Z := AF_m_file + 0xc60.     (* 0x86da0, the frame's release and the return *)

(* the blank set as the loop's shift mask (' ', '\r', '\t'), s3 (0x86354 `slli s3,a2,0x9`, a2 = 0x800011) *)
Definition MF_BLANK : Z := 0x100002200.
(* low.i's shadow bytes: out of scope (0xf8) and in scope (0) *)
Definition MF_LOW_OFF : Z := 0xf8.
Definition MF_LOW_ON : Z := 0.
(* the entry's ra, s0 .. s11, in the order the prologue stores them below sp0 (ra at sp0 - 8, s11 at sp0 - 104;
   0x86148-0x86178 at sp + 312 .. sp + 216 with sp = sp0 - 320) *)
Definition mf_saved_regs : list Z := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
(* s1, the base of the frame cells: (sp0 - 320) & -32 (0x86180 `andi sp,sp,-32`, 0x86184 `mv s1,sp`) *)
Definition mf_s1 (sp0 : Z) : Z := sp0 - 320 - (sp0 - 320) mod 32.
(* the cur cell 136(s1): &c->seg[i] for Some i, NULL for None (plain cur_ptr / cur_ok) *)
Definition mf_cur_ptr (c : Z) (cur : option nat) : Z :=
  match cur with Some i => seg_spec.mseg_addr c i | None => 0 end.
Definition mf_cur_ok (mc : mconf) (cur : option nat) : Prop :=
  match cur with Some i => (i < length (mc_seg mc))%nat | None => True end.

(* ============================ the line and the partial model steps ============================ *)
(* Image A's text (the segconf porter's lib/Prog/mfu_facts.v:228-271 at dec616e11c2f). At the head the text left is rest at
   p; the line is the bytes before its first '\n' (or all of rest), the text after it is mf_rest rest, at
   mf_next p rest (nl + 1, or the NUL when there is no '\n'). *)
Definition mf_line (rest : list Z) : list Z := fst (break_nl rest).
Definition mf_rest (rest : list Z) : list Z := snd (break_nl rest).
Definition mf_next (p : Z) (rest : list Z) : Z := p + Z.of_nat (length rest - length (mf_rest rest)).
(* the final model from a state st after the line numbered line + 1 *)
Definition mf_fin (st : mconf * option nat) (line : Z) (rest : list Z) : mconf :=
  fst (m_lines st (line + 1) (lines (mf_rest rest))).
(* the tail of m_header after its name checks (SegModel.m_header from `match m_find c nm`) *)
Definition mh_find (c : mconf) (nm : list Z) (line : Z) : mconf * option nat :=
  match m_find c nm with
  | None =>
      if (32 <=? length (mc_seg c))%nat then
        (m_refuse (MConf (mc_seg c) (mc_overflow c + 1) (mc_refused c) (mc_kept c) (mc_gen c) (mc_reading c))
                  line false, None)
      else (m_set_segs c (mc_seg c ++ [ms_with_gen (mc_gen c) (mseg0 nm)]), Some (length (mc_seg c)))
  | Some i =>
      let c1 := if ms_gen (nth i (mc_seg c) mseg_d) =? mc_gen c then m_refuse c line false else c in
      (m_upd c1 i (ms_with_gen (mc_gen c)), Some i)
  end.
(* the tail of m_key after the key k and the value v are cut (SegModel.m_key's `Some ei, Some gi` branch from
   `if ieq k S_role`) *)
Definition mk_disp (c : mconf) (gi : nat) (k v : list Z) (line : Z) : mconf :=
  if ieq k S_role then
    match h_role_word (h_fold v 64) with
    | Some r => m_upd c gi (ms_with_role r (snprintf_s 96 F_s [AS (mc_reading c)]))
    | None => m_refuse c line false
    end
  else if ieq k S_model then
    let low := h_fold v 24 in
    match cat_row low with
    | None => m_refuse c line false
    | Some _ => m_upd c gi (ms_with_model low)
    end
  else if ieq k S_ignore then
    if ieq v S_yes || ieq v S_true || ((length v =? 1)%nat && (hd0 v =? 49)) then
      m_upd c gi (ms_with_ignore true (snprintf_s 96 F_s [AS (mc_reading c)]))
    else if ieq v S_no || ieq v S_false || ((length v =? 1)%nat && (hd0 v =? 48)) then
      m_upd c gi (ms_with_ignore false (snprintf_s 96 F_s [AS (mc_reading c)]))
    else m_refuse c line false
  else if ieq k S_knock then m_refuse c line true
  else m_refuse c line false.
(* the key k = the bytes [ok, ok + kl) and the value v = the bytes [ov, ov + vl) of the text left, both inside
   the line (mf_cuts.v:168-170) *)
Definition mk_kv (rest : list Z) (ok kl ov vl : nat) (k v : list Z) : Prop :=
  (ok + kl <= length (mf_line rest))%nat /\ (ov + vl <= length (mf_line rest))%nat /\
  firstn kl (skipn ok rest) = k /\ firstn vl (skipn ov rest) = v.

(* image B's pure parameters (lib/B/Prog/SegInstB.v), local names of this file *)
#[local] Notation MF_STK := SegInstB.STK_m_file.
#[local] Notation RLO := SegInstB.RLO_A.
#[local] Notation RHI := SegInstB.RHI_A.
#[local] Notation lit := SegInstB.seg_litA_fz.
#[local] Notation WORDS := SegInstB.wordsA.
#[local] Notation ROLES := SegInstB.rolesA.
#[local] Notation CAT := SegInstB.catA.
#[local] Notation GOTW := SegInstB.gotwA.
#[local] Notation GUARD := SegInstB.guardA.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the variables of m_file_contract *)
Record mfv := mkMFV {
  mv_ly : alayout; mv_S : astate; mv_W : world SEGS; mv_regs : bvmap 5 word; mv_mem : word -> option byte;
  mv_md : Model; mv_ch : list (Z * Z * Z); mv_c : Z; mv_t : Z; mv_lp : Z; mv_mc : mconf; mv_s : list Z;
  mv_lab : option (list Z) }.
Definition mv_sp (v : mfv) : Z := spZ (mv_regs v).
(* n_kept at the entry: it fixes the footprint *)
Definition mv_k0 (v : mfv) : nat := length (mc_kept (mv_mc v)).
(* the model the block holds at the return *)
Definition mf_final (v : mfv) : mconf := SegModel.m_file (mv_mc v) (mv_s v) (mv_lab v).

Section e.
Variable B : asyms.

(* the entry facts: m_file_contract's premises, in its order, except sa_frm0 (each statement takes it at its own
   FP state) *)
Definition mf_cx (v : mfv) : Prop :=
afn_pre SEGS B MF_STK (mv_ly v) (mv_S v) (mv_W v) (mv_regs v) (mv_mem v) (mv_md v) (mv_ch v) /\
sa_room (mv_S v) /\
arodata_okP SEGS RLO RHI B (rdW (mv_W v) (mv_mem v)) /\
(forall x, In x M_FILE_LITS -> sa_lit SEGS B (rdW (mv_W v) (mv_mem v)) (lit x) x) /\
mf_words SEGS B (rdW (mv_W v) (mv_mem v)) WORDS /\ mf_roles SEGS B (rdW (mv_W v) (mv_mem v)) ROLES /\
sa_cat SEGS B (rdW (mv_W v) (mv_mem v)) CAT /\ sa_ssp (rdW (mv_W v) (mv_mem v)) GOTW GUARD /\
getr (mv_regs v) 10 = w64 (mv_c v) /\ 0 <= mv_c v < 2 ^ 64 /\
getr (mv_regs v) 11 = w64 (mv_t v) /\ 0 <= mv_t v < 2 ^ 64 /\
getr (mv_regs v) 12 = w64 (mv_lp v) /\ 0 <= mv_lp v < 2 ^ 64 /\
m_file_pre SEGS B (mv_ly v) (mv_S v) (rdW (mv_W v) (mv_mem v)) (mv_c v) (mv_t v) (mv_lp v) (mv_mc v) (mv_s v)
  (mv_lab v) /\
st_nev (mv_S v) + EV_m_file <= EV_MAX.

(* the contract's post *)
Definition MF_POST (v : mfv) : world SEGS -> config -> Prop :=
apost_baseF SEGS B MF_STK (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_regs v) (mv_ly v) (mv_S v) (mv_W v)
  (mv_mem v) (mv_md v) EV_m_file
(fun ly' S' W' regs' mem' md' =>
 sa_mconf (rdW W' mem') (mv_c v) (mf_final v) /\ sa_noalloc B (mv_ly v) (mv_S v) ly' S').

(* the layout and allocator state at a mid-walk point: the entry's layout, the entry's state up to st_fs (the
   side-stack frame taken at 0x861b4 is the walk's only state change) *)
Definition mf_ls (v : mfv) (lyc : alayout) (Sc : astate) : Prop :=
lyc = mv_ly v /\ exists f, Sc = set_fs f (mv_S v).

(* the entry's callee-saved registers below sp0 *)
Definition mf_saved (m : word -> option byte) (sp0 : Z) (regs : bvmap 5 word) : Prop :=
forall j r, nth_error mf_saved_regs j = Some r ->
val_mem SEGS m (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))).

(* what the walk keeps from the frame call on: the journal from the entry with the frame (1, pos) owned, the blocks
   unchanged, the frame's flag pointer in its last word, low.i's shadow bytes at lowsh, the saved registers, the
   cell 120(s1) = FB (0x86214; the epilogue reads it at 0x86da8), and the mconf block holding mcc, addressable, with
   its slack *)
Definition mf_core (v : mfv) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (memc : word -> option byte)
(mdc : Model) (pos lowsh : Z) (mcc : mconf) : Prop :=
ajournal SEGS B MF_STK (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v) (mv_W v)
  (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc memc mdc 0 /\
Permutation (ablocks B lyc Sc) (ablocks B (mv_ly v) (mv_S v)) /\
val_mem SEGS (mrestrict (w_H Wc) memc) (frame_addr lyc 1 pos + 120) 8 (flag_addr lyc 1 pos) /\
(forall i, 4 <= i < 12 ->
 val_mem SEGS (mrestrict (w_H Wc) memc) (SHADOW_OFF + frame_addr lyc 1 pos / 8 + i) 1 lowsh) /\
mf_saved (mrestrict (w_H Wc) memc) (mv_sp v) (mv_regs v) /\
val_mem SEGS (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v) + 120) 8 (frame_addr lyc 1 pos) /\
sa_mconf (rdW Wc memc) (mv_c v) mcc /\ sa_addr (rdW Wc memc) (mv_c v) seg_spec.SEG_M_SIZE /\
sa_tail (rdW Wc memc) (mv_c v + seg_spec.SEG_M_SIZE - 1).

(* the frame cells the set-up 0x86300-0x86374 completes (the image-B m_file cut map table C.1 and the B-only invariants), with
   cur in 136(s1); 16(s1) and 40(s1) hold the bitwise complements the wrap traps 0x86b74 and 0x86ac8 compare with *)
Definition mf_cells (v : mfv) (lyc : alayout) (pos : Z) (memc : word -> option byte) (Wc : world SEGS)
(cur : option nat) : Prop :=
val_mem SEGS (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v) + 16) 8 (2 ^ 64 - 1 - mv_c v) /\
val_mem SEGS (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v) + 24) 8 (mv_c v + seg_spec.MC_OVERFLOW) /\
val_mem SEGS (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v) + 32) 8 (mv_c v + seg_spec.MC_KNOCK) /\
val_mem SEGS (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v) + 40) 8 (2 ^ 64 - 1 - (mv_c v + seg_spec.MC_KNOCK)) /\
val_mem SEGS (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v) + 48) 8 (mv_c v + seg_spec.MC_NKEPT) /\
val_mem SEGS (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v) + 56) 8 (mv_c v + seg_spec.MC_GEN) /\
val_mem SEGS (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v) + 64) 8 (mv_c v + seg_spec.MC_READING) /\
val_mem SEGS (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v) + 72) 8 (SHADOW_OFF + WORDS / 8) /\
val_mem SEGS (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v) + 80) 8 WORDS /\
val_mem SEGS (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v) + 88) 8 (SHADOW_OFF + frame_addr lyc 1 pos / 8) /\
val_mem SEGS (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v) + 96) 8 (frame_addr lyc 1 pos) /\
val_mem SEGS (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v) + 104) 8 (SHADOW_OFF + (mv_c v + seg_spec.MC_GEN) / 8) /\
val_mem SEGS (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v) + 112) 8 (mv_c v) /\
val_mem SEGS (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v) + 128) 8 (mv_c v + seg_spec.MC_N) /\
val_mem SEGS (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v) + 136) 8 (mf_cur_ptr (mv_c v) cur) /\
val_mem SEGS (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v) + 144) 8 (frame_addr lyc 1 pos + 32).

(* the 8-byte frame cell off(s1) holds x (the scratch cells 192 / 208 at HFIND and the K cuts) *)
Definition mf_slot (v : mfv) (memc : word -> option byte) (Wc : world SEGS) (off x : Z) : Prop :=
val_mem SEGS (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v) + off) 8 x.
(* the next line's address in 152(s1) (from 0x86420 on) *)
Definition mf_np (v : mfv) (memc : word -> option byte) (Wc : world SEGS) (np : Z) : Prop :=
mf_slot v memc Wc 152 np.

(* the registers both exits of the walk have and the epilogue reads: sp = s1 (the side-stack frame path), gp,
   tp, s0 = sp0, s1, s2 = the shadow base, s7 = FAKE, s8 = shadow(FB) *)
Definition mf_regs_ex (v : mfv) (lyc : alayout) (pos : Z) (regs1 : bvmap 5 word) : Prop :=
getr regs1 2 = w64 (mf_s1 (mv_sp v)) /\ getr regs1 3 = w64 (as_gp B) /\ getr regs1 4 = w64 (as_tp B) /\
getr regs1 8 = w64 (mv_sp v) /\ getr regs1 9 = w64 (mf_s1 (mv_sp v)) /\
getr regs1 18 = w64 SHADOW_OFF /\ getr regs1 23 = w64 (frame_addr lyc 1 pos) /\
getr regs1 24 = w64 (SHADOW_OFF + frame_addr lyc 1 pos / 8).
(* the registers every cut after the entry has: mf_regs_ex and s3 = the blank mask, s6 = c + 0x2000, s9 = c *)
Definition mf_regs_at (v : mfv) (lyc : alayout) (pos : Z) (regs1 : bvmap 5 word) : Prop :=
mf_regs_ex v lyc pos regs1 /\ getr regs1 19 = w64 MF_BLANK /\
getr regs1 22 = w64 (mv_c v + seg_spec.MC_N) /\ getr regs1 25 = w64 (mv_c v).

(* the line loop's facts (plain m_file_loop over the reader): the text left rest at p is the suffix of the entry's
   text, a C string with its slack, addressable; cur names an entry; n_kept has not gone below the entry's; and the
   room the counters and the line number keep, which shrinks with the text left *)
Definition mf_loop (v : mfv) (Wc : world SEGS) (memc : word -> option byte) (mcc : mconf) (cur : option nat)
(line p : Z) (rest : list Z) : Prop :=
(length rest <= length (mv_s v))%nat /\ rest = skipn (length (mv_s v) - length rest) (mv_s v) /\
p = mv_t v + Z.of_nat (length (mv_s v) - length rest) /\
sa_str (rdW Wc memc) p rest /\ sa_addr (rdW Wc memc) p (Z.of_nat (length rest) + 1) /\
mf_cur_ok mcc cur /\ (mv_k0 v <= length (mc_kept mcc))%nat /\
0 <= line /\ line + Z.of_nat (length rest) <= 65535 /\
mc_refused mcc + Z.of_nat (length rest) < 2 ^ 32 /\ mc_overflow mcc + Z.of_nat (length rest) < 2 ^ 32.

Definition mf_at (v : mfv) (Wc : world SEGS) (regs1 : bvmap 5 word) (memc : word -> option byte) (mdc : Model)
(pc : Z) : Prop :=
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS)) mdc) (MF_POST v).

(* ===================================== the statements ===================================== *)
(* the walk from the entry *)
Definition MF_ENTRY_stmt : Prop :=
forall v, mf_cx v -> sa_frm0 ->
SRr SEGS (mv_W v) (cfg_at SEGS (BASE + AF_m_file) (mv_regs v) (mv_mem v) (mv_md v)) (MF_POST v).

(* 0x86378, the head (plain H_MF_HEAD n): s10 = p, s5 = line (the lines consumed), s4 = 511; the text left is
   nonempty and shorter than n bytes *)
Definition MF_HEAD_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (cur : option nat) (line p : Z) (rest : list Z),
mf_cx v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc -> mf_cells v lyc pos memc Wc cur -> mf_regs_at v lyc pos regs1 ->
(length rest < n)%nat -> rest <> [] -> mf_loop v Wc memc mcc cur line p rest ->
fst (m_lines (mcc, cur) line (lines rest)) = mf_final v ->
getr regs1 26 = w64 p -> getr regs1 21 = w64 line -> getr regs1 20 = w64 511 ->
mf_at v Wc regs1 memc mdc MF_HEAD.

(* 0x86820, the tail (plain H_MF_TAIL n): s10 = p (the text after the line, possibly empty), s11 = line (the lines
   consumed; 0x86834 copies it to s5), s4 = 511 *)
Definition MF_TAIL_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (cur : option nat) (line p : Z) (rest : list Z),
mf_cx v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc -> mf_cells v lyc pos memc Wc cur -> mf_regs_at v lyc pos regs1 ->
(length rest < n)%nat -> mf_loop v Wc memc mcc cur line p rest ->
fst (m_lines (mcc, cur) line (lines rest)) = mf_final v ->
getr regs1 26 = w64 p -> getr regs1 27 = w64 line -> getr regs1 20 = w64 511 ->
mf_at v Wc regs1 memc mdc MF_TAIL.

(* 0x86da0, the release and the return (plain H_MF_EXIT): the block holds the final model; s7 = FAKE, s8 =
   shadow(FB) and 120(s1) = FB are what the release reads *)
Definition MF_EXIT_stmt : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos,
mf_cx v -> mf_ls v lyc Sc ->
mf_core v lyc Sc Wc memc mdc pos MF_LOW_OFF (mf_final v) -> mf_regs_ex v lyc pos regs1 ->
mf_at v Wc regs1 memc mdc MF_EXIT.

(* 0x863d4, a long line (plain H_MF_LONG n): s10 = p, a0 = the line's end, a2 = the next line's address, a6 =
   0x20 (the blank skip's bound 0x863f4), s11 = line + 1, s4 = 511 *)
Definition MF_LONG_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (cur : option nat) (line p : Z) (rest : list Z),
mf_cx v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc -> mf_cells v lyc pos memc Wc cur -> mf_regs_at v lyc pos regs1 ->
(length rest <= n)%nat -> rest <> [] -> mf_loop v Wc memc mcc cur line p rest ->
(512 <= length (mf_line rest))%nat ->
mf_fin (m_line (mcc, cur) (line + 1) (mf_line rest)) line rest = mf_final v ->
getr regs1 26 = w64 p -> getr regs1 10 = w64 (p + Z.of_nat (length (mf_line rest))) ->
getr regs1 12 = w64 (mf_next p rest) -> getr regs1 16 = w64 0x20 ->
getr regs1 27 = w64 (line + 1) -> getr regs1 20 = w64 511 ->
mf_at v Wc regs1 memc mdc MF_LONG.

(* 0x864f4, a header line (plain H_MF_HDR n): the stripped line sl = the bytes [i, j) of the line, its first byte
   '['; s10 = p + i, s4 = p + j, a2 = j - i, s5 = 0x20 (the b[7] test 0x86588), 152(s1) = the next line's address,
   s11 = line + 1 *)
Definition MF_HDR_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (cur : option nat) (line p : Z) (rest : list Z) (i j : nat),
mf_cx v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc -> mf_cells v lyc pos memc Wc cur -> mf_regs_at v lyc pos regs1 ->
(length rest <= n)%nat -> rest <> [] -> mf_loop v Wc memc mcc cur line p rest ->
(length (mf_line rest) < 512)%nat ->
(i < j)%nat -> (j <= length (mf_line rest))%nat ->
slice i j (mf_line rest) = h_strip (h_cut_comment (mf_line rest)) ->
nth i (mf_line rest) 0 = LBR ->
mf_fin (m_header mcc (h_strip (h_cut_comment (mf_line rest))) (line + 1)) line rest = mf_final v ->
getr regs1 26 = w64 (p + Z.of_nat i) -> getr regs1 20 = w64 (p + Z.of_nat j) ->
getr regs1 12 = w64 (Z.of_nat (j - i)) -> getr regs1 21 = w64 0x20 ->
mf_np v memc Wc (mf_next p rest) -> getr regs1 27 = w64 (line + 1) ->
mf_at v Wc regs1 memc mdc MF_HDR.

(* 0x8661c, a key line (plain H_MF_KEY n): as HDR, the first byte not '[' *)
Definition MF_KEY_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (cur : option nat) (line p : Z) (rest : list Z) (i j : nat),
mf_cx v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc -> mf_cells v lyc pos memc Wc cur -> mf_regs_at v lyc pos regs1 ->
(length rest <= n)%nat -> rest <> [] -> mf_loop v Wc memc mcc cur line p rest ->
(length (mf_line rest) < 512)%nat ->
(i < j)%nat -> (j <= length (mf_line rest))%nat ->
slice i j (mf_line rest) = h_strip (h_cut_comment (mf_line rest)) ->
nth i (mf_line rest) 0 <> LBR ->
mf_fin (m_key mcc cur (h_strip (h_cut_comment (mf_line rest))) (line + 1), cur) line rest = mf_final v ->
getr regs1 26 = w64 (p + Z.of_nat i) -> getr regs1 20 = w64 (p + Z.of_nat j) ->
getr regs1 12 = w64 (Z.of_nat (j - i)) -> getr regs1 21 = w64 0x20 ->
mf_np v memc Wc (mf_next p rest) -> getr regs1 27 = w64 (line + 1) ->
mf_at v Wc regs1 memc mdc MF_KEY.

(* 0x865c0, m_find's call (plain H_MF_HFIND n): the name nm = the bytes [o, o + |nm|) of the text left, inside the
   line, 1 <= |nm| <= 15; a1 = the name, also in 192(s1) (memcpy's source, 0x86b8c), s10 = |nm|, s4 = 511, s11 =
   line + 1, the next line's address only in 152(s1) *)
Definition MF_HFIND_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (cur : option nat) (line p : Z) (rest : list Z) (o : nat)
  (nm : list Z),
mf_cx v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc -> mf_cells v lyc pos memc Wc cur -> mf_regs_at v lyc pos regs1 ->
(length rest <= n)%nat -> rest <> [] -> mf_loop v Wc memc mcc cur line p rest ->
(0 < length nm < 16)%nat -> (o + length nm <= length (mf_line rest))%nat ->
firstn (length nm) (skipn o rest) = nm ->
mf_fin (mh_find mcc nm (line + 1)) line rest = mf_final v ->
getr regs1 11 = w64 (p + Z.of_nat o) -> mf_slot v memc Wc 192 (p + Z.of_nat o) ->
getr regs1 26 = w64 (Z.of_nat (length nm)) -> getr regs1 20 = w64 511 ->
getr regs1 27 = w64 (line + 1) -> mf_np v memc Wc (mf_next p rest) ->
mf_at v Wc regs1 memc mdc MF_HFIND.

(* the K cuts (plain H_MF_KAT pc missed n): cur = Some gi, the key k = [ok, ok + kl) and the value v = [ov, ov +
   vl) of the text left, both inside the line, the words missed so far; 208(s1) = k (and a0 = k at KDISP: ka0),
   s5 = kl, 192(s1) = v, s10 = vl, s11 = line + 1; the next line's address only in 152(s1); low.i in scope *)
Definition MF_KAT_stmt (pc : Z) (missed : list (list Z)) (ka0 : bool) (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (ok kl ov vl : nat)
  (k vv : list Z),
mf_cx v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core v lyc Sc Wc memc mdc pos MF_LOW_ON mcc -> mf_cells v lyc pos memc Wc (Some gi) ->
mf_regs_at v lyc pos regs1 ->
(length rest <= n)%nat -> rest <> [] -> mf_loop v Wc memc mcc (Some gi) line p rest ->
mk_kv rest ok kl ov vl k vv -> Forall (fun w => ieq k w = false) missed ->
mf_fin (mk_disp mcc gi k vv (line + 1), Some gi) line rest = mf_final v ->
mf_slot v memc Wc 208 (p + Z.of_nat ok) -> (ka0 = true -> getr regs1 10 = w64 (p + Z.of_nat ok)) ->
getr regs1 21 = w64 (Z.of_nat kl) ->
mf_slot v memc Wc 192 (p + Z.of_nat ov) -> getr regs1 26 = w64 (Z.of_nat vl) ->
getr regs1 27 = w64 (line + 1) -> mf_np v memc Wc (mf_next p rest) ->
mf_at v Wc regs1 memc mdc pc.
(* 0x86714 (no word missed; a0 = k), 0x86840 ("role" missed), 0x86968 ("model" too), 0x86a7c ("ignore" too) *)
Definition MF_KDISP_stmt (n : nat) : Prop := MF_KAT_stmt MF_KDISP [] true n.
Definition MF_KMODEL_stmt (n : nat) : Prop := MF_KAT_stmt MF_KMODEL [S_role] false n.
Definition MF_KIGN_stmt (n : nat) : Prop := MF_KAT_stmt MF_KIGN [S_role; S_model] false n.
Definition MF_KKNOCK_stmt (n : nat) : Prop := MF_KAT_stmt MF_KKNOCK [S_role; S_model; S_ignore] false n.

(* 0x86c1c, m_key's common end (ASan only): the line is done, the state is the tail's with the next line's address
   p only in 152(s1) and low.i still in scope; s11 = line (the lines consumed), s4 = 511 *)
Definition MF_KDONE_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (cur : option nat) (line p : Z) (rest : list Z),
mf_cx v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core v lyc Sc Wc memc mdc pos MF_LOW_ON mcc -> mf_cells v lyc pos memc Wc cur -> mf_regs_at v lyc pos regs1 ->
(length rest < n)%nat -> mf_loop v Wc memc mcc cur line p rest ->
fst (m_lines (mcc, cur) line (lines rest)) = mf_final v ->
mf_np v memc Wc p -> getr regs1 27 = w64 line -> getr regs1 20 = w64 511 ->
mf_at v Wc regs1 memc mdc MF_KDONE.

(* the contract from the walk from the entry: the bundle is the contract's variables *)
Lemma m_file_contract_of_entry : MF_ENTRY_stmt ->
m_file_contract SEGS B (BASE + AF_m_file) MF_STK RLO RHI lit WORDS ROLES CAT GOTW GUARD.
Proof.
intros EN. unfold m_file_contract.
intros ly S W regs mem md ch c t lp mc s lab HPRE HFRM HROOM HROD HLIT HWD HRL HCAT HSSP H10 H10r H11 H11r H12 H12r
  HMP HEV.
exact (EN (mkMFV ly S W regs mem md ch c t lp mc s lab)
  (conj HPRE (conj HROOM (conj HROD (conj HLIT (conj HWD (conj HRL (conj HCAT (conj HSSP (conj H10 (conj H10r
  (conj H11 (conj H11r (conj H12 (conj H12r (conj HMP HEV))))))))))))))) HFRM).
Qed.
(* the base registers of a cut are those of the exit *)
Lemma mf_regs_ex_of_at : forall v lyc pos regs1, mf_regs_at v lyc pos regs1 -> mf_regs_ex v lyc pos regs1.
Proof. intros v lyc pos regs1 [H _]. exact H. Qed.
End e.
End f.
End d.

(* ============================ the segments and how they chain ============================ *)
(* Each cut at every FP state (a cut is reached at the FP state the last snprintf call returned), and one
   S_MF_<piece> per segment of the image-B m_file cut map section 4: `<its exit cuts> -> <its entry cut>`. The pieces' code,
   traps, checks and callees are listed there and in the image-B m_file segment table (S_MF_ENTRY 157 instructions, FRONT 88,
   LONGP 39, HDRA 65, HDRB 113, KEYA 74, KROLE 101, KMOD 43, KIGNP 97, KKNOCKP 44, KDONE 11, TAIL 13, EXIT 57). *)
Section g. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section h.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
Section i.
Variable B : asyms.

Definition MF_ENTRY_F : Prop := forall fx0 : YK11.FPState, MF_ENTRY_stmt (fx := fx0) B.
Definition MF_HEAD_F (n : nat) : Prop := forall fx0 : YK11.FPState, MF_HEAD_stmt (fx := fx0) B n.
Definition MF_TAIL_F (n : nat) : Prop := forall fx0 : YK11.FPState, MF_TAIL_stmt (fx := fx0) B n.
Definition MF_EXIT_F : Prop := forall fx0 : YK11.FPState, MF_EXIT_stmt (fx := fx0) B.
Definition MF_LONG_F (n : nat) : Prop := forall fx0 : YK11.FPState, MF_LONG_stmt (fx := fx0) B n.
Definition MF_HDR_F (n : nat) : Prop := forall fx0 : YK11.FPState, MF_HDR_stmt (fx := fx0) B n.
Definition MF_KEY_F (n : nat) : Prop := forall fx0 : YK11.FPState, MF_KEY_stmt (fx := fx0) B n.
Definition MF_HFIND_F (n : nat) : Prop := forall fx0 : YK11.FPState, MF_HFIND_stmt (fx := fx0) B n.
Definition MF_KDISP_F (n : nat) : Prop := forall fx0 : YK11.FPState, MF_KDISP_stmt (fx := fx0) B n.
Definition MF_KMODEL_F (n : nat) : Prop := forall fx0 : YK11.FPState, MF_KMODEL_stmt (fx := fx0) B n.
Definition MF_KIGN_F (n : nat) : Prop := forall fx0 : YK11.FPState, MF_KIGN_stmt (fx := fx0) B n.
Definition MF_KKNOCK_F (n : nat) : Prop := forall fx0 : YK11.FPState, MF_KKNOCK_stmt (fx := fx0) B n.
Definition MF_KDONE_F (n : nat) : Prop := forall fx0 : YK11.FPState, MF_KDONE_stmt (fx := fx0) B n.

(* S_MF_ENTRY: the prologue, the side-stack frame, the c & 3 trap, snprintf of c->reading, gen++ (its overflow
   trap), *text = 0 to EXIT, the set-up *)
Definition S_MF_ENTRY : Prop := (forall n, MF_HEAD_F n) -> MF_EXIT_F -> MF_ENTRY_F.
(* S_MF_FRONT: strchr / strlen, line + 1, the long-line test, the comment cut, strip, the '[' test; an empty line
   to TAIL *)
Definition S_MF_FRONT : Prop :=
forall n, MF_TAIL_F n -> MF_LONG_F n -> MF_HDR_F n -> MF_KEY_F n -> MF_HEAD_F (S n).
(* S_MF_LONGP: the blank skip, cur = NULL on '[', m_refuse *)
Definition S_MF_LONGP : Prop := forall n, MF_TAIL_F n -> MF_LONG_F n.
(* S_MF_HDRA: memchr ']', strip twice, ieq "segment", the name checks; the refusals to TAIL *)
Definition S_MF_HDRA : Prop := forall n, MF_TAIL_F n -> MF_HFIND_F n -> MF_HDR_F n.
(* S_MF_HDRB: m_find; found: the gen test, m_refuse; new: n < 32, memset, memcpy; full: overflow++, m_refuse *)
Definition S_MF_HDRB : Prop := forall n, MF_TAIL_F n -> MF_HFIND_F n.
(* S_MF_KEYA: memchr '=', cur = NULL or no '=' refused, the key and value strips, the quotes, low.i in scope *)
Definition S_MF_KEYA : Prop := forall n, MF_TAIL_F n -> MF_KDISP_F n -> MF_KEY_F n.
(* S_MF_KROLE: ieq "role", fold, the words loop (strlen, bcmp), the role stores, snprintf; a miss m_refuse *)
Definition S_MF_KROLE : Prop := forall n, MF_KDONE_F n -> MF_KMODEL_F n -> MF_KDISP_F n.
(* S_MF_KMOD: ieq "model", fold, fuzz_catalogue_row, memcpy into g->model; NULL m_refuse *)
Definition S_MF_KMOD : Prop := forall n, MF_KDONE_F n -> MF_KIGN_F n -> MF_KMODEL_F n.
(* S_MF_KIGNP: ieq "ignore", the six value words, the ignore stores, snprintf; a bad value m_refuse *)
Definition S_MF_KIGNP : Prop := forall n, MF_KDONE_F n -> MF_KKNOCK_F n -> MF_KIGN_F n.
(* S_MF_KKNOCKP: ieq "knock", kept_knock[n_kept] = 1, m_refuse; an unknown key m_refuse *)
Definition S_MF_KKNOCKP : Prop := forall n, MF_KDONE_F n -> MF_KKNOCK_F n.
(* S_MF_KDONE: s10 = 152(s1), low.i out of scope again *)
Definition S_MF_KDONE : Prop := forall n, MF_TAIL_F n -> MF_KDONE_F n.
(* S_MF_TAIL: the check of *p, s5 = s11, `bnez` back to HEAD, else EXIT *)
Definition S_MF_TAIL : Prop := forall n, MF_HEAD_F n -> MF_EXIT_F -> MF_TAIL_F n.
(* S_MF_EXIT: FB + 0 = 0x45e0360e, the frame's shadow 0xf5, the flag byte cleared, the restores, `ret` *)
Definition S_MF_EXIT : Prop := MF_EXIT_F.
(* one line, HEAD (S n) from TAIL n (plain S_MF_LINE) *)
Definition S_MF_LINE : Prop := forall n, MF_TAIL_F n -> MF_HEAD_F (S n).

(* the in-line segments give one line (plain mf_cuts.v mf_line_from_parts, with KDONE between the K pieces and the
   tail) *)
Lemma mf_line_from_parts :
  S_MF_FRONT -> S_MF_LONGP -> S_MF_HDRA -> S_MF_HDRB -> S_MF_KEYA -> S_MF_KROLE -> S_MF_KMOD -> S_MF_KIGNP ->
  S_MF_KKNOCKP -> S_MF_KDONE -> S_MF_LINE.
Proof.
intros FR LG HA HB KA KR KM KI KK KD n HT.
pose proof (KD n HT) as HKD. pose proof (KK n HKD) as HKK. pose proof (KI n HKD HKK) as HKI.
pose proof (KM n HKD HKI) as HKM. pose proof (KR n HKD HKM) as HKP. pose proof (KA n HT HKP) as HKY.
pose proof (HB n HT) as HHF. pose proof (HA n HT HHF) as HHD.
exact (FR n HT (LG n HT) HHD HKY).
Qed.

(* every head, by induction on the bound n on the text left (plain m_file.v m_file_heads): HEAD 0 is empty, no
   text is shorter than 0 bytes; HEAD (S n) is one line from TAIL n, which TAIL gives from HEAD n and EXIT *)
Lemma mf_heads : S_MF_EXIT -> S_MF_TAIL -> S_MF_LINE -> forall n, MF_HEAD_F n.
Proof.
intros EX TL LN n. induction n as [|n IH].
- unfold MF_HEAD_F. intros fx0. unfold MF_HEAD_stmt. intros. lia.
- apply LN. apply TL; [exact IH | exact EX].
Qed.

(* the walk from the entry from all the segments *)
Lemma mf_entry_from_parts : S_MF_ENTRY -> S_MF_EXIT -> S_MF_TAIL -> S_MF_LINE -> MF_ENTRY_F.
Proof. intros EN EX TL LN. apply EN; [exact (mf_heads EX TL LN) | exact EX]. Qed.

(* the contract at every FP state from the segments *)
Lemma m_file_contract_of_parts :
  S_MF_ENTRY -> S_MF_EXIT -> S_MF_TAIL -> S_MF_FRONT -> S_MF_LONGP -> S_MF_HDRA -> S_MF_HDRB -> S_MF_KEYA ->
  S_MF_KROLE -> S_MF_KMOD -> S_MF_KIGNP -> S_MF_KKNOCKP -> S_MF_KDONE ->
  forall fx0 : YK11.FPState,
  m_file_contract (fx := fx0) SEGS B (BASE + AF_m_file) MF_STK RLO RHI lit WORDS ROLES CAT GOTW GUARD.
Proof.
intros EN EX TL FR LG HA HB KA KR KM KI KK KD fx0.
apply (m_file_contract_of_entry (fx := fx0)).
exact (mf_entry_from_parts EN EX TL (mf_line_from_parts FR LG HA HB KA KR KM KI KK KD) fx0).
Qed.
End i.
End h.
End g.
