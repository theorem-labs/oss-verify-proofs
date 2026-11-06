(* m_file on fuzz_segconf.asan (image A, 0x85ebc): the segment statements of its walk, one MF_<cut>_stmt per cut of
   the G2 walk owner's guide/MF-CUTS-A.md (sha256 8761669a9b3d) section 2, in the form of plugin-hostd/fuzz_command's
   lib/A/Prog/check_reply_m.v (origin/ossv/recipes 501c0d516c69; AWALK-FORM.md 2.9): a bundle of the contract's
   variables (mfv), the entry facts (mf_cx), the post (MF_POST), a mid-walk invariant (mf_core, mf_cells), the
   registers at a program point (mf_regs_at and each cut's own), and the configuration at BASE + pc realizing the
   post (mf_at). Statement text and the logic that chains the segments (no instruction is executed here). Lane
   the m_file cut-statement lane of the G2 walk owner's G2.
   CHANGE LOG (newest first; the segment lanes rebase on each):
   - 4 (on commit 60167ac2d043): MF_EXIT_stmt takes mf_regs_ex (sp = s1, gp, tp, s0 = sp0, s1, s2 = SB,
     s10 = shadow(FB)) in place of mf_regs_at. On the empty-text path (0x86060 -> 0x86e70) the set-up 0x86064-0x860cc
     has not run, so s3 (`li s3,32` 0x86094; it still holds FB from 0x85f44) and s9 (0x860b8; still the caller's)
     are not mf_regs_at's; the epilogue 0x86e70-0x86f50 reads only s0, s1, s8, s10 and 112(s1). mf_regs_ex_of_at
     gives it from mf_regs_at (TAIL -> EXIT). Found by the image-B twin's cut lane, confirmed on image A
     by the ENTRY segment lane. Every other statement is unchanged.
   - 3 (on commit b14fca6b866f): image A's pure parameters come from lib/A/Prog/SegInstA.v (the image-A owner's ruling
     16:54Z): the Section variables RLO RHI lit WORDS ROLES CAT GOTW GUARD are gone and MF_STK is no longer a
     Definition here. The statements use SegInstA.STK_m_file (= 8,560), RLO_A, RHI_A, seg_litA_fz, wordsA, rolesA,
     catA, gotwA, guardA (local notations MF_STK, RLO, ... below name them in this file only). Every MF_<cut>_stmt
     and MF_<cut>_F now takes B (and n) only: write `MF_HEAD_stmt (fx := fx0) B n`, `MF_HEAD_F B n`. No cut
     predicate changed. Entries and call targets stay listing terms (BASE + AF_<F>, SIGMA SS_<x>).
   - 2 (on commit 76c815f097a3): aligned to the image-A owner's text of record of m_file_c.v (commit
     044216da3413): the Section variables and every MF_<cut>_F / m_file_contract use take the contract's parameter
     order `RLO RHI lit WORDS ROLES CAT GOTW GUARD`; MF_STK = 288 + 16 + (64 + 2 * ESTACK) = 8,560 (the image-A owner's image-A
     STK_m_file: the deepest callee is fuzz_catalogue_row, snprintf's window is CMD_SNP_K = 2 * ESTACK). mf_cx is
     unchanged in shape (mf_words / mf_roles / m_file_pre now carry the image-A owner's sa_pinned and label forms).
   - 1 (e6baa14cc8d5): the first text.

   LOGICAL CONTENT: the plain / image-B owner's plain cuts (lib/Prog/m_file_c.v H_MF_HEAD / H_MF_TAIL / H_MF_EXIT at 440d61eaa8c8 and
   lib/Prog/mf_cuts.v H_MF_LONG / HDR / KEY / HFIND / KAT at dec616e11c2f) restated over the A reader, with the line
   loop's invariant m_file_loop as mf_loop, indexed by the bound n on the text left as there. The plain post of a
   cut is the function's post computed from the cut's state; here the post is the contract's, fixed by the bundle
   (as check_reply_m's CR_POST), and each cut states the plain post's model as an equation with the final model
   mf_final v = SegModel.m_file mc s lab: HEAD / TAIL / KDONE `fst (m_lines (mcc, cur) line (lines rest)) =
   mf_final v`, LONG `mf_fin (m_line ..)`, HDR `mf_fin (m_header ..)`, KEY `mf_fin (m_key .., cur)`, HFIND
   `mf_fin (mh_find ..)`, the K cuts `mf_fin (mk_disp ..)`. The line terms mf_line / mf_rest / mf_next / mf_fin and
   the partial steps mh_find / mk_disp are restated word for word from the plain / image-B owner's lib/Prog/mfu_facts.v:228-271 at
   dec616e11c2f (build-independent; that file is not in this tree), as is mk_kv (mf_cuts.v:168-170).

   THE CUTS (A pc; listing offset = AF_m_file + (pc - 0x85ebc); the entries into each, MF-CUTS-A.md section 2):
     ENTRY  0x85ebc (+0x000)  the call
     HEAD   0x860d0 (+0x214)  0x860cc (the set-up), 0x86d10 (the tail's `bnez`)
     LONG   0x86110 (+0x254)  0x8610c (`bge a1,a0`, a1 = 511, not taken)
     HDR    0x862cc (+0x410)  0x862c8 (`bne a0,a1`, a1 = '[', not taken)
     KEY    0x8633c (+0x480)  0x862c8 (taken)
     KDISP  0x86684 (+0x7c8)  0x86680 (after low.i is marked usable 0x86664-0x86680)
     KMODEL 0x867b8 (+0x8fc)  0x86698 (ieq "role" = 0)
     KIGN   0x8693c (+0xa80)  0x867cc (ieq "model" = 0)
     HFIND  0x86abc (+0xc00)  0x86ab8 (`bgeu s4,a0`, a0 = 16, not taken)
     KKNOCK 0x86b20 (+0xc64)  0x86950 (ieq "ignore" = 0)
     KDONE  0x86cd0 (+0xe14)  every K path (0x867b4, 0x86938, 0x868b4, 0x86ccc, 0x86a40): m_key's common end, the
                              ASan-only cut MF-CUTS-A.md section 5 item 2 recommends
     TAIL   0x86cf8 (+0xe3c)  0x861f4, 0x862a4, 0x86be0, 0x86c80, 0x86cf4
     EXIT   0x86e70 (+0xfb4)  0x86060 (empty text), 0x86d14 (the tail, *p = 0)

   PLACEMENTS (MF-CUTS-A.md 2.1): s1 = (sp0 - 288) & -32 (mf_s1); every frame cell is s1-relative: 24 &kept_knock[0]
   = c + 0x238c, 32 c + 0x2004, 40 c + 0x23ac, 48 c + 0x23b0, 56 shadow(c + 0x23b0), 64 &c->reading = c + 0x23b4,
   72 shadow(WORDS), 80 WORDS, 88 c + 0x2000, 104 FAKE, 112 FB, 120 shadow(FB), 128 c, 136 cur, 152 the low buffer
   FB + 32, and 144 the next line's address from 0x862b8 on (HDR, KEY, HFIND, the K cuts, KDONE); shadow(x) =
   SHADOW_OFF + x / 8. The registers at every cut after the entry: sp = s1, gp, tp, s0 = sp0, s1, s2 = SHADOW_OFF,
   s3 = 0x20, s9 = the blank mask 0x100002200, s10 = shadow(FB); s8 = FAKE except at the K cuts, where s8 = line + 1
   and FAKE is only in 104(s1). The cut's own registers are named at each statement. low.i's 8 shadow bytes
   (shadow(FB) + 4 .. + 11) are 0xf8 at HEAD, LONG, HDR, KEY, HFIND, TAIL, EXIT and 0 at the K cuts and KDONE.
   The saved registers ra, s0 .. s11 at sp0 - 8 .. sp0 - 104 (mf_saved).
   THE SIDE-STACK FRAME ONLY: FB = FAKE = frame_addr lyc 1 pos, sp = s1. The real-stack fallback (FAKE = 0, FB =
   s1 - 128, sp = FB; 0x85f4c-0x85f64) is not stated: the use-after-return option is AR's constant cell 1
   (lib/Reusable/YG0f.v:193) and astack_malloc_realizes 1 returns a frame, as check_reply_m states only that branch
   (check_reply_c.v:40-42).
   EXIT names only the cells the empty-text path has set when it reaches 0x86e70 from 0x86060: 112(s1) (stored
   0x86038) and the registers s8, s10 (24 .. 152 except 48 / 56 / 64 / 88 / 112 are stored after 0x86060).
   THE FP STATE: m_file reaches the snprintf wrapper itself (0x86014, 0x86934, 0x86a34) and through m_refuse, so a
   cut is reached at the FP state the last call returned. Every statement takes sa_frm0 at its own fx (the wrappers'
   post gives rounding mode 0 back) and its post is apost_baseF at its own fx, as check_reply_m's; the segment
   shapes S_MF_<x> take and give each cut at every FP state (MF_<cut>_F), and PaFx's srr_after_artF joins the posts
   (check_reply.v:104-123).
   STACK: SegInstA.STK_m_file = 288 + 16 + STK_fuzz_catalogue_row = 288 + 16 + (64 + 2 * ESTACK) = 8,560 (the deepest
   callee window below s1 is fuzz_catalogue_row's).
   IMAGE NUMBERS: SegInstA's pure parameters (RLO_A, RHI_A, seg_litA_fz, wordsA, rolesA, catA, gotwA, guardA), named
   in this file by the local notations RLO, RHI, lit, WORDS, ROLES, CAT, GOTW, GUARD. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable SegSyms SegList SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
(* image A's pure parameters (lib/A/Prog/SegInstA.v), local names of this file *)
#[local] Notation MF_STK := SegInstA.STK_m_file.
#[local] Notation RLO := SegInstA.RLO_A.
#[local] Notation RHI := SegInstA.RHI_A.
#[local] Notation lit := SegInstA.seg_litA_fz.
#[local] Notation WORDS := SegInstA.wordsA.
#[local] Notation ROLES := SegInstA.rolesA.
#[local] Notation CAT := SegInstA.catA.
#[local] Notation GOTW := SegInstA.gotwA.
#[local] Notation GUARD := SegInstA.guardA.

(* ===================================== the cut points ===================================== *)
Definition MF_HEAD : Z := AF_m_file + 0x214.     (* 0x860d0, the line-loop head *)
Definition MF_LONG : Z := AF_m_file + 0x254.     (* 0x86110, a line of 512 bytes or more *)
Definition MF_HDR : Z := AF_m_file + 0x410.      (* 0x862cc, a stripped line that starts with '[' *)
Definition MF_KEY : Z := AF_m_file + 0x480.      (* 0x8633c, a stripped line that does not *)
Definition MF_KDISP : Z := AF_m_file + 0x7c8.    (* 0x86684, m_key's dispatch on the key *)
Definition MF_KMODEL : Z := AF_m_file + 0x8fc.   (* 0x867b8, the key is not "role" *)
Definition MF_KIGN : Z := AF_m_file + 0xa80.     (* 0x8693c, nor "model" *)
Definition MF_HFIND : Z := AF_m_file + 0xc00.    (* 0x86abc, the header passed its checks: m_find *)
Definition MF_KKNOCK : Z := AF_m_file + 0xc64.   (* 0x86b20, nor "ignore" *)
Definition MF_KDONE : Z := AF_m_file + 0xe14.    (* 0x86cd0, m_key's common end *)
Definition MF_TAIL : Z := AF_m_file + 0xe3c.     (* 0x86cf8, the end of every line *)
Definition MF_EXIT : Z := AF_m_file + 0xfb4.     (* 0x86e70, the frame's release and the return *)

(* the blank set as the loop's shift mask (' ', '\r', '\t'), s9 *)
Definition MF_BLANK : Z := 0x100002200.
(* low.i's shadow bytes: out of scope (0xf8) and in scope (0) *)
Definition MF_LOW_OFF : Z := 0xf8.
Definition MF_LOW_ON : Z := 0.
(* the entry's ra, s0 .. s11, in the order the prologue stores them below sp0 (ra at sp0 - 8, s11 at sp0 - 104) *)
Definition mf_saved_regs : list Z := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
(* s1, the base of the spill slots: (sp0 - 288) & -32 *)
Definition mf_s1 (sp0 : Z) : Z := sp0 - 288 - (sp0 - 288) mod 32.
(* the cur cell 136(s1): &c->seg[i] for Some i, NULL for None (plain cur_ptr / cur_ok) *)
Definition mf_cur_ptr (c : Z) (cur : option nat) : Z :=
  match cur with Some i => seg_spec.mseg_addr c i | None => 0 end.
Definition mf_cur_ok (mc : mconf) (cur : option nat) : Prop :=
  match cur with Some i => (i < length (mc_seg mc))%nat | None => True end.

(* ============================ the line and the partial model steps ============================ *)
(* Restated from the plain / image-B owner's lib/Prog/mfu_facts.v:228-271 at dec616e11c2f. At the head the text left is rest at p;
   the line is the bytes before its first '\n' (or all of rest), the text after it is mf_rest rest, at
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
   side-stack frame taken at 0x85f30 is the walk's only state change) *)
Definition mf_ls (v : mfv) (lyc : alayout) (Sc : astate) : Prop :=
lyc = mv_ly v /\ exists f, Sc = set_fs f (mv_S v).

(* the entry's callee-saved registers below sp0 *)
Definition mf_saved (m : word -> option byte) (sp0 : Z) (regs : bvmap 5 word) : Prop :=
forall j r, nth_error mf_saved_regs j = Some r ->
val_mem SEGS m (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))).

(* what the walk keeps from the frame call on: the journal from the entry with the frame (1, pos) owned, the blocks
   unchanged, the frame's flag pointer in its last word, low.i's shadow bytes at lowsh, the saved registers, the
   slot 112(s1) = FB, and the mconf block holding mcc, addressable, with its slack *)
Definition mf_core (v : mfv) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (memc : word -> option byte)
(mdc : Model) (pos lowsh : Z) (mcc : mconf) : Prop :=
ajournal SEGS B MF_STK (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v) (mv_W v)
  (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc memc mdc 0 /\
Permutation (ablocks B lyc Sc) (ablocks B (mv_ly v) (mv_S v)) /\
val_mem SEGS (mrestrict (w_H Wc) memc) (frame_addr lyc 1 pos + 120) 8 (flag_addr lyc 1 pos) /\
(forall i, 4 <= i < 12 ->
 val_mem SEGS (mrestrict (w_H Wc) memc) (SHADOW_OFF + frame_addr lyc 1 pos / 8 + i) 1 lowsh) /\
mf_saved (mrestrict (w_H Wc) memc) (mv_sp v) (mv_regs v) /\
val_mem SEGS (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v) + 112) 8 (frame_addr lyc 1 pos) /\
sa_mconf (rdW Wc memc) (mv_c v) mcc /\ sa_addr (rdW Wc memc) (mv_c v) seg_spec.SEG_M_SIZE /\
sa_tail (rdW Wc memc) (mv_c v + seg_spec.SEG_M_SIZE - 1).

(* the spill slots the set-up 0x86064-0x860cc completes (MF-CUTS-A.md 2.1), with cur in 136(s1) *)
Definition mf_cells (v : mfv) (lyc : alayout) (pos : Z) (memc : word -> option byte) (Wc : world SEGS)
(cur : option nat) : Prop :=
val_mem SEGS (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v) + 24) 8 (mv_c v + seg_spec.MC_KNOCK) /\
val_mem SEGS (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v) + 32) 8 (mv_c v + seg_spec.MC_OVERFLOW) /\
val_mem SEGS (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v) + 40) 8 (mv_c v + seg_spec.MC_NKEPT) /\
val_mem SEGS (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v) + 48) 8 (mv_c v + seg_spec.MC_GEN) /\
val_mem SEGS (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v) + 56) 8 (SHADOW_OFF + (mv_c v + seg_spec.MC_GEN) / 8) /\
val_mem SEGS (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v) + 64) 8 (mv_c v + seg_spec.MC_READING) /\
val_mem SEGS (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v) + 72) 8 (SHADOW_OFF + WORDS / 8) /\
val_mem SEGS (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v) + 80) 8 WORDS /\
val_mem SEGS (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v) + 88) 8 (mv_c v + seg_spec.MC_N) /\
val_mem SEGS (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v) + 104) 8 (frame_addr lyc 1 pos) /\
val_mem SEGS (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v) + 120) 8 (SHADOW_OFF + frame_addr lyc 1 pos / 8) /\
val_mem SEGS (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v) + 128) 8 (mv_c v) /\
val_mem SEGS (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v) + 136) 8 (mf_cur_ptr (mv_c v) cur) /\
val_mem SEGS (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v) + 152) 8 (frame_addr lyc 1 pos + 32).

(* the next line's address in 144(s1) (from 0x862b8 on) *)
Definition mf_np (v : mfv) (memc : word -> option byte) (Wc : world SEGS) (np : Z) : Prop :=
val_mem SEGS (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v) + 144) 8 np.

(* the registers every cut after the entry has: sp = s1 (the side-stack frame path), gp, tp, s0 = sp0, s1,
   s2 = the shadow base, s3 = ' ', s9 = the blank mask, s10 = shadow(FB) *)
Definition mf_regs_at (v : mfv) (lyc : alayout) (pos : Z) (regs1 : bvmap 5 word) : Prop :=
getr regs1 2 = w64 (mf_s1 (mv_sp v)) /\ getr regs1 3 = w64 (as_gp B) /\ getr regs1 4 = w64 (as_tp B) /\
getr regs1 8 = w64 (mv_sp v) /\ getr regs1 9 = w64 (mf_s1 (mv_sp v)) /\
getr regs1 18 = w64 SHADOW_OFF /\ getr regs1 19 = w64 0x20 /\ getr regs1 25 = w64 MF_BLANK /\
getr regs1 26 = w64 (SHADOW_OFF + frame_addr lyc 1 pos / 8).
(* the registers the release and the return need, all set before the empty-text test 0x86060: mf_regs_at without
   s3 and s9 *)
Definition mf_regs_ex (v : mfv) (lyc : alayout) (pos : Z) (regs1 : bvmap 5 word) : Prop :=
getr regs1 2 = w64 (mf_s1 (mv_sp v)) /\ getr regs1 3 = w64 (as_gp B) /\ getr regs1 4 = w64 (as_tp B) /\
getr regs1 8 = w64 (mv_sp v) /\ getr regs1 9 = w64 (mf_s1 (mv_sp v)) /\
getr regs1 18 = w64 SHADOW_OFF /\ getr regs1 26 = w64 (SHADOW_OFF + frame_addr lyc 1 pos / 8).
Lemma mf_regs_ex_of_at : forall v lyc pos regs1, mf_regs_at v lyc pos regs1 -> mf_regs_ex v lyc pos regs1.
Proof. intros v lyc pos regs1 (R2 & R3 & R4 & R8 & R9 & R18 & _ & _ & R26). repeat split; assumption. Qed.

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

(* 0x860d0, the head (plain H_MF_HEAD n): s11 = p, s5 = c, s6 = line (the lines consumed), s8 = FAKE; the text left
   is nonempty and shorter than n bytes *)
Definition MF_HEAD_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (cur : option nat) (line p : Z) (rest : list Z),
mf_cx v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc -> mf_cells v lyc pos memc Wc cur -> mf_regs_at v lyc pos regs1 ->
getr regs1 24 = w64 (frame_addr lyc 1 pos) ->
(length rest < n)%nat -> rest <> [] -> mf_loop v Wc memc mcc cur line p rest ->
fst (m_lines (mcc, cur) line (lines rest)) = mf_final v ->
getr regs1 27 = w64 p -> getr regs1 21 = w64 (mv_c v) -> getr regs1 22 = w64 line ->
mf_at v Wc regs1 memc mdc MF_HEAD.

(* 0x86cf8, the tail (plain H_MF_TAIL n): a7 = p (the text after the line, possibly empty), s5 = c, s6 = line,
   s8 = FAKE *)
Definition MF_TAIL_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (cur : option nat) (line p : Z) (rest : list Z),
mf_cx v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc -> mf_cells v lyc pos memc Wc cur -> mf_regs_at v lyc pos regs1 ->
getr regs1 24 = w64 (frame_addr lyc 1 pos) ->
(length rest < n)%nat -> mf_loop v Wc memc mcc cur line p rest ->
fst (m_lines (mcc, cur) line (lines rest)) = mf_final v ->
getr regs1 17 = w64 p -> getr regs1 21 = w64 (mv_c v) -> getr regs1 22 = w64 line ->
mf_at v Wc regs1 memc mdc MF_TAIL.

(* 0x86e70, the release and the return (plain H_MF_EXIT): the block holds the final model; s8 = FAKE, s10 =
   shadow(FB) and 112(s1) = FB are what the release reads *)
Definition MF_EXIT_stmt : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos,
mf_cx v -> mf_ls v lyc Sc ->
mf_core v lyc Sc Wc memc mdc pos MF_LOW_OFF (mf_final v) -> mf_regs_ex v lyc pos regs1 ->
getr regs1 24 = w64 (frame_addr lyc 1 pos) ->
mf_at v Wc regs1 memc mdc MF_EXIT.

(* 0x86110, a long line (plain H_MF_LONG n): s11 = p, s7 = the line's end, a7 = the next line's address, s6 =
   line + 1, s5 = c, s8 = FAKE *)
Definition MF_LONG_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (cur : option nat) (line p : Z) (rest : list Z),
mf_cx v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc -> mf_cells v lyc pos memc Wc cur -> mf_regs_at v lyc pos regs1 ->
getr regs1 24 = w64 (frame_addr lyc 1 pos) ->
(length rest <= n)%nat -> rest <> [] -> mf_loop v Wc memc mcc cur line p rest ->
(512 <= length (mf_line rest))%nat ->
mf_fin (m_line (mcc, cur) (line + 1) (mf_line rest)) line rest = mf_final v ->
getr regs1 27 = w64 p -> getr regs1 23 = w64 (p + Z.of_nat (length (mf_line rest))) ->
getr regs1 17 = w64 (mf_next p rest) -> getr regs1 22 = w64 (line + 1) -> getr regs1 21 = w64 (mv_c v) ->
mf_at v Wc regs1 memc mdc MF_LONG.

(* 0x862cc, a header line (plain H_MF_HDR n): the stripped line sl = the bytes [i, j) of the line, its first byte
   '['; s11 = p + i, s7 = p + j, a2 = j - i, a7 = 144(s1) = the next line's address, s6 = line + 1, s5 = c,
   s8 = FAKE *)
Definition MF_HDR_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (cur : option nat) (line p : Z) (rest : list Z) (i j : nat),
mf_cx v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc -> mf_cells v lyc pos memc Wc cur -> mf_regs_at v lyc pos regs1 ->
getr regs1 24 = w64 (frame_addr lyc 1 pos) ->
(length rest <= n)%nat -> rest <> [] -> mf_loop v Wc memc mcc cur line p rest ->
(length (mf_line rest) < 512)%nat ->
(i < j)%nat -> (j <= length (mf_line rest))%nat ->
slice i j (mf_line rest) = h_strip (h_cut_comment (mf_line rest)) ->
nth i (mf_line rest) 0 = LBR ->
mf_fin (m_header mcc (h_strip (h_cut_comment (mf_line rest))) (line + 1)) line rest = mf_final v ->
getr regs1 27 = w64 (p + Z.of_nat i) -> getr regs1 23 = w64 (p + Z.of_nat j) ->
getr regs1 12 = w64 (Z.of_nat (j - i)) ->
getr regs1 17 = w64 (mf_next p rest) -> mf_np v memc Wc (mf_next p rest) ->
getr regs1 22 = w64 (line + 1) -> getr regs1 21 = w64 (mv_c v) ->
mf_at v Wc regs1 memc mdc MF_HDR.

(* 0x8633c, a key line (plain H_MF_KEY n): as HDR, the first byte not '[' *)
Definition MF_KEY_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (cur : option nat) (line p : Z) (rest : list Z) (i j : nat),
mf_cx v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc -> mf_cells v lyc pos memc Wc cur -> mf_regs_at v lyc pos regs1 ->
getr regs1 24 = w64 (frame_addr lyc 1 pos) ->
(length rest <= n)%nat -> rest <> [] -> mf_loop v Wc memc mcc cur line p rest ->
(length (mf_line rest) < 512)%nat ->
(i < j)%nat -> (j <= length (mf_line rest))%nat ->
slice i j (mf_line rest) = h_strip (h_cut_comment (mf_line rest)) ->
nth i (mf_line rest) 0 <> LBR ->
mf_fin (m_key mcc cur (h_strip (h_cut_comment (mf_line rest))) (line + 1), cur) line rest = mf_final v ->
getr regs1 27 = w64 (p + Z.of_nat i) -> getr regs1 23 = w64 (p + Z.of_nat j) ->
getr regs1 12 = w64 (Z.of_nat (j - i)) ->
getr regs1 17 = w64 (mf_next p rest) -> mf_np v memc Wc (mf_next p rest) ->
getr regs1 22 = w64 (line + 1) -> getr regs1 21 = w64 (mv_c v) ->
mf_at v Wc regs1 memc mdc MF_KEY.

(* 0x86abc, m_find's call (plain H_MF_HFIND n): the name nm = the bytes [o, o + |nm|) of the text left, inside the
   line, 1 <= |nm| <= 15; s5 = the name, s4 = |nm|, s6 = s7 = line + 1, s8 = FAKE; c only in 128(s1), the next
   line's address only in 144(s1) *)
Definition MF_HFIND_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (cur : option nat) (line p : Z) (rest : list Z) (o : nat)
  (nm : list Z),
mf_cx v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc -> mf_cells v lyc pos memc Wc cur -> mf_regs_at v lyc pos regs1 ->
getr regs1 24 = w64 (frame_addr lyc 1 pos) ->
(length rest <= n)%nat -> rest <> [] -> mf_loop v Wc memc mcc cur line p rest ->
(0 < length nm < 16)%nat -> (o + length nm <= length (mf_line rest))%nat ->
firstn (length nm) (skipn o rest) = nm ->
mf_fin (mh_find mcc nm (line + 1)) line rest = mf_final v ->
getr regs1 21 = w64 (p + Z.of_nat o) -> getr regs1 20 = w64 (Z.of_nat (length nm)) ->
getr regs1 22 = w64 (line + 1) -> getr regs1 23 = w64 (line + 1) -> mf_np v memc Wc (mf_next p rest) ->
mf_at v Wc regs1 memc mdc MF_HFIND.

(* the K cuts (plain H_MF_KAT pc missed n): cur = Some gi, the key k = [ok, ok + kl) and the value v = [ov, ov +
   vl) of the text left, both inside the line, the words missed so far; s11 = k, s6 = kl, s5 = v, s4 = vl, s7 = the
   value's end, s8 = line + 1 (FAKE only in 104(s1)); c only in 128(s1), the next line's address only in 144(s1);
   low.i in scope *)
Definition MF_KAT_stmt (pc : Z) (missed : list (list Z)) (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (ok kl ov vl : nat)
  (k vv : list Z),
mf_cx v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core v lyc Sc Wc memc mdc pos MF_LOW_ON mcc -> mf_cells v lyc pos memc Wc (Some gi) ->
mf_regs_at v lyc pos regs1 ->
(length rest <= n)%nat -> rest <> [] -> mf_loop v Wc memc mcc (Some gi) line p rest ->
mk_kv rest ok kl ov vl k vv -> Forall (fun w => ieq k w = false) missed ->
mf_fin (mk_disp mcc gi k vv (line + 1), Some gi) line rest = mf_final v ->
getr regs1 27 = w64 (p + Z.of_nat ok) -> getr regs1 22 = w64 (Z.of_nat kl) ->
getr regs1 21 = w64 (p + Z.of_nat ov) -> getr regs1 20 = w64 (Z.of_nat vl) ->
getr regs1 23 = w64 (p + Z.of_nat (ov + vl)) -> getr regs1 24 = w64 (line + 1) ->
mf_np v memc Wc (mf_next p rest) ->
mf_at v Wc regs1 memc mdc pc.
(* 0x86684 (no word missed), 0x867b8 ("role" missed), 0x8693c ("model" too), 0x86b20 ("ignore" too) *)
Definition MF_KDISP_stmt (n : nat) : Prop := MF_KAT_stmt MF_KDISP [] n.
Definition MF_KMODEL_stmt (n : nat) : Prop := MF_KAT_stmt MF_KMODEL [S_role] n.
Definition MF_KIGN_stmt (n : nat) : Prop := MF_KAT_stmt MF_KIGN [S_role; S_model] n.
Definition MF_KKNOCK_stmt (n : nat) : Prop := MF_KAT_stmt MF_KKNOCK [S_role; S_model; S_ignore] n.

(* 0x86cd0, m_key's common end (ASan only): the line is done, the state is the tail's with the next line's address
   p only in 144(s1) and low.i still in scope; s5 = c, s6 = line (the lines consumed), s8 = FAKE *)
Definition MF_KDONE_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (cur : option nat) (line p : Z) (rest : list Z),
mf_cx v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core v lyc Sc Wc memc mdc pos MF_LOW_ON mcc -> mf_cells v lyc pos memc Wc cur -> mf_regs_at v lyc pos regs1 ->
getr regs1 24 = w64 (frame_addr lyc 1 pos) ->
(length rest < n)%nat -> mf_loop v Wc memc mcc cur line p rest ->
fst (m_lines (mcc, cur) line (lines rest)) = mf_final v ->
mf_np v memc Wc p -> getr regs1 21 = w64 (mv_c v) -> getr regs1 22 = w64 line ->
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
End e.
End f.
End d.

(* ============================ the segments and how they chain ============================ *)
(* Each cut at every FP state (a cut is reached at the FP state the last snprintf call returned), and one
   S_MF_<piece> per segment of MF-CUTS-A.md section 4: `<its exit cuts> -> <its entry cut>`. The pieces' code and
   callees are listed there (S_MF_ENTRY 141 instructions, FRONT 113, LONGP 40, HDRA 142, HDRB 113, KEYA 146,
   KROLE 130, KMOD 76, KIGNP 100, KKNOCKP 43, KDONE 10, TAIL 13, EXIT 57). *)
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

(* S_MF_ENTRY: the prologue, the side-stack frame, snprintf of c->reading, gen++, *text = 0 to EXIT, the set-up *)
Definition S_MF_ENTRY : Prop := (forall n, MF_HEAD_F n) -> MF_EXIT_F -> MF_ENTRY_F.
(* S_MF_FRONT: strchr / strlen, the long-line test, the comment cut, the strip, the '[' test; an empty line to TAIL *)
Definition S_MF_FRONT : Prop :=
forall n, MF_TAIL_F n -> MF_LONG_F n -> MF_HDR_F n -> MF_KEY_F n -> MF_HEAD_F (S n).
(* S_MF_LONGP: the blank skip, cur = NULL on '[', m_refuse *)
Definition S_MF_LONGP : Prop := forall n, MF_TAIL_F n -> MF_LONG_F n.
(* S_MF_HDRA: memchr ']', the strips, ieq "segment", the name checks; the refusals to TAIL *)
Definition S_MF_HDRA : Prop := forall n, MF_TAIL_F n -> MF_HFIND_F n -> MF_HDR_F n.
(* S_MF_HDRB: m_find; found: the gen test, m_refuse; new: n < 32, memset, memcpy; full: overflow++, m_refuse *)
Definition S_MF_HDRB : Prop := forall n, MF_TAIL_F n -> MF_HFIND_F n.
(* S_MF_KEYA: memchr '=', cur = NULL or no '=' refused, the key and value strips, the quotes, low.i in scope *)
Definition S_MF_KEYA : Prop := forall n, MF_TAIL_F n -> MF_KDISP_F n -> MF_KEY_F n.
(* S_MF_KROLE: ieq "role", the fold, the words loop (strlen, bcmp), the role stores, snprintf; a miss m_refuse *)
Definition S_MF_KROLE : Prop := forall n, MF_KDONE_F n -> MF_KMODEL_F n -> MF_KDISP_F n.
(* S_MF_KMOD: ieq "model", the fold, fuzz_catalogue_row, memcpy into g->model; NULL m_refuse *)
Definition S_MF_KMOD : Prop := forall n, MF_KDONE_F n -> MF_KIGN_F n -> MF_KMODEL_F n.
(* S_MF_KIGNP: ieq "ignore", the six value words, the ignore stores, snprintf; a bad value m_refuse *)
Definition S_MF_KIGNP : Prop := forall n, MF_KDONE_F n -> MF_KKNOCK_F n -> MF_KIGN_F n.
(* S_MF_KKNOCKP: ieq "knock", kept_knock[n_kept] = 1, m_refuse; an unknown key m_refuse *)
Definition S_MF_KKNOCKP : Prop := forall n, MF_KDONE_F n -> MF_KKNOCK_F n.
(* S_MF_KDONE: a7 = 144(s1), low.i out of scope again *)
Definition S_MF_KDONE : Prop := forall n, MF_TAIL_F n -> MF_KDONE_F n.
(* S_MF_TAIL: the check of *p, `bnez` back to HEAD, else EXIT *)
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
