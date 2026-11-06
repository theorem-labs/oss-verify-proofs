(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): the walk-internal piece statements of
   reac_segconf_parse_file (0x87a78, 4908 bytes, 1227 instructions; reac_segconf.c:120-296). Statement text only:
   no segment and no walk is proved here, and pf_pieces_give_contract (the whole function from its 15 segments)
   is stated, not proved. By the G3 walk owner, 2026-10-30. The image-A owner ruled (15:57Z) that these
   statements are walk-internal (they name image A's pcs) and not shared contracts.

   THE FORM. fuzz_command's released segment form (origin/ossv/recipes 501c0d516c69, proofs/plugin-hostd/
   fuzz_command/lib/A/Prog/): a bundle of the contract's variables (check_reply_m.v crv), the state at each cut as
   a predicate over the machine state (chain_words_d.v INV_K* / cw_fi, check_round_trip.v crt_J / crt_fr /
   crt_regs / crt_slots for the class-5 frame), and per cut "from this state the walk reaches the post"
   (chain_words_d.v cw_from, check_reply_m.v CR_*_stmt). Each segment statement S_A<k> says: its exit cuts
   imply its entry cut(s) (continuation form, chain_words_d.v cw_S*P). The exit cuts are taken at EVERY FP state
   (`HA_<CUT>`), because snprintf (7 sites) and refuse (11 sites, vsnprintf inside) return at another FP state
   (apost_baseF's relation; the segment lifts with PaFx's srr_apost_baseF_lift, as check_reply_s4.v does); the
   entry cut is at the ambient FP state.
   The functional invariant is the plain one, by Require of lib/Prog/pf_pieces_spec.v (pf_line, pf_next,
   pf_tline, pf_lctx, pf_cnt, pf_cur_ptr, pf_cur_ok, pf_inb, pf_prov_mid / pf_prov_fin, pf_role_step, pf_start):
   the plain H_* names are kept where the meaning is the same (H_HEAD, H_TAIL, H_LONG, H_HDR, H_KEY, H_ROLE,
   H_MODEL, H_IGN, H_INTENT, H_DONE, H_ENTRY); the loop is by the plain measure n, a bound on the text left.

   SOURCES. Machine code: the excerpts in the unit's internal record, commit dfb49d6ad789, path
   records/segp/dis/, reac_segconf_parse_file.fuzz_segconf.asan.s
   and g3.asan.ann.txt (every register / slot / shadow conjunct below cites the pc that sets it). Cut plan:
   the unit's internal record, commit dfb49d6ad789, path records/segp/plans/PLAN-pf-asan.md
   (section 1 frames, 2 the 41 checks, 3 the 56 calls, 4.2 the 15-segment cover, re-checked
   by script against the excerpt: 1227 instructions, no gap, no overlap, the per-segment instruction, check and
   call counts of the plan's table). Two corrections to the plan found while stating: (1) s9 is `at` only up to
   0x87f3c (`addi s9, zero, 9`): at HDR / KEY s9 = 9 and s4 = 0x20 (0x87ea8), the blanks body[7] is compared with
   (0x88308-0x8830c), and cur is in slot 0xb0 (0x87e7c); plan section 5 item 3 says s9 = at at every mid-line cut.
   (2) the text-NULL return DONE0 (0x88be4) is not a cut: reader_pre gives t <> 0, so `beqz s9, 0x88be4` at
   0x87d1c is decided and 0x88be4..0x88bf4 (check #41) is dead, as is the real-stack fallback 0x87b08-0x87b20
   (the kit's astack_malloc_realizes returns the frame; the use-after-return flag is AR's constant 1) and the
   inline release 0x88c18-0x88c20 (slot 0x88 holds the frame, not 0).

   THE CUTS (pc = BASE + PF_<CUT>; segment that owns the cut's code; who enters it):
     ENTRY  0x87a78 A1  the contract            FTAKEN 0x87b24 A2  A1 (frame taken, `bnez a0`)
     FRAME  0x87cc4 A3  A2 (shadow laid)        DONE   0x88bb8 A4  A3 (empty text), A5 (tail `*p == 0`)
     HEAD   0x87ddc A5  A3, A5's tail           TAIL   0x88068 A5  A5, A6, A7, A8b, A9, A10b, A11b
     LONG   0x87e2c A6  A5 (len >= 512)         REF3   0x87e74 A6  A9 (F_neither / F_outside), A6's LONG path
     HDR    0x87f6c A7  A5                      KEY    0x87fac A9  A5
     CLR    0x880fc A7  A8a (F_bound), A7       RS3    0x88100 A7  A12 (F_badignore), A7's CLR path
     SEG    0x887a4 A8a A7                      NEW    0x8890c A8b A8a (no match, n < 32)
     FOUND  0x88964 A8b A8a (strcmp == 0)       PROV2  0x889f0 A8b A12 (ignore_file snprintf)
     ROLE   0x881d4 A10a A9                     MODEL  0x8826c A11a A9
     IGN    0x88364 A12 A9                      INTENT 0x88450 A10b A10a
     MISS   0x885a8 A11b A11a (by_token NULL)   LOWOUT 0x88774 A11b A11a (hit), A11b (miss)

   WHAT EVERY CUT FROM FTAKEN ON CARRIES (pf_fi, pf_obj): the journal from the entry with the class-5 frame
   (5, pos) as this call's own frame and 0 events (check_reply_m.v cr_mid; check_round_trip.v crt_J); the
   entry's layout and the entry's state up to st_fs (cr_ls; the side-stack frame is the only state change, the
   callees' posts are sa_noalloc); the 13 saved registers at sp0 - 8 .. sp0 - 0x68 (0x87a80-0x87ab0); the
   frame's flag pointer at F + fs_frame_bytes 5 - 8 (astack_malloc_realizes; __asan_stack_free_5 reads it); the
   rounding mode 0 (reader_pre's sa_frm0; every snprintf / refuse post keeps fcsr or sets frm 0); sp = s1 =
   (sp0 - 0x140) & -32 (0x87a78, 0x87ab8, 0x87abc; the fake path never moves sp), s0 = sp0 (0x87ab4), gp, tp,
   s6 = SHADOW_OFF (0x87ae0, through the GOT word 0xa2a50; overwritten only at 0x88bbc, after DONE); and the
   caller's objects at the cut's reader: the text and the block c (bytes, shadow, live block), the catalogue and
   the 38 literals as sa_cat / sa_lit (pinned: they survive frame_alloc_5 and every call, SegABase sa_pinned),
   the read-only view and the stack-protector cells.
   F = frame_addr ly 5 pos, SH = shadow_addr F (= s11 from 0x87b64), the objects at F + 0x20 cur_name[16],
   F + 0x40 buf[512], F + 0x280 low[64], F + 0x2e0 low146[24], F + 0x320 known[240], F + 0x450 ntok
   (.rodata 0x17667's description string; PLAN section 1.3). The frame's 144 shadow cells per scope: pf_shb. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable SegSyms SegList SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase refuse_c
  reac_segconf_parse_file_c SegInstA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(** ** The cut pcs, as listing offsets (BASE + AF_reac_segconf_parse_file = 0x87a78, SegList / SegAddr) *)
Definition PF_ENTRY : Z := AF_reac_segconf_parse_file.            (* 0x87a78 *)
Definition PF_FTAKEN : Z := AF_reac_segconf_parse_file + 0xac.    (* 0x87b24 *)
Definition PF_FRAME : Z := AF_reac_segconf_parse_file + 0x24c.    (* 0x87cc4 *)
Definition PF_HEAD : Z := AF_reac_segconf_parse_file + 0x364.     (* 0x87ddc *)
Definition PF_LONG : Z := AF_reac_segconf_parse_file + 0x3b4.     (* 0x87e2c *)
Definition PF_REF3 : Z := AF_reac_segconf_parse_file + 0x3fc.     (* 0x87e74 *)
Definition PF_HDR : Z := AF_reac_segconf_parse_file + 0x4f4.      (* 0x87f6c *)
Definition PF_KEY : Z := AF_reac_segconf_parse_file + 0x534.      (* 0x87fac *)
Definition PF_TAIL : Z := AF_reac_segconf_parse_file + 0x5f0.     (* 0x88068 *)
Definition PF_CLR : Z := AF_reac_segconf_parse_file + 0x684.      (* 0x880fc *)
Definition PF_RS3 : Z := AF_reac_segconf_parse_file + 0x688.      (* 0x88100 *)
Definition PF_ROLE : Z := AF_reac_segconf_parse_file + 0x75c.     (* 0x881d4 *)
Definition PF_MODEL : Z := AF_reac_segconf_parse_file + 0x7f4.    (* 0x8826c *)
Definition PF_IGN : Z := AF_reac_segconf_parse_file + 0x8ec.      (* 0x88364 *)
Definition PF_INTENT : Z := AF_reac_segconf_parse_file + 0x9d8.   (* 0x88450 *)
Definition PF_MISS : Z := AF_reac_segconf_parse_file + 0xb30.     (* 0x885a8 *)
Definition PF_LOWOUT : Z := AF_reac_segconf_parse_file + 0xcfc.   (* 0x88774 *)
Definition PF_SEG : Z := AF_reac_segconf_parse_file + 0xd2c.      (* 0x887a4 *)
Definition PF_NEW : Z := AF_reac_segconf_parse_file + 0xe94.      (* 0x8890c *)
Definition PF_FOUND : Z := AF_reac_segconf_parse_file + 0xeec.    (* 0x88964 *)
Definition PF_PROV2 : Z := AF_reac_segconf_parse_file + 0xf78.    (* 0x889f0 *)
Definition PF_DONE : Z := AF_reac_segconf_parse_file + 0x1140.    (* 0x88bb8 *)

(** ** The class-5 frame's objects (offsets from F; .rodata 0x17667, PLAN section 1.3) *)
Definition PF_O_CN : Z := 0x20.      (* cur_name[16], R:127 *)
Definition PF_O_BUF : Z := 0x40.     (* buf[512], R:142 *)
Definition PF_O_LOW : Z := 0x280.    (* role low[64], R:234 *)
Definition PF_O_L146 : Z := 0x2e0.   (* model low[24], R:252 *)
Definition PF_O_KNOWN : Z := 0x320.  (* known[240], R:258 *)
Definition PF_O_NTOK : Z := 0x450.   (* ntok, R:259 *)

(** ** The frame's shadow, cell by cell (PLAN sections 1.3 and 1.4)
    Cell i is the shadow byte of F + 8 i. The entry lays all 144 cells (0x87b68-0x87cbc inline, 0x87b94
    meta_fill_f8 for buf's 64): 0xf1 left redzone (cells 0-3, a0 = -0xf at 0x87b60), 0xf2 middle redzones
    (s2 = -0xe at 0x87b40), 0xf3 right redzone (cells 0x8b-0x8f, a0 = -0xd at 0x87c98), 0xf8 an object out of
    scope (s5 = -8 at 0x87b44). An object in scope has cells 0x00. The scope events after the entry:
    cur_name in at 0x87d38-0x87d3c (out at 0x88bd4, in A4); buf in at 0x87e20 (meta_fill_00, every line before
    the length test), out at 0x88070 (meta_fill_f8, the tail; TAIL 0x88068 is two instructions before it);
    low in at 0x881d4-0x881f0, out at 0x88894-0x888b0; low146 in at 0x8826c-0x88274, out at 0x88774-0x8877c;
    known and ntok in at 0x885ac-0x88624, out at 0x886f0-0x88768. *)
Record pf_scope := PFSc { sc_cn : bool; sc_buf : bool; sc_low : bool; sc_l146 : bool; sc_known : bool }.
Definition pf_io (b : bool) : Z := if b then 0 else 0xf8.
Definition pf_shb (sc : pf_scope) (i : Z) : Z :=
  if i <? 4 then 0xf1                              (* 0x00-0x03 left redzone *)
  else if i <? 6 then pf_io (sc_cn sc)             (* 0x04-0x05 cur_name *)
  else if i <? 8 then 0xf2                         (* 0x06-0x07 *)
  else if i <? 72 then pf_io (sc_buf sc)           (* 0x08-0x47 buf *)
  else if i <? 80 then 0xf2                        (* 0x48-0x4f *)
  else if i <? 88 then pf_io (sc_low sc)           (* 0x50-0x57 low *)
  else if i <? 92 then 0xf2                        (* 0x58-0x5b *)
  else if i <? 95 then pf_io (sc_l146 sc)          (* 0x5c-0x5e low146 *)
  else if i <? 100 then 0xf2                       (* 0x5f-0x63 *)
  else if i <? 130 then pf_io (sc_known sc)        (* 0x64-0x81 known *)
  else if i <? 138 then 0xf2                       (* 0x82-0x89 *)
  else if i <? 139 then pf_io (sc_known sc)        (* 0x8a ntok, with known *)
  else 0xf3.                                       (* 0x8b-0x8f right redzone *)
(* FRAME: all out; HEAD and DONE: cur_name in; inside a line (and TAIL): cur_name, buf; INTENT: and low;
   MISS / LOWOUT: and low146 *)
Definition PF_SC0 : pf_scope := PFSc false false false false false.
Definition PF_SC_HEAD : pf_scope := PFSc true false false false false.
Definition PF_SC_LINE : pf_scope := PFSc true true false false false.
Definition PF_SC_LOW : pf_scope := PFSc true true true false false.
Definition PF_SC_L146 : pf_scope := PFSc true true false true false.

(** ** Register, slot and shadow forms (check_round_trip.v crt_regs / crt_slots / crt_frame) *)
(* the registers the prologue saves, slot j at sp0 - 8 - 8 j: ra, s0, s1, s2 .. s11 (0x87a80-0x87ab0) *)
Definition PF_SAVED : list Z := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition pf_rg (rX : bvmap 5 word) (L : list (Z * Z)) : Prop :=
  Forall (fun rv => getr rX (Z_to_bv 5 (fst rv)) = w64 (snd rv)) L.
Definition pf_sl (rd : reader) (b : Z) (L : list (Z * Z)) : Prop :=
  Forall (fun ov => rdword rd (b + fst ov) = Some (snd ov)) L.
Definition pf_saved (rd : reader) (sp0 : Z) (regs : bvmap 5 word) : Prop :=
  forall j r, nth_error PF_SAVED j = Some r ->
  rdword rd (sp0 - 8 - 8 * Z.of_nat j) = Some (bv_unsigned (getr regs (Z_to_bv 5 r))).
Definition pf_fsh (rd : reader) (sh : Z) (sc : pf_scope) : Prop :=
  forall i, 0 <= i < 144 -> rd (sh + i) = Some (pf_shb sc i).
(* cur_name holds the C string nm (seg_spec.cstr_enc; the plain pf_nm_at) *)
Definition pf_nm (rd : reader) (a : Z) (nm : list Z) : Prop :=
  exists f, sa_bytes rd a f /\ seg_spec.cstr_enc 16 nm f.

(** ** The tail of the header step (r_header from seg_get on, SegModel R:197-211): the state after an accepted
    name; SEG, NEW and FOUND state their post with it (A7 rewrites r_header to it under the header's tests). *)
Definition pf_seg_step (c : rconf) (nm : list Z) (ln : Z) (name : list Z) : rconf * option nat * list Z :=
  match seg_get c name with
  | (c1, None) => (refuse c1 ln F_bound [AS name; AI 32], None, nm)
  | (c1, Some (i, is_new)) =>
    let c2 := if negb is_new && (rs_seen_gen (nth i (rc_seg c1) rseg_d) =? rc_gen c1)
              then refuse c1 ln F_twice [AS name] else c1 in
    (r_upd c2 i (rs_with_gen (rc_gen c2)), Some i, snprintf_s 16 F_s [AS name])
  end.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the variables of reac_segconf_parse_file_contract (lib/A/Prog/reac_segconf_parse_file_c.v) *)
Record pfv := mkPFV {
  p_ly : alayout; p_S : astate; p_W : world SEGS; p_regs : bvmap 5 word; p_mem : word -> option byte;
  p_md : Model; p_ch : list (Z * Z * Z); p_c : Z; p_t : Z; p_lp : Z; p_rcs : rconf; p_s : list Z;
  p_lab : option (list Z) }.
(* the entry sp; s1 = the realigned locals base (0x87a78 addi sp,sp,-0x140; 0x87ab8 andi sp,sp,-0x20) *)
Definition pf_sp0 (v : pfv) : Z := spZ (p_regs v).
Definition pf_s1 (v : pfv) : Z := (pf_sp0 v - 0x140) - (pf_sp0 v - 0x140) mod 32.
(* the class-5 frame F (frame_alloc_5's a0, 0x87af0), its flag cell, its shadow SH (s11, 0x87b3c / 0x87b64) *)
Definition pf_F (v : pfv) (pos : Z) : Z := frame_addr (p_ly v) 5 pos.
Definition pf_FL (v : pfv) (pos : Z) : Z := flag_addr (p_ly v) 5 pos.
Definition pf_SH (v : pfv) (pos : Z) : Z := shadow_addr (pf_F v pos).
(* the text's bytes and NUL *)
Definition pf_len (v : pfv) : Z := Z.of_nat (length (p_s v)) + 1.

Section e.
Variable B : asyms.

(** *** The entry, the post *)
(* reac_segconf_parse_file_contract's premises at image A (SegInstA.v's values; A = BASE + AF_<F>). The SAME Prop
   at every FP state: reac_segconf_parse_file_pre's only FP conjunct is reader_pre's sa_frm0 (the entry's
   rounding mode), so it is held at SOME FP state fe (the entry's), and each cut carries the rounding mode of its
   own FP state in pf_fi. A segment that calls snprintf / refuse thus hands pf_cx v on unchanged to the cut it
   reaches at the callee's FP state (the cross_check walk met the FP-bound form of this premise in cross_check's
   loop). *)
Definition pf_cx (v : pfv) : Prop :=
  afn_pre SEGS B STK_reac_segconf_parse_file (p_ly v) (p_S v) (p_W v) (p_regs v) (p_mem v) (p_md v) (p_ch v) /\
  arodata_okP SEGS RLO_A RHI_A B (rdW (p_W v) (p_mem v)) /\
  getr (p_regs v) 10 = w64 (p_c v) /\ 0 <= p_c v < 2 ^ 64 /\
  getr (p_regs v) 11 = w64 (p_t v) /\ 0 <= p_t v < 2 ^ 64 /\
  getr (p_regs v) 12 = w64 (p_lp v) /\ 0 <= p_lp v < 2 ^ 64 /\
  (exists fe : YK11.FPState,
     reac_segconf_parse_file_pre (fx := fe) SEGS B seg_litA_rc catA gotwA guardA (p_ly v) (p_S v)
       (rdW (p_W v) (p_mem v)) (p_c v) (p_t v) (p_lp v) (p_rcs v) (p_s v) (p_lab v)) /\
  sa_room_n 2 (p_S v) /\
  st_nev (p_S v) + EV_reac_segconf_parse_file <= EV_MAX.
(* the contract's post *)
Definition PF_POST (v : pfv) : world SEGS -> config -> Prop :=
  apost_baseF SEGS B STK_reac_segconf_parse_file (seg_spec.RC_PARSE_W (p_c v)) (p_regs v) (p_ly v) (p_S v)
    (p_W v) (p_mem v) (p_md v) EV_reac_segconf_parse_file
    (fun ly' S' W' regs' mem' md' =>
     getr regs' 10 = w64 (snd (SegModel.r_parse_file (p_rcs v) (p_s v) (p_lab v))) /\
     sa_rconf (rdW W' mem') (p_c v) (fst (SegModel.r_parse_file (p_rcs v) (p_s v) (p_lab v))) /\
     sa_noalloc B (p_ly v) (p_S v) ly' S').
(* the same post for a final state cf of the block (the plain pf_ret): a0 = c->n = the number of entries, c
   holds cf. PF_POST v is PF_POSTr v (fst (r_parse_file ..)) once r_parse_file's let is destructed. *)
Definition PF_POSTr (v : pfv) (cf : rconf) : world SEGS -> config -> Prop :=
  apost_baseF SEGS B STK_reac_segconf_parse_file (seg_spec.RC_PARSE_W (p_c v)) (p_regs v) (p_ly v) (p_S v)
    (p_W v) (p_mem v) (p_md v) EV_reac_segconf_parse_file
    (fun ly' S' W' regs' mem' md' =>
     getr regs' 10 = w64 (Z.of_nat (length (rc_seg cf))) /\ sa_rconf (rdW W' mem') (p_c v) cf /\
     sa_noalloc B (p_ly v) (p_S v) ly' S').

(** *** The parts every cut after the frame take shares *)
(* the frame part (see the head comment): journal, layout and state, live blocks, saved registers, flag
   pointer, rounding mode, sp / gp / tp / s0 / s1 / s6 *)
Definition pf_fi (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (rX : bvmap 5 word)
  (memc : word -> option byte) (mdc : Model) : Prop :=
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v)
    (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc mdc 0 /\
  lyc = p_ly v /\ (exists f, Sc = set_fs f (p_S v)) /\
  Permutation (ablocks B lyc Sc) (ablocks B (p_ly v) (p_S v)) /\
  pf_saved (rdW Wc memc) (pf_sp0 v) (p_regs v) /\
  rdword (rdW Wc memc) (pf_F v pos + fs_frame_bytes 5 - 8) = Some (pf_FL v pos) /\
  sa_frm0 /\
  pf_rg rX [(2, pf_s1 v); (3, as_gp B); (4, as_tp B); (8, pf_sp0 v); (9, pf_s1 v); (22, SHADOW_OFF)].
(* the caller's objects at the cut's reader rd: the text (strchr / strlen / strspn / memcpy and checks #2, #3,
   #12), the block c (every c / cur / seg[i] check), the catalogue (#28, reac_box_catalogue[_by_token]), the
   literals (every interceptor / refuse format), the read-only view (rt_rom_view), printf's guard cells *)
Definition pf_obj (v : pfv) (lyc : alayout) (Sc : astate) (rd : reader) : Prop :=
  sa_str rd (p_t v) (p_s v) /\ sa_addr rd (p_t v) (pf_len v) /\ sa_heap B lyc Sc (p_t v) (pf_len v) /\
  sa_addr rd (p_c v) seg_spec.SEG_C_SIZE /\ sa_heap B lyc Sc (p_c v) seg_spec.SEG_C_SIZE /\
  sa_cat SEGS B rd catA /\ (forall x, In x PARSE_FILE_LITS -> sa_lit SEGS B rd (seg_litA_rc x) x) /\
  arodata_okP SEGS RLO_A RHI_A B rd /\ sa_ssp rd gotwA guardA.
(* the label, which the snprintf of 0x87ce8 reads (FTAKEN and FRAME only): where it lies (the contract's
   three places) and its bytes' shadow at rd; its addressability at every AR state in the image case stays in
   pf_cx (reac_segconf_parse_file_pre) *)
Definition pf_lab (v : pfv) (lyc : alayout) (Sc : astate) (rd : reader) : Prop :=
  sa_ostr rd (p_lp v) (p_lab v) /\
  match p_lab v with
  | Some l =>
      (sa_heap B lyc Sc (p_lp v) (Z.of_nat (length l) + 1) \/ sa_fframe lyc Sc (p_lp v) (Z.of_nat (length l) + 1) \/
       sa_img SEGS B (p_lp v) (Z.of_nat (length l) + 1)) /\
      sa_addr rd (p_lp v) (Z.of_nat (length l) + 1)
  | None => True
  end.
(* the spine's state at a cut (the plain pf_state): c holds cf, cur is an entry of it, cur_name holds nm, and
   the counters have room for the k text bytes left *)
Definition pf_st (v : pfv) (pos : Z) (rd : reader) (cf : rconf) (cur : option nat) (nm : list Z) (k : nat)
  : Prop :=
  sa_rconf rd (p_c v) cf /\ pf_cur_ok cf cur /\ pf_nm rd (pf_F v pos + PF_O_CN) nm /\ pf_cnt cf k.
(* the same where cur is dead (after a header's name: SEG, NEW, FOUND) or not yet the step's (CLR) *)
Definition pf_st0 (v : pfv) (pos : Z) (rd : reader) (cf : rconf) (nm : list Z) (k : nat) : Prop :=
  sa_rconf rd (p_c v) cf /\ pf_nm rd (pf_F v pos + PF_O_CN) nm /\ pf_cnt cf k.
(* the loop's constant registers (PLAN section 4.3, and the write list of each register): s2 = '#' (0x87dbc;
   strip_comment's mark), s3 = SH + 8 (0x87d18, buf's first shadow cell: meta_fill's a0 at 0x87e1c / 0x8806c),
   s8 = c (0x87ac8), s11 = SH. s3 and s8 are borrowed in some branches; each cut below lists them only where
   they hold. *)
Definition PF_RL (v : pfv) (pos : Z) : list (Z * Z) :=
  [(18, 0x23); (19, pf_SH v pos + 8); (24, p_c v); (27, pf_SH v pos)].
(* inside a line that starts at o: s5 = p' = t + pf_next s o (0x87de8-0x87e10, the next line), s10 = lineno =
   ln + 1 (0x87e14, addiw; ln + 1 <= 65536) *)
Definition PF_RM (v : pfv) (o : nat) (ln : Z) : list (Z * Z) :=
  [(21, p_t v + Z.of_nat (pf_next (p_s v) o)); (26, ln + 1)].
(* the 19 spill slots s1 + N the setup writes (0x87b24 .. 0x87dd8) and no line changes (PLAN section 1.1; the
   loop's slot writes are only 0xb0 at 0x87e7c / 0x887ac and 0x18 at 0x885a8); 0xd0 is dead and left out *)
Definition PF_SL (v : pfv) (pos : Z) : list (Z * Z) :=
  [(0x20, p_c v + seg_spec.RC_OVERFLOW);                     (* 0x87dc4, read 0x887f8 *)
   (0x28, p_c v + seg_spec.RS_SEEN_GEN);                     (* 0x87db0 &seg[0].seen_gen, read 0x887c4 *)
   (0x30, pf_F v pos + PF_O_L146);                           (* 0x87d98, read 0x8828c *)
   (0x38, shadow_addr (p_c v + seg_spec.RC_GEN));            (* 0x87d20, read 0x88974 / 0x889b0 *)
   (0x40, p_c v + seg_spec.RC_GEN);                          (* 0x87d2c *)
   (0x48, pf_F v pos + PF_O_LOW);                            (* 0x87d90, read 0x88208 *)
   (0x50, pf_F v pos + PF_O_CN);                             (* 0x87d44 *)
   (0x58, p_c v + seg_spec.RC_READING);                      (* 0x87d28 *)
   (0x60, (p_c v + seg_spec.RC_N) / 8);                      (* 0x87d6c, read 0x887a4 / 0x88bb8 *)
   (0x68, pf_F v pos);                                       (* 0x87d30, read 0x87d80 / 0x88bdc *)
   (0x70, pf_F v pos + PF_O_NTOK);                           (* 0x87da8 *)
   (0x78, pf_F v pos + PF_O_KNOWN);                          (* 0x87da0 *)
   (0x80, p_c v + seg_spec.RC_N);                            (* 0x87d24 *)
   (0x88, pf_F v pos);                                       (* 0x87b24 frame_alloc_5's result, read 0x88bf8 *)
   (0x90, p_c v);                                            (* 0x87dd8 *)
   (0x98, pf_SH v pos + 8);                                  (* 0x87b90 *)
   (0xa0, seg_litA_rc F_long);                               (* 0x87dd4 (0x213a0), read 0x87e70 *)
   (0xa8, seg_litA_rc [SP; TAB; CR]);                        (* 0x87dcc (0x21380), read 0x87e30 *)
   (0xb8, pf_F v pos + PF_O_BUF)].                           (* 0x87d88 *)
(* every cut from HEAD on: the entry facts, the frame part, the objects, the slots, the frame's shadow *)
Definition pf_base (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (rX : bvmap 5 word)
  (memc : word -> option byte) (mdc : Model) (sc : pf_scope) : Prop :=
  pf_cx v /\ pf_fi v pos lyc Sc Wc rX memc mdc /\ pf_obj v lyc Sc (rdW Wc memc) /\
  pf_sl (rdW Wc memc) (pf_s1 v) (PF_SL v pos) /\ pf_fsh (rdW Wc memc) (pf_SH v pos) sc.
(* inside a line that starts at o (the plain pf_ctx): o < length s, the rest is at most n bytes, and the
   account at the next line's offset counts this line (lineno = ln + 1) *)
Definition pf_mid (v : pfv) (o : nat) (ln : Z) (d : list (list Z)) (n : nat) : Prop :=
  (o < length (p_s v))%nat /\ (length (skipn o (p_s v)) <= n)%nat /\
  pf_lctx (p_s v) (pf_next (p_s v) o) (ln + 1) d.
(* the post from a state st of the line's step (the plain pf_fin of r_lines st (ln + 1) (lines rest')) *)
Definition pf_postm (v : pfv) (st : rconf * option nat * list Z) (o : nat) (ln : Z) : world SEGS -> config -> Prop :=
  PF_POSTr v (fst (fst (r_lines st (ln + 1) (lines (skipn (pf_next (p_s v) o) (p_s v)))))).
(* a split key line (R:215-223, the plain pf_kv) with key and val C strings in buf *)
Definition pf_kv (rd : reader) (v : pfv) (pos : Z) (line : list Z) (kp vp : Z) (key val : list Z) : Prop :=
  (exists ei : nat, strchr line EQ = Some ei /\ key = r_trim (firstn ei line) /\
                    val = r_unquote (r_trim (skipn (S ei) line))) /\
  sa_str rd kp key /\ pf_inb (pf_F v pos + PF_O_BUF) kp key /\
  sa_str rd vp val /\ pf_inb (pf_F v pos + PF_O_BUF) vp val.
(* the three refusals of the shared refuse call 0x87e74: F_long (from LONG: a3 = 0x1ff at 0x87e64, a2 from slot
   0xa0), F_neither (0x88094-0x880a0: a3 = s7 = line) and F_outside (0x881bc-0x881cc: a3 = s7 = key) *)
Definition pf_ref3 (rd : reader) (v : pfv) (pos : Z) (f : list Z) (fa : Z) (args : list arg) (a3 : Z) : Prop :=
  (f = F_long /\ fa = seg_litA_rc F_long /\ args = [AI 511] /\ a3 = 511) \/
  (exists x, ((f = F_neither /\ fa = seg_litA_rc F_neither) \/ (f = F_outside /\ fa = seg_litA_rc F_outside)) /\
             args = [AS x] /\ sa_str rd a3 x /\ pf_inb (pf_F v pos + PF_O_BUF) a3 x).

(** *** The cuts: the state INV_<CUT>, and H_<CUT>: from that state the walk reaches the post *)

(* ENTRY (0x87a78, A1): the contract over the bundle (check_reply_m.v CR_ENTRY_stmt); sa_frm0 is the ambient FP
   state's rounding mode (the contract's reader_pre conjunct) *)
Definition H_ENTRY : Prop :=
  forall v, pf_cx v -> sa_frm0 ->
  SRr SEGS (p_W v) (cfg_at SEGS (BASE + PF_ENTRY) (p_regs v) (p_mem v) (p_md v)) (PF_POST v).

(* FTAKEN (0x87b24, A2): frame_alloc_5 returned the class-5 frame F (aj_stack_malloc_atS's post: the journal
   with (5, pos) own, the flag pointer, the frame's whole shadow 0), `bnez a0` taken. a0 = s7 = F (0x87b00),
   s8 = c, s9 = t, s3 = label (0x87ac0-0x87ac8), s10 = 0x40e0 (0x87afc, s2 = 0x4000 at 0x87ae4); c untouched. *)
Definition INV_FTAKEN (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (rX : bvmap 5 word)
  (memc : word -> option byte) (mdc : Model) : Prop :=
  pf_cx v /\ pf_fi v pos lyc Sc Wc rX memc mdc /\ pf_obj v lyc Sc (rdW Wc memc) /\ pf_lab v lyc Sc (rdW Wc memc) /\
  sa_rconf (rdW Wc memc) (p_c v) (p_rcs v) /\
  zero_shadow (rdW Wc memc) SHADOW_OFF (pf_F v pos) (fs_frame_bytes 5) /\
  pf_rg rX [(10, pf_F v pos); (23, pf_F v pos); (24, p_c v); (25, p_t v); (19, p_lp v); (26, 0x40e0)].
Definition H_FTAKEN : Prop :=
  forall v pos lyc Sc Wc rX memc mdc, INV_FTAKEN v pos lyc Sc Wc rX memc mdc ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_FTAKEN) rX memc mdc) (PF_POST v).

(* FRAME (0x87cc4, A3): the frame header and the 144 shadow cells laid (0x87b24-0x87cc0), every object out of
   scope; slots 0x88 (F) and 0x98 (SH + 8); s10 = &c->gen (0x87b28), a0 = 0x4080 (0x87cc0; 0x87cc4 is
   `add s5, s8, a0`), s7 = F, s8 = c, s9 = t, s3 = label *)
Definition INV_FRAME (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (rX : bvmap 5 word)
  (memc : word -> option byte) (mdc : Model) : Prop :=
  pf_cx v /\ pf_fi v pos lyc Sc Wc rX memc mdc /\ pf_obj v lyc Sc (rdW Wc memc) /\ pf_lab v lyc Sc (rdW Wc memc) /\
  sa_rconf (rdW Wc memc) (p_c v) (p_rcs v) /\
  pf_sl (rdW Wc memc) (pf_s1 v) [(0x88, pf_F v pos); (0x98, pf_SH v pos + 8)] /\
  pf_fsh (rdW Wc memc) (pf_SH v pos) PF_SC0 /\
  pf_rg rX [(27, pf_SH v pos); (10, 0x4080); (23, pf_F v pos); (24, p_c v); (25, p_t v); (19, p_lp v);
            (26, p_c v + seg_spec.RC_GEN)].
Definition H_FRAME : Prop :=
  forall v pos lyc Sc Wc rX memc mdc, INV_FRAME v pos lyc Sc Wc rX memc mdc ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_FRAME) rX memc mdc) (PF_POST v).

(* DONE (0x88bb8, A4): the loop has ended (A3's empty text, `beqz` 0x87d70; the tail's `*p == 0`, 0x88090).
   A4 reads c->n through slot 0x60 + s6 (#40) and slot 0x80, puts cur_name out of scope (0x88bd4, s11), reloads
   F from slot 0x68, stores the retired magic at F (0x88c04), releases the frame by __asan_stack_free_5
   (0x88c10, a0 = slot 0x88) and returns. Post: the function's post from c's state cf (the plain H_DONE). *)
Definition INV_DONE (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (rX : bvmap 5 word)
  (memc : word -> option byte) (mdc : Model) (cf : rconf) : Prop :=
  pf_cx v /\ pf_fi v pos lyc Sc Wc rX memc mdc /\ pf_obj v lyc Sc (rdW Wc memc) /\
  sa_rconf (rdW Wc memc) (p_c v) cf /\
  pf_sl (rdW Wc memc) (pf_s1 v)
    [(0x60, (p_c v + seg_spec.RC_N) / 8); (0x68, pf_F v pos); (0x80, p_c v + seg_spec.RC_N); (0x88, pf_F v pos)] /\
  pf_fsh (rdW Wc memc) (pf_SH v pos) PF_SC_HEAD /\
  pf_rg rX [(27, pf_SH v pos)].
Definition H_DONE : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf, INV_DONE v pos lyc Sc Wc rX memc mdc cf ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_DONE) rX memc mdc) (PF_POSTr v cf).

(* HEAD (0x87ddc, A5): the line-loop head (the plain H_HEAD). A line starts at o (o < length s), p = s9 =
   t + o (0x87d50 / 0x88088), ln = lineno = s10 lines consumed, cur in s4 (0x87d74 / the tail), c holds cf,
   cur_name holds nm; buf out of scope (0x88070). Post: the function's post from r_lines (cf, cur, nm) ln
   (lines rest), rest = skipn o s; n bounds length rest. *)
Definition INV_HEAD (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (cur : option nat) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) : Prop :=
  pf_base v pos lyc Sc Wc rX memc mdc PF_SC_HEAD /\
  pf_lctx (p_s v) o ln d /\ (o < length (p_s v))%nat /\ (length (skipn o (p_s v)) <= n)%nat /\
  pf_st v pos (rdW Wc memc) cf cur nm (length (skipn o (p_s v))) /\
  pf_rg rX (PF_RL v pos ++ [(25, p_t v + Z.of_nat o); (26, ln); (20, pf_cur_ptr (p_c v) cur)]).
Definition H_HEAD (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf cur nm o ln d, INV_HEAD n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_HEAD) rX memc mdc)
    (PF_POSTr v (fst (fst (r_lines (cf, cur, nm) ln (lines (skipn o (p_s v))))))).

(* TAIL (0x88068, A5): a line has been read (the plain H_TAIL). o is the next line's offset, p' = s5 = t + o;
   s3 = SH + 8 for the meta_fill_f8 at 0x88070, which puts buf out of scope: at TAIL buf is still IN scope.
   The rest is shorter than n: the head it loops to is H_HEAD (pred n). *)
Definition INV_TAIL (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (cur : option nat) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) : Prop :=
  pf_base v pos lyc Sc Wc rX memc mdc PF_SC_LINE /\
  pf_lctx (p_s v) o ln d /\ (length (skipn o (p_s v)) < n)%nat /\
  pf_st v pos (rdW Wc memc) cf cur nm (length (skipn o (p_s v))) /\
  pf_rg rX (PF_RL v pos ++ [(21, p_t v + Z.of_nat o); (26, ln); (20, pf_cur_ptr (p_c v) cur)]).
Definition H_TAIL (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf cur nm o ln d, INV_TAIL n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_TAIL) rX memc mdc)
    (PF_POSTr v (fst (fst (r_lines (cf, cur, nm) ln (lines (skipn o (p_s v))))))).

(* LONG (0x87e2c, A6; `bltu s7, 0x200` at 0x87e28 not taken): at = s9 = t + o, len = s7 (0x87df0 / 0x87e08),
   cur in s4 (not spilled on this path), buf in scope (0x87e20). The step is r_line's long branch. *)
Definition INV_LONG (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (cur : option nat) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) : Prop :=
  pf_base v pos lyc Sc Wc rX memc mdc PF_SC_LINE /\ pf_mid v o ln d n /\
  pf_st v pos (rdW Wc memc) cf cur nm (length (skipn o (p_s v))) /\
  (512 <= length (pf_line (p_s v) o))%nat /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln ++
            [(20, pf_cur_ptr (p_c v) cur); (25, p_t v + Z.of_nat o); (23, Z.of_nat (length (pf_line (p_s v) o)))]).
Definition H_LONG (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf cur nm o ln d, INV_LONG n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_LONG) rX memc mdc)
    (pf_postm v (r_line cf cur nm (ln + 1) (pf_line (p_s v) o)) o ln).

(* REF3 (0x87e74, A6's shared refuse call; entered from LONG's path and from A9 by `j 0x87e74` at 0x881d0):
   refuse(c, lineno, f, a3) with a0 = c, a1 = lineno, a2 = f's literal, a3 per pf_ref3; s4 = the step's cur'
   (the masked cur of 0x87e50-0x87e60, the key line's cur, or NULL), then `j` TAIL (0x87e78). *)
Definition INV_REF3 (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (cur' : option nat)
  (nm : list Z) (o : nat) (ln : Z) (d : list (list Z)) (f : list Z) (fa : Z) (args : list arg) (a3 : Z) : Prop :=
  pf_base v pos lyc Sc Wc rX memc mdc PF_SC_LINE /\ pf_mid v o ln d n /\
  pf_st v pos (rdW Wc memc) cf cur' nm (length (skipn o (p_s v))) /\
  pf_ref3 (rdW Wc memc) v pos f fa args a3 /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln ++
            [(20, pf_cur_ptr (p_c v) cur'); (10, p_c v); (11, ln + 1); (12, fa); (13, a3)]).
Definition H_REF3 (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf cur' nm o ln d f fa args a3,
  INV_REF3 n v pos lyc Sc Wc rX memc mdc cf cur' nm o ln d f fa args a3 ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_REF3) rX memc mdc)
    (pf_postm v (refuse cf (ln + 1) f args, cur', nm) o ln).

(* HDR (0x87f6c, A7): the line (len < 512) copied into buf (0x87e90), its comment cut, trimmed (0x87f44);
   s7 = lp = the trimmed line pf_tline s o in buf, first byte '['; s4 = 0x20 (0x87ea8) and s9 = 9 (0x87f3c),
   body[7]'s two blanks (0x88308-0x8830c); cur in slot 0xb0 (0x87e7c). The step is r_header. *)
Definition INV_HDR (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (cur : option nat) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (lp : Z) : Prop :=
  pf_base v pos lyc Sc Wc rX memc mdc PF_SC_LINE /\ pf_mid v o ln d n /\
  pf_st v pos (rdW Wc memc) cf cur nm (length (skipn o (p_s v))) /\
  pf_sl (rdW Wc memc) (pf_s1 v) [(0xb0, pf_cur_ptr (p_c v) cur)] /\
  (length (pf_line (p_s v) o) < 512)%nat /\
  sa_str (rdW Wc memc) lp (pf_tline (p_s v) o) /\ pf_inb (pf_F v pos + PF_O_BUF) lp (pf_tline (p_s v) o) /\
  hd0 (pf_tline (p_s v) o) = LBR /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln ++ [(20, 0x20); (25, 9); (23, lp)]).
Definition H_HDR (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf cur nm o ln d lp,
  INV_HDR n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d lp ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_HDR) rX memc mdc)
    (pf_postm v (r_header cf nm (ln + 1) (pf_tline (p_s v) o)) o ln).

(* KEY (0x87fac, A9): as HDR, but the trimmed line is neither empty nor a header (0x87f60, 0x87f68). The step
   is r_key. *)
Definition INV_KEY (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (cur : option nat) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (lp : Z) : Prop :=
  pf_base v pos lyc Sc Wc rX memc mdc PF_SC_LINE /\ pf_mid v o ln d n /\
  pf_st v pos (rdW Wc memc) cf cur nm (length (skipn o (p_s v))) /\
  pf_sl (rdW Wc memc) (pf_s1 v) [(0xb0, pf_cur_ptr (p_c v) cur)] /\
  (length (pf_line (p_s v) o) < 512)%nat /\
  sa_str (rdW Wc memc) lp (pf_tline (p_s v) o) /\ pf_inb (pf_F v pos + PF_O_BUF) lp (pf_tline (p_s v) o) /\
  hd0 (pf_tline (p_s v) o) <> 0 /\ hd0 (pf_tline (p_s v) o) <> LBR /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln ++ [(20, 0x20); (25, 9); (23, lp)]).
Definition H_KEY (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf cur nm o ln d lp,
  INV_KEY n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d lp ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_KEY) rX memc mdc)
    (pf_postm v (r_key cf cur nm (ln + 1) (pf_tline (p_s v) o)) o ln).

(* CLR (0x880fc, A7; `mv s4, zero` then RS3): after a header refusal (F_unknown at 0x880f8, F_bound at 0x88834 by
   `j 0x880fc` at 0x88838) c holds cf; the step's cur is NULL. s3 is reloaded at RS3. *)
Definition INV_CLR (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) : Prop :=
  pf_base v pos lyc Sc Wc rX memc mdc PF_SC_LINE /\ pf_mid v o ln d n /\
  pf_st0 v pos (rdW Wc memc) cf nm (length (skipn (pf_next (p_s v) o) (p_s v))) /\
  pf_rg rX ([(18, 0x23); (24, p_c v); (27, pf_SH v pos)] ++ PF_RM v o ln).
Definition H_CLR (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d, INV_CLR n v pos lyc Sc Wc rX memc mdc cf nm o ln d ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_CLR) rX memc mdc) (pf_postm v (cf, None, nm) o ln).

(* RS3 (0x88100, A7; `ld s3, 0x98(s1)`, `j` TAIL): after the bad-ignore refusal (A12, `j 0x88100` at 0x88430;
   cur kept in s4) or from CLR (cur = NULL); c holds cf. *)
Definition INV_RS3 (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (cur' : option nat)
  (nm : list Z) (o : nat) (ln : Z) (d : list (list Z)) : Prop :=
  pf_base v pos lyc Sc Wc rX memc mdc PF_SC_LINE /\ pf_mid v o ln d n /\
  pf_st v pos (rdW Wc memc) cf cur' nm (length (skipn (pf_next (p_s v) o) (p_s v))) /\
  pf_rg rX ([(18, 0x23); (24, p_c v); (27, pf_SH v pos)] ++ PF_RM v o ln ++ [(20, pf_cur_ptr (p_c v) cur')]).
Definition H_RS3 (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf cur' nm o ln d, INV_RS3 n v pos lyc Sc Wc rX memc mdc cf cur' nm o ln d ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_RS3) rX memc mdc) (pf_postm v (cf, cur', nm) o ln).

(* SEG (0x887a4, A8a; `bltu a0, 0x10` at 0x88340 taken): the header's name (1 to 15 bytes) is in buf at np =
   s9 (trim at 0x88310), s3 reloaded (0x8832c). A8a builds sh(&c->n) from slot 0x60 (#29), loads n, runs the
   strcmp search (0x887d0) and the bound test. The post is the header step from seg_get on. *)
Definition INV_SEG (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (np : Z) (name : list Z) : Prop :=
  pf_base v pos lyc Sc Wc rX memc mdc PF_SC_LINE /\ pf_mid v o ln d n /\
  pf_st0 v pos (rdW Wc memc) cf nm (length (skipn o (p_s v))) /\
  sa_str (rdW Wc memc) np name /\ pf_inb (pf_F v pos + PF_O_BUF) np name /\ (1 <= length name <= 15)%nat /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln ++ [(25, np)]).
Definition H_SEG (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d np name,
  INV_SEG n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_SEG) rX memc mdc) (pf_postm v (pf_seg_step cf nm (ln + 1) name) o ln).

(* NEW (0x8890c, A8b; from `blez s3` 0x887cc or `blt s3, 0x20` 0x887f4): no entry has the name and there is
   room; s3 = n (0x887bc), slot 0xb0 = sh(&c->n) (0x887ac, read by #35 at 0x8890c). A8b stores n + 1, memsets
   seg[n] (0x88940), names it (0x88958), then the seen_gen store and cur_name's snprintf (0x889f0). *)
Definition INV_NEW (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (np : Z) (name : list Z) : Prop :=
  pf_base v pos lyc Sc Wc rX memc mdc PF_SC_LINE /\ pf_mid v o ln d n /\
  pf_st0 v pos (rdW Wc memc) cf nm (length (skipn o (p_s v))) /\
  sa_str (rdW Wc memc) np name /\ pf_inb (pf_F v pos + PF_O_BUF) np name /\ (1 <= length name <= 15)%nat /\
  r_find_go (rc_seg cf) name 0 = None /\ (length (rc_seg cf) < 32)%nat /\
  pf_sl (rdW Wc memc) (pf_s1 v) [(0xb0, shadow_addr (p_c v + seg_spec.RC_N))] /\
  pf_rg rX ([(18, 0x23); (27, pf_SH v pos); (19, Z.of_nat (length (rc_seg cf))); (25, np)] ++ PF_RM v o ln).
Definition H_NEW (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d np name,
  INV_NEW n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_NEW) rX memc mdc) (pf_postm v (pf_seg_step cf nm (ln + 1) name) o ln).

(* FOUND (0x88964, A8b; strcmp == 0 at 0x887dc): entry i has the name; s4 = &seg[i], s7 = &seg[i].seen_gen
   (the search's two induction pointers, 0x887e4-0x887e8; #36 tests s7). *)
Definition INV_FOUND (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (np : Z) (name : list Z) (i : nat) : Prop :=
  pf_base v pos lyc Sc Wc rX memc mdc PF_SC_LINE /\ pf_mid v o ln d n /\
  pf_st0 v pos (rdW Wc memc) cf nm (length (skipn o (p_s v))) /\
  sa_str (rdW Wc memc) np name /\ pf_inb (pf_F v pos + PF_O_BUF) np name /\ (1 <= length name <= 15)%nat /\
  r_find_go (rc_seg cf) name 0 = Some i /\
  pf_rg rX ([(18, 0x23); (27, pf_SH v pos); (20, seg_spec.rseg_addr (p_c v) i);
             (23, seg_spec.rseg_addr (p_c v) i + seg_spec.RS_SEEN_GEN); (25, np)] ++ PF_RM v o ln).
Definition H_FOUND (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d np name i,
  INV_FOUND n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name i ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_FOUND) rX memc mdc) (pf_postm v (pf_seg_step cf nm (ln + 1) name) o ln).

(* PROV2 (0x889f0, A8b's shared snprintf; entered from A12 by `j 0x889f0` at 0x88908): the ignore branch has
   stored ignore = b and ignore_set = 1 (#33, #34): c holds pf_prov_mid (PIgn b) cf gi; a0 = &seg[gi].ignore_file,
   a1 = 0x60, a2 = "%s", a3 = c->reading (slot 0x58). snprintf gives pf_prov_fin (PIgn b) cf gi, then TAIL. *)
Definition INV_PROV2 (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (b : bool) (gi : nat) : Prop :=
  pf_base v pos lyc Sc Wc rX memc mdc PF_SC_LINE /\ pf_mid v o ln d n /\
  pf_st v pos (rdW Wc memc) (pf_prov_mid (PIgn b) cf gi) (Some gi) nm (length (skipn (pf_next (p_s v) o) (p_s v))) /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln ++
            [(20, seg_spec.rseg_addr (p_c v) gi); (10, seg_spec.rseg_addr (p_c v) gi + seg_spec.RS_IGNORE_FILE);
             (11, 0x60); (12, seg_litA_rc F_s); (13, p_c v + seg_spec.RC_READING)]).
Definition H_PROV2 (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d b gi, INV_PROV2 n v pos lyc Sc Wc rX memc mdc cf nm o ln d b gi ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_PROV2) rX memc mdc) (pf_postm v (pf_prov_fin (PIgn b) cf gi, Some gi, nm) o ln).

(* ROLE / MODEL / IGN (0x881d4 A10a, 0x8826c A11a, 0x88364 A12; the strcasecmp dispatch 0x88160 / 0x88174 /
   0x88188): the key line is split (pf_kv), s7 = key (0x87fe0), s9 = val (0x87fec / 0x88148), cur = Some gi in
   s4 (0x87fb8; `beqz s4` at 0x8814c not taken) and slot 0xb0, s8 = c (0x88008 / 0x880a4). The step is r_key. *)
Definition INV_KV (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (gi : nat) (kp vp : Z) (key val : list Z) : Prop :=
  pf_base v pos lyc Sc Wc rX memc mdc PF_SC_LINE /\ pf_mid v o ln d n /\
  pf_st v pos (rdW Wc memc) cf (Some gi) nm (length (skipn o (p_s v))) /\
  pf_kv (rdW Wc memc) v pos (pf_tline (p_s v) o) kp vp key val /\
  pf_sl (rdW Wc memc) (pf_s1 v) [(0xb0, seg_spec.rseg_addr (p_c v) gi)] /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln ++ [(20, seg_spec.rseg_addr (p_c v) gi); (23, kp); (25, vp)]).
Definition H_ROLE (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d gi kp vp key val,
  INV_KV n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi kp vp key val ->
  strcasecmp key S_role = 0 ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_ROLE) rX memc mdc)
    (pf_postm v (r_key cf (Some gi) nm (ln + 1) (pf_tline (p_s v) o)) o ln).
Definition H_MODEL (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d gi kp vp key val,
  INV_KV n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi kp vp key val ->
  strcasecmp key S_role <> 0 -> strcasecmp key S_model = 0 ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_MODEL) rX memc mdc)
    (pf_postm v (r_key cf (Some gi) nm (ln + 1) (pf_tline (p_s v) o)) o ln).
Definition H_IGN (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d gi kp vp key val,
  INV_KV n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi kp vp key val ->
  strcasecmp key S_role <> 0 -> strcasecmp key S_model <> 0 -> strcasecmp key S_ignore = 0 ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_IGN) rX memc mdc)
    (pf_postm v (r_key cf (Some gi) nm (ln + 1) (pf_tline (p_s v) o)) o ln).

(* INTENT (0x88450, A10b; after the fold loop and low[k] = 0 at 0x8844c, #25): low (in scope since
   0x881d4-0x881f0) holds the 64 bytes LB with r_low val 0 64 and its NUL first (the plain H_INTENT's O1 form;
   bcmp reads up to 7 of them); s3 = low (0x88208), s9 = val. The step is pf_role_step. *)
Definition INV_INTENT (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (gi : nat) (vp : Z) (val : list Z) : Prop :=
  pf_base v pos lyc Sc Wc rX memc mdc PF_SC_LOW /\ pf_mid v o ln d n /\
  pf_st v pos (rdW Wc memc) cf (Some gi) nm (length (skipn o (p_s v))) /\
  sa_str (rdW Wc memc) vp val /\ pf_inb (pf_F v pos + PF_O_BUF) vp val /\
  (exists LB : list byte, length LB = 64%nat /\ sa_bytes (rdW Wc memc) (pf_F v pos + PF_O_LOW) LB /\
     firstn (S (length (r_low val 0 64))) (seg_spec.zs LB) = r_low val 0 64 ++ [0]) /\
  pf_rg rX ([(18, 0x23); (24, p_c v); (27, pf_SH v pos); (19, pf_F v pos + PF_O_LOW)] ++ PF_RM v o ln ++
            [(20, seg_spec.rseg_addr (p_c v) gi); (25, vp)]).
Definition H_INTENT (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val,
  INV_INTENT n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_INTENT) rX memc mdc) (pf_postm v (pf_role_step cf gi nm (ln + 1) val) o ln).

(* MISS (0x885a8, A11b; reac_box_catalogue_by_token returned NULL, `beqz` at 0x8853c): low146 in scope
   (0x8826c-0x88274), known / ntok out; s9 = val (spilled to slot 0x18 at 0x885a8), cur in slot 0xb0. A11b
   lays known's scope, joins the 11 tokens into known (0x8865c loop, #28), refuses with F_badmodel (0x886e8) and
   falls into LOWOUT. *)
Definition INV_MISS (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (gi : nat) (vp : Z) (val : list Z) : Prop :=
  pf_base v pos lyc Sc Wc rX memc mdc PF_SC_L146 /\ pf_mid v o ln d n /\
  pf_st v pos (rdW Wc memc) cf (Some gi) nm (length (skipn o (p_s v))) /\
  sa_str (rdW Wc memc) vp val /\ pf_inb (pf_F v pos + PF_O_BUF) vp val /\
  by_token (r_low val 0 24) = None /\
  pf_sl (rdW Wc memc) (pf_s1 v) [(0xb0, seg_spec.rseg_addr (p_c v) gi)] /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln ++ [(25, vp)]).
Definition H_MISS (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val,
  INV_MISS n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_MISS) rX memc mdc)
    (pf_postm v (refuse cf (ln + 1) F_badmodel [AS nm; AS val; AS known], Some gi, nm) o ln).

(* LOWOUT (0x88774, A11b; from the hit path `j 0x88774` at 0x8859c, and the miss path's fall-through): the
   model step is done, c holds cf; low146 still in scope (its out-stores begin here), known / ntok out; a0 = -8
   (0x88598 / 0x886ec), s3 = SH + 8, s4 = cur (0x88558 / 0x88770). *)
Definition INV_LOWOUT (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (gi : nat) : Prop :=
  pf_base v pos lyc Sc Wc rX memc mdc PF_SC_L146 /\ pf_mid v o ln d n /\
  pf_st v pos (rdW Wc memc) cf (Some gi) nm (length (skipn (pf_next (p_s v) o) (p_s v))) /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln ++ [(20, seg_spec.rseg_addr (p_c v) gi); (10, -8)]).
Definition H_LOWOUT (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d gi, INV_LOWOUT n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_LOWOUT) rX memc mdc) (pf_postm v (cf, Some gi, nm) o ln).

End e.
End f.
End d.

(** ** The segments (cover and counts: PLAN-pf-asan section 4.2, re-checked against the excerpt)
    Each holds at every ambient FP state (the f0 binder); its exit cuts are taken at every FP state (the HA_
    forms). A statement names no callee: each segment FILE takes, as Section hypotheses, the runtime entries
    and program callees of its own calls, in the texts the contract's head comment names, each at every FP
    state (`forall fx0 : YK11.FPState, ...`). Entries and call targets are LISTING terms (the image-A owner's
    ruling 16:54Z): a runtime entry or trampoline is `pa_sigma SS_<name>` (SegSyms.v), a program callee is
    `BASE + AF_<F>` (its call target `pa_sigma SS_<F>` by seg_sig_prog). The RtSeg rows are the interceptor
    owner's accepted texts (commit 80d098bd1905, lib/A/Rt/RtSeg.v):
      strchr        @RtSeg.astrchr_realizes fx0 rc SEGS B (pa_sigma SS___interceptor_trampoline_strchr)  A5, A7, A9
      strncasecmp   @RtSeg.astrncasecmp_realizes fx0 rc SEGS B
                      (pa_sigma SS___interceptor_trampoline_strncasecmp)                      A7
      strcasecmp    @RtSeg.astrcasecmp_realizes fx0 rc SEGS B
                      (pa_sigma SS___interceptor_trampoline_strcasecmp)                       A9, A12
      strlen        RtString.astrlen_realizes at pa_sigma SS___interceptor_trampoline_strlen (row 16)  A5, A7, A9
      strspn        RtString.astrspn_realizes at pa_sigma SS___interceptor_trampoline_strspn, gotwA, guardA
                      (row 2)                                                                 A6
      strcmp        RtString.astrcmp_realizes at pa_sigma SS___interceptor_trampoline_strcmp (row 17)  A8a
      snprintf      RtFormat.asnprintf_realizes at pa_sigma SS___interceptor_trampoline_snprintf, gotwA, guardA
                      (row 4)                                                                 A3, A8b, A10b, A11a, A11b
      bcmp          the kit's abcmp_realizes (YG0d.v) at pa_sigma SS___interceptor_trampoline_bcmp     A10b
      memcpy        aintrin_realizes OCpy at pa_sigma SS___asan_memcpy (YG0d.v)              A5
      memset        aintrin_realizes OSet at pa_sigma SS___asan_memset                       A3, A8b
      set_shadow    aset_shadow_realizes at pa_sigma SS___asan_set_shadow_f8, 0xf8 (A2, A5) and
                      pa_sigma SS___asan_set_shadow_00, 0x00 (A5; A4's call is dead)
      frame take    astack_malloc_realizes 5 (palf_sm: pa_sigma SS___asan_stack_malloc_5),
                      stack_malloc_progressP                                                  A1
      frame release RtStack.astack_free_cls_realizes at pa_sigma SS___asan_stack_free_5, 5; astack_free_law,
                      frame_flag_lawP                                                         A4
      refuse        refuse_contract at BASE + AF_refuse, STK_refuse, RLO_A, RHI_A, seg_litA_rc, gotwA, guardA
                      A6, A7, A8a, A8b, A9, A10b, A11b, A12
      trim          trim_contract at BASE + AF_trim, STK_trim                               A5, A7, A9
      by_token      reac_box_catalogue_by_token_contract at BASE + AF_reac_box_catalogue_by_token, catA  A11a
      catalogue     reac_box_catalogue_contract at BASE + AF_reac_box_catalogue, catA       A11b
    plus the image facts the walks share (SegInstA's seg_litA_rc_facts / seg_litA_rc_S_base over RC_LITS and
    STK_values; SegObj's seg_val_objs and seg_sig_prog; the walk records of the listing). The walk theorem is at
    BASE + AF_reac_segconf_parse_file (the brief's form); SegInstA's A_reac_segconf_parse_file_A_AF ties it to
    A_reac_segconf_parse_file_A when the closing file pins BASE = seg_text. *)
Section s.
Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
Variable B : asyms.
Definition HA_FTAKEN : Prop := forall f1 : YK11.FPState, H_FTAKEN (fx := f1) B.
Definition HA_FRAME : Prop := forall f1 : YK11.FPState, H_FRAME (fx := f1) B.
Definition HA_DONE : Prop := forall f1 : YK11.FPState, H_DONE (fx := f1) B.
Definition HA_HEAD (n : nat) : Prop := forall f1 : YK11.FPState, H_HEAD (fx := f1) B n.
Definition HA_TAIL (n : nat) : Prop := forall f1 : YK11.FPState, H_TAIL (fx := f1) B n.
Definition HA_LONG (n : nat) : Prop := forall f1 : YK11.FPState, H_LONG (fx := f1) B n.
Definition HA_REF3 (n : nat) : Prop := forall f1 : YK11.FPState, H_REF3 (fx := f1) B n.
Definition HA_HDR (n : nat) : Prop := forall f1 : YK11.FPState, H_HDR (fx := f1) B n.
Definition HA_KEY (n : nat) : Prop := forall f1 : YK11.FPState, H_KEY (fx := f1) B n.
Definition HA_CLR (n : nat) : Prop := forall f1 : YK11.FPState, H_CLR (fx := f1) B n.
Definition HA_RS3 (n : nat) : Prop := forall f1 : YK11.FPState, H_RS3 (fx := f1) B n.
Definition HA_SEG (n : nat) : Prop := forall f1 : YK11.FPState, H_SEG (fx := f1) B n.
Definition HA_NEW (n : nat) : Prop := forall f1 : YK11.FPState, H_NEW (fx := f1) B n.
Definition HA_FOUND (n : nat) : Prop := forall f1 : YK11.FPState, H_FOUND (fx := f1) B n.
Definition HA_PROV2 (n : nat) : Prop := forall f1 : YK11.FPState, H_PROV2 (fx := f1) B n.
Definition HA_ROLE (n : nat) : Prop := forall f1 : YK11.FPState, H_ROLE (fx := f1) B n.
Definition HA_MODEL (n : nat) : Prop := forall f1 : YK11.FPState, H_MODEL (fx := f1) B n.
Definition HA_IGN (n : nat) : Prop := forall f1 : YK11.FPState, H_IGN (fx := f1) B n.
Definition HA_INTENT (n : nat) : Prop := forall f1 : YK11.FPState, H_INTENT (fx := f1) B n.
Definition HA_MISS (n : nat) : Prop := forall f1 : YK11.FPState, H_MISS (fx := f1) B n.
Definition HA_LOWOUT (n : nat) : Prop := forall f1 : YK11.FPState, H_LOWOUT (fx := f1) B n.

(* A1 (plain P1), 0x87a78-0x87b24, 43 instructions: the prologue, the GOT loads of the shadow base and the
   use-after-return flag, frame_alloc_5 (0x87af0). ENTRY -> FTAKEN. *)
Definition S_A1 : Prop := forall f0 : YK11.FPState, HA_FTAKEN -> H_ENTRY (fx := f0) B.
(* A2 (P1), 0x87b24-0x87cc4, 104: slot 0x88, the frame header, the 144 shadow cells (meta_fill_f8 0x87b94).
   FTAKEN -> FRAME. *)
Definition S_A2 : Prop := forall f0 : YK11.FPState, HA_FRAME -> H_FTAKEN (fx := f0) B.
(* A3 (P1), 0x87cc4-0x87ddc + cold 0x88c68-0x88c90, 80: snprintf(c->reading) (0x87ce8), c->gen++ (#1), the
   text-NULL test (decided: t <> 0), cur_name in scope and memset (0x87d4c), *p (#2), the 19 slots.
   FRAME -> DONE (empty text) or HEAD (o = 0, ln = 0, d = [], cf = pf_start rcs lab, cur = None, nm = []). *)
Definition S_A3 : Prop := forall f0 : YK11.FPState, (forall n, HA_HEAD n) -> HA_DONE -> H_FRAME (fx := f0) B.
(* A4 (P1), 0x88bb8-0x88c68 + cold 0x88c90-0x88cb8, 54 (of which 0x88be4-0x88bf4 and 0x88c18-0x88c20 dead):
   #40, cur_name out, the retired magic, frame_release_5 (0x88c10), the epilogue. DONE -> the return. *)
Definition S_A4 : Prop := forall f0 : YK11.FPState, H_DONE (fx := f0) B.
(* A5 (P2), 111: the line driver (strchr / strlen, meta_fill_00, memcpy, strip_comment, trim, the tail's
   meta_fill_f8 and *p). HEAD -> LONG, HDR, KEY or TAIL (empty line, 0x87fa4); TAIL -> HEAD (pred n) or DONE. *)
Definition S_A5 : Prop :=
  forall (f0 : YK11.FPState) (n : nat),
    (HA_LONG n -> HA_HDR n -> HA_KEY n -> HA_TAIL n -> H_HEAD (fx := f0) B n) /\
    (HA_HEAD (pred n) -> HA_DONE -> H_TAIL (fx := f0) B n).
(* A6 (P3 + the shared refuse), 24: strspn, at[lead] (#3), refuse (0x87e74). LONG -> TAIL; REF3 -> TAIL. *)
Definition S_A6 : Prop :=
  forall (f0 : YK11.FPState) (n : nat),
    (HA_TAIL n -> H_LONG (fx := f0) B n) /\ (HA_TAIL n -> H_REF3 (fx := f0) B n).
(* A7 (P4 header), 97: strchr ']', the four header refusals, trim, strncasecmp "segment", body[7], trim, strlen,
   F_noname / F_toolong. HDR -> TAIL or SEG; CLR -> TAIL; RS3 -> TAIL. *)
Definition S_A7 : Prop :=
  forall (f0 : YK11.FPState) (n : nat),
    (HA_TAIL n -> HA_SEG n -> H_HDR (fx := f0) B n) /\ (HA_TAIL n -> H_CLR (fx := f0) B n) /\
    (HA_TAIL n -> H_RS3 (fx := f0) B n).
(* A8a (P4 seg_get search), 49: #29, the strcmp loop (0x887d0), c->overflow++ (#30), F_bound.
   SEG -> NEW, FOUND or CLR. *)
Definition S_A8a : Prop :=
  forall (f0 : YK11.FPState) (n : nat), HA_NEW n -> HA_FOUND n -> HA_CLR n -> H_SEG (fx := f0) B n.
(* A8b (P4 create / found / seen_gen + the shared snprintf), 91: n + 1 (#35), memset, snprintf(name), #36-#39,
   F_twice, cur_name's / ignore_file's snprintf (0x889f0). NEW -> TAIL; FOUND -> TAIL; PROV2 -> TAIL. *)
Definition S_A8b : Prop :=
  forall (f0 : YK11.FPState) (n : nat),
    (HA_TAIL n -> H_NEW (fx := f0) B n) /\ (HA_TAIL n -> H_FOUND (fx := f0) B n) /\
    (HA_TAIL n -> H_PROV2 (fx := f0) B n).
(* A9 (P5 + KNOCK / NOKEY), 129: strchr '=', *eq = 0, two trims, unquote, the strcasecmp dispatch, the
   knock / no-key refusal (0x88510). KEY -> ROLE, MODEL, IGN, REF3 (no '=' or cur = NULL) or TAIL. *)
Definition S_A9 : Prop :=
  forall (f0 : YK11.FPState) (n : nat),
    HA_ROLE n -> HA_MODEL n -> HA_IGN n -> HA_REF3 n -> HA_TAIL n -> H_KEY (fx := f0) B n.
(* A10a (P6 fold), 57: low in scope, the fold loop (0x88218), low[k] = 0. ROLE -> INTENT. *)
Definition S_A10a : Prop := forall (f0 : YK11.FPState) (n : nat), HA_INTENT n -> H_ROLE (fx := f0) B n.
(* A10b (P6 intent + role_file), 87: five bcmp, F_badrole, role stores (#31, #32), snprintf(role_file),
   low out. INTENT -> TAIL. *)
Definition S_A10b : Prop := forall (f0 : YK11.FPState) (n : nat), HA_TAIL n -> H_INTENT (fx := f0) B n.
(* A11a (P7 fold, by_token, hit + model_file), 84: low146 in scope, the fold (0x8829c), by_token (0x88538), the
   model stores (#27) and two snprintf. MODEL -> MISS or LOWOUT. *)
Definition S_A11a : Prop :=
  forall (f0 : YK11.FPState) (n : nat), HA_MISS n -> HA_LOWOUT n -> H_MODEL (fx := f0) B n.
(* A11b (P7 known join + refusal), 121: known / ntok scope, reac_box_catalogue, the join, F_badmodel, known out,
   low146 out. MISS -> TAIL; LOWOUT -> TAIL. *)
Definition S_A11b : Prop :=
  forall (f0 : YK11.FPState) (n : nat),
    (HA_TAIL n -> H_MISS (fx := f0) B n) /\ (HA_TAIL n -> H_LOWOUT (fx := f0) B n).
(* A12 (P8 ignore), 96: four strcasecmp, "1" / "0", F_badignore, the ignore stores (#33, #34).
   IGN -> RS3 or PROV2. *)
Definition S_A12 : Prop :=
  forall (f0 : YK11.FPState) (n : nat), HA_RS3 n -> HA_PROV2 n -> H_IGN (fx := f0) B n.
End s.

(** ** The whole function from its segments (NOT proved here). The loop by induction on n (the plain F3):
    H_TAIL 0 holds outright (its rest would be shorter than 0); S_A5's tail part gives H_TAIL (S n) from
    H_HEAD n and H_DONE (S_A4); within one n the mid-line cuts follow from H_TAIL n in the order LOWOUT, MISS,
    MODEL; PROV2, RS3, IGN; INTENT, ROLE; REF3, LONG; CLR, NEW, FOUND, SEG, HDR; KEY; then H_HEAD n (S_A5).
    S_A3 takes H_HEAD at every n, S_A2 and S_A1 close the entry, and H_ENTRY at the ambient FP state is the
    contract after the bundle is unpacked. *)
Section g.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
Variable B : asyms.
Definition pf_pieces_give_contract : Prop :=
  S_A1 B -> S_A2 B -> S_A3 B -> S_A4 B -> S_A5 B -> S_A6 B -> S_A7 B -> S_A8a B -> S_A8b B -> S_A9 B ->
  S_A10a B -> S_A10b B -> S_A11a B -> S_A11b B -> S_A12 B ->
  reac_segconf_parse_file_contract SEGS B (BASE + AF_reac_segconf_parse_file) STK_reac_segconf_parse_file
    RLO_A RHI_A seg_litA_rc catA gotwA guardA.
End g.
