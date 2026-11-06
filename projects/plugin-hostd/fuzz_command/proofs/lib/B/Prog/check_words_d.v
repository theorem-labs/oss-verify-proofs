(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: check_reply's ASan walk (fuzz_command.asan, 0x86d78) assembled from its
   segments, as proofs/cgif/cgif_file_fuzzer/lib/A/ACh5.v assembles cgif_close's (pb_cgif_closeX):
     s1 the entry to the memchr call, s2 memchr / check_reply_answer / sup_reply_code, s3 the code's split,
     s4 snprintf, s4b rec_code_declared, s5 strcmp, s6 strlen / rec_shape_of, s7 syntax_reply_matches twice,
     s8 the frame's release and the return.
   snprintf is the only call that changes the FP state, so s4b, s5 and s8 (the segments after it) are taken at every
   FP state and s4 uses them at the state the wrapper returns.
   `pb_check_reply` is tcheck_reply_spec (lib/A/Prog/check_reply_c.v). The walk's facts at the entry that the
   statement no longer states come from its premises: the record's cells (replace_str flag byte, stack guard, errno)
   from CmdRecCells' cmd_rec_cells, the recorder's GOT words from cmd_ro_ok's RO_ptr_a70xx bytes, the read-only
   ranges from CmdRecRo's cmd_ro_in_img, and the words' shadow from AR's zshadow_ok of the stack window
   [ly_stk_lo, ly_stk_hi) (the words lie in it: spZ regs <= w and w + WORDS_W + 12 <= ly_stk_hi ly). The kit lemmas
   take the image facts IMG (cmd_img_facts); the segments take CmdRecImg's cmd_heap_tail_vis, and its
   cmd_prog_unowned and cmd_rom_view_on at IMG, so no record fact is a Section hypothesis (the walk hypotheses keep
   cgif's names; the record facts are lemmas of lib/A/Prog/CmdRecFacts.v). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply.v, with its module paths and module names changed; 263 of its 289 lines of code are new or changed and 126 lines of the source are left out. *)
(* check_words' ASan+UBSan walk (plugin-hostd/fuzz_command.asan-ubsan, entry 0x87ae8, 455 instructions): the points
   where the walk is cut into segments, the state the walk is in at each point, and each segment's statement. The B
   twin of an earlier version of the A walk lib/A/Prog/check_words_d.v, stated on the pass-4/5 forms of
   lib/B/Prog/check_words_c.v (pass 5b; its statement text is the one of pass 5).

   The walk is cut at the program points below (listing offsets from BASE = 0x86530; the address on the pinned image
   in brackets). Each segment lemma proves "SRr from a state at point X that satisfies INV_X, to check_words' post",
   given the statements of the points it continues to. The A walk's cut points carry over one to one (A address in
   the last column):

     entry  0x15b8 [0x87ae8]  afn_pre (the statement's premises, cw_ent)                              A 0x878b4
     J      SIG CS_joined     the entry of joined (after `jal joined` at 0x87c24; ra = BASE + 0x16f8)  A 0x879e8
     P1     0x16f8 [0x87c28]  joined has returned                                                    A 0x879ec
     LH     0x1784 [0x87cb4]  head of the call loop, call c (`li a0,17`, UBSan index check)            A 0x87a7c
     IH     0x1848 [0x87d78]  head of the item loop, call c, item a, template cursor j in s4          A 0x87b00
     IK     0x1888 [0x87db8]  item a: the cursor s7 is past the spaces, the kind byte is next         A 0x87b38
     ICMP   0x19b4 [0x87ee4]  item a: s5 holds the string the item asks for (0: none), s7 at the item  A 0x87bfc
     ICMP2  0x19d0 [0x87f00]  item a: strcspn returned (s4 = its answer), s5 <> 0                     A 0x87c0c
     IL     0x19fc [0x87f2c]  latch of the item loop, item a done                                     A 0x87c30
     D      0x1a50 [0x87f80]  after the item loop of call c: the dispatch on call->fn                 A 0x87c90
     REL    0x1b7c [0x880ac]  after the call loop: free(line), the frame's release, the return        A 0x87db8

   B's code differs from A's in the item loop: every arm of the kind dispatch (`*`, `L`, `#`, `?`, a word) meets at
   one strcspn call (0x87ef0; A has three), with s5 = 0 for an item that asks for nothing (`*`, and `?k` with k past
   the words read); after strcspn `beqz s5` goes to the latch. The template cursor is not advanced before the latch:
   s7 holds the item's start and s4 the strcspn answer until 0x87f38 (add s4,s7,s4). So INV_ICMP carries want_at's
   option (wq) with s5 = 0 for None, and INV_ICMP2 / INV_IL carry s7 and s4 instead of the advanced cursor.

   Segments (files): A entry -> J (check_words_sA.v); J -> P1 and P1 -> LH 0 | REL (check_words_sJB.v);
   LH -> IH | D (sC); IH -> IK | D and IL -> IH | D (sI1); IK -> ICMP (sI2); ICMP -> ICMP2 | IL and ICMP2 -> IL (sI3);
   D -> LH (c+1) | REL (sD); REL -> post (sR). The two loops are closed by induction on the remaining trip count in
   check_words_asm.v; check_words.v proves the theorem.

   What each invariant carries: the journal from the entry (ajournal, own frame (0, pos)), the registers and stack
   slots the code reads later, the frame's flag pointer and number[16]'s shadow, joined's block (after P1), and the
   meter. Facts the entry state gives about memory the walk never writes (the caller's struct words, the word array
   and words, g_rec and the recorded arguments, the image's read-only bytes) are NOT repeated: each segment reads them
   at its current state from the entry fact and the journal.

   B's scratch area (s1 = sp1, the realigned sp, 0x87b2c), with the instruction that stores each slot:
     8 g_rec+8 (0x87c34)          16 SB + F/8 (0x87be0)        24 F (0x87b88)              32 F (0x87bec)
     40 g_call_words (0x87c98)    48 g_rec (0x87cb0)           56 ~g_call_words (0x87ca0)  64 g_rec+16 (0x87c80)
     72 ~(g_rec+16) (0x87c88)     80 SB + (g_rec+8)/8 (0x87c40) 88 F+32 (0x87c64)          96 SB + cp/8 (0x87cec)
     104 c (0x87cc0)              112, 120 g_rec+24+56c (0x87ca4/a8, latch 0x88048/54)     128 cp (0x87cf0)
     136 (Wd+16)/8 (0x87d34)      144 Wd+16 (0x87c6c)          152 line (0x87c48)           160 read (0x87cac)
     168 ~(cp+8) (0x87d6c)        176 " " 0x21160 (0x87c94)    184 SB + (cp+4)/8 (0x87d1c)  200 F (0x87bf0, never read)
     208 len (joined's out cell)
   where cp = &g_rec.calls[c].fn = g_rec + 16 + 56 c and ~x = 2^64 - 1 - x. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString RtNumber RtFormat RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import printf_facts_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require joined_c check_words_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
joined_c check_words_add_c check_words_chain_c check_words_pin_set_c sup_reply_code_c HarnessPropsA.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import check_words_c PaFx.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Module PCW := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.check_words_c.
Module PJn := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.joined_c.

(* ---------------------------------------------------------------------------------------------------------- *)
(* program points (listing offsets from BASE = 0x86530) *)
Definition CW_PC_P1 : Z := 0x16f8.     (* 0x87c28, joined's return address *)
Definition CW_PC_LH : Z := 0x1784.     (* 0x87cb4 *)
Definition CW_PC_IH : Z := 0x1848.     (* 0x87d78 *)
Definition CW_PC_IK : Z := 0x1888.     (* 0x87db8 *)
Definition CW_PC_ICMP : Z := 0x19b4.   (* 0x87ee4 *)
Definition CW_PC_ICMP2 : Z := 0x19d0.  (* 0x87f00 *)
Definition CW_PC_IL : Z := 0x19fc.     (* 0x87f2c *)
Definition CW_PC_D : Z := 0x1a50.      (* 0x87f80 *)
Definition CW_PC_REL : Z := 0x1b7c.    (* 0x880ac *)
Definition CW_SB : Z := 0x7fff8000.
(* the 64-bit complement ~x = 2^64 - 1 - x (the `not` precomputes of the UBSan wrap checks) *)
Definition cw_not (x : Z) : Z := 2 ^ 64 - 1 - x.

(* the callee-saved registers the prologue stores, register cw_saved[j] at sp0 - 8 - 8 j (0x87af0 .. 0x87b20) *)
Definition cw_saved : list Z := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].

(* the templates of g_call_words (fuzz_command.c:304-331): the table 0xa5920 (RO_g_call_words) holds, for each
   recorded function fn < 26, the address cw_tptr fn of its item string cw_tpl fn (the RO_lit_* objects of CmdRo.v;
   slots 3 and 8 hold "" 0x212c0) *)
Definition cw_tptr (fn : Z) : Z :=
  match fn with
  | 0 => 0x21900 | 1 => 0x21920 | 2 => 0x21940 | 3 => 0x212c0 | 4 => 0x21960 | 5 => 0x21980 | 6 => 0x219a0
  | 7 => 0x219c0 | 8 => 0x212c0 | 9 => 0x21940 | 10 => 0x219e0 | 11 => 0x21a00 | 12 => 0x21a20 | 13 => 0x21a00
  | 14 => 0x21a40 | 15 => 0x21a20 | 16 => 0x21a60 | 17 => 0x21a80 | 18 => 0x21940 | 19 => 0x21aa0 | 20 => 0x21ac0
  | 21 => 0x21a00 | 22 => 0x21a00 | 23 => 0x21a00 | 24 => 0x21a00 | _ => 0x21ae0
  end.
Definition cw_tpl (fn : Z) : list byte :=
  map (Z_to_bv 8) match fn with
  | 0 => [49; 32; 35; 50; 32; 42; 32; 42] | 1 => [35; 49; 32; 76] | 2 => [35; 49] | 3 => []
  | 4 => [48; 32; 76; 32; 49; 32; 50] | 5 => [76] | 6 => [76; 32; 42; 32; 42] | 7 => [76; 32; 42] | 8 => []
  | 9 => [35; 49] | 10 => [63; 49] | 11 => [49] | 12 => [49; 32; 50] | 13 => [49] | 14 => [49; 32; 35; 50]
  | 15 => [49; 32; 50] | 16 => [49; 32; 50; 32; 51] | 17 => [35; 49; 32; 42; 32; 42] | 18 => [35; 49]
  | 19 => [35; 49; 32; 48] | 20 => [49; 32; 50; 32; 51; 32; 42] | 21 => [49] | 22 => [49] | 23 => [49]
  | 24 => [49] | _ => [42]
  end.
(* the code's parse of a template (the plain lib/Prog/CwItems.v:24-39 item_of / tpl_items, with the ASan atoi value
   atoi_a): skip the spaces (the strspn wrapper on " "), the kind byte picks the item, skip the item (strcspn) *)
Definition CW_SP1 : list byte := [Z_to_bv 8 32].
Definition item_of_a (s : list byte) : PCW.witem :=
  let b := bv_unsigned (hd (Z_to_bv 8 0) s) in
  if b =? 35 then PCW.INum (atoi_a (tl s))
  else if b =? 42 then PCW.IStar
  else if b =? 76 then PCW.ILine
  else if b =? 63 then PCW.IOpt (atoi_a (tl s))
  else PCW.IWord (atoi_a s).
Fixpoint tpl_items_a (f : nat) (s : list byte) : list PCW.witem :=
  match f, s with
  | O, _ => []
  | _, [] => []
  | S f', _ :: _ =>
      let s1 := skipn (PSpn.spn_len CW_SP1 s) s in
      item_of_a s1 :: tpl_items_a f' (skipn (PCspn.cspn_len CW_SP1 s1) s1)
  end.
Definition cw_parse (s : list byte) : list PCW.witem := tpl_items_a (S (length s)) s.
(* the cursor after the spaces before the item at j, and after the item *)
Definition cw_kp (tpl : list byte) (j : nat) : nat := j + PSpn.spn_len CW_SP1 (skipn j tpl).
Definition cw_kn (tpl : list byte) (j : nat) : nat := cw_kp tpl j + PCspn.cspn_len CW_SP1 (skipn (cw_kp tpl j) tpl).
(* the strcspn answer at the item that starts at j1 (s4 at ICMP2 and IL) *)
Definition cw_cs (tpl : list byte) (j1 : nat) : nat := PCspn.cspn_len CW_SP1 (skipn j1 tpl).

(* the read-only strings and objects whose shadow the inline checks and the wrappers read: g_rec, the table, " ",
   "", "%d" and the 16 item strings (address, bytes with the terminator) *)
Definition CW_ZSH : list (Z * Z) :=
  [(A_G_REC, 960); (0xa5920, 208); (0x21160, 2); (0x212c0, 1); (0x218e0, 3);
   (0x21900, 9); (0x21920, 5); (0x21940, 3); (0x21960, 8); (0x21980, 2); (0x219a0, 6); (0x219c0, 4);
   (0x219e0, 3); (0x21a00, 2); (0x21a20, 4); (0x21a40, 5); (0x21a60, 6); (0x21a80, 7); (0x21aa0, 5);
   (0x21ac0, 8); (0x21ae0, 2)].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.

(* ---------------------------------------------------------------------------------------------------------- *)
(* The record facts the segment files take as Section hypotheses (`Hypothesis <name> : <name>_P B`), each proved
   from lib/B/Prog/CmdRecFacts.v in check_words_rf.v, so that check_words.v discharges them by exact and the
   theorem names only the statement's hypotheses and the walk hypotheses. CW_ZSH_P is
   cmd_aread_ok_chk at the 21 ranges of CW_ZSH; cw_ro_unowned_P is cif_ro_unowned (IMG) at the same ranges. *)
Definition cmd_rec_cells_P : Prop := forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  rdW W mem 0xae455 = Some 1 /\ aguard_ok SEGS W mem 0xa6bf8 0x604158 /\ exists ev, rd32 (rdW W mem) (as_errno B) ev.
Definition cmd_rom_view_on_P : Prop := forall (W : world SEGS) mem,
  arodata_okP SEGS RLO RHI B (rdW W mem) -> rt_rom_view SEGS B W mem.
Definition cmd_heap_tail_vis_P : Prop := forall ly S (W : world SEGS) mem md p n e, AR SEGS B ly S W mem md ->
  In (p, n) (ablocks B ly S) -> p <= e < p + req_size n -> atail_vis SEGS W mem e.
Definition cmd_prog_unowned_P : Prop := forall a, inFP cmd_PG a ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Definition CW_ZSH_P : Prop := forall ly S (W : world SEGS) mem md a n, AR SEGS B ly S W mem md -> In (a, n) CW_ZSH ->
  range_addressable (rdW W mem) SHADOW_OFF a n /\ shadow_hull_vis (rdW W mem) a n.
Definition cw_ro_unowned_P : Prop := forall a n i, In (a, n) CW_ZSH -> a <> A_G_REC -> 0 <= i < n ->
  in_img SEGS (a + i) /\ ~ Exists (in_zr (a + i)) (as_owned_static B) /\ ~ (as_errno B <= a + i < as_errno B + 4).
(* CmdRecFacts' cmd_tail_vis_at: the bytes of a literal's last 8-byte word are visible at every AR state *)
Definition cmd_tail_vis_P : Prop := forall ly S (W : world SEGS) mem md e, AR SEGS B ly S W mem md ->
  In e cmd_ro_ends -> atail_vis SEGS W mem e.
(* the GOT word 0xa6bc8 holds g_rec's address (CmdRecRo's cmd_got_rec, at a state with arodata_okP) *)
Definition cmd_got_rec_P : Prop := forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  arodata_okP SEGS RLO RHI B (rdW W mem) -> aval_mem (rdW W mem) 0xa6bc8 8 A_G_REC.
(* the walk hypothesis RRO *)
Definition RRO_P : Prop := forall a, RLO <= a < RHI -> in_img SEGS a.

(* ---------------------------------------------------------------------------------------------------------- *)
(* the entry: the statement's state and witnesses, and its premises *)
Record cwE := mkCWE {
  e_ly : alayout; e_S : astate; e_W : world SEGS; e_regs : bvmap 5 word; e_mem : word -> option byte; e_md : Model;
  e_ch : list (Z * Z * Z); e_Wd : Z; e_arr : Z; e_wp : list Z; e_ws : list (list byte); e_R : rstate;
  e_O : list (Z * Z) }.
Definition cw_sp0 (e : cwE) : Z := spZ (e_regs e).
Definition cw_n (e : cwE) : Z := Z.of_nat (length (e_ws e)).
Definition cw_read (e : cwE) : Z := Z.min (cw_n e) 64.
Definition cw_JN (e : cwE) : Z := PJn.join_need (e_ws e) + 1.
Definition cw_ncalls (e : cwE) : Z := Z.of_nat (length (r_calls (e_R e))).
Definition cw_rd0 (e : cwE) : reader := rdW (e_W e) (e_mem e).

(* tcheck_words_spec's premises (lib/B/Prog/check_words_c.v), in the order of the A
   walk's cw_ent (an earlier version of lib/A/Prog/check_words_d.v) so that destruct patterns port by
   position: the two alignment premises (`Wd mod 8 = 0`, check_words_c.v:159, and `arr mod 8 = 0`, :170) come last;
   the rounding-mode-0 premise is `frm0 fx` (PaFx.v:33, convertible to the statement's form) *)
Definition cw_ent (e : cwE) : Prop :=
  let ly := e_ly e in let S := e_S e in let W := e_W e in let regs := e_regs e in let mem := e_mem e in
  let ws := e_ws e in let wp := e_wp e in
  afn_pre SEGS B CHECK_WORDS_STK ly S W regs mem (e_md e) (e_ch e) /\
  frm0 fx /\
  arodata_okP SEGS RLO RHI B (rdW W mem) /\
  getr regs 10 = w64 (e_Wd e) /\
  cmd_ro_ok (rdW W mem) /\ cmd_val_objs /\
  spZ regs <= e_Wd e + 16 /\ e_Wd e + 32 <= ly_stk_hi ly /\
  aval_mem (rdW W mem) (e_Wd e + 16) 8 (e_arr e) /\ 0 <= e_arr e < 2 ^ 64 /\
  aval_mem (rdW W mem) (e_Wd e + 24) 4 (Z.of_nat (length ws)) /\
  length wp = length ws /\ Z.of_nat (length ws) < 2 ^ 31 /\
  in_blockA (ablocks B ly S) (e_arr e) (8 * Z.of_nat (length ws)) /\
  (forall k, (k < length ws)%nat ->
   aval_mem (rdW W mem) (e_arr e + 8 * Z.of_nat k) 8 (nth k wp 0) /\ 0 <= nth k wp 0 < 2 ^ 64 /\
   in_blockA (ablocks B ly S) (nth k wp 0) (Z.of_nat (length (nth k ws [])) + 1) /\
   astr_atR (rdW W mem) (nth k wp 0) (nth k ws [])) /\
  PJn.join_need ws + 1 < MALLOC_MAX /\
  rec_repA B ly S (rdW W mem) (e_R e) (e_O e) /\
  words_prop_at atoi_a (e_R e) ws /\
  count_cid 0 (frames S) < fs_frames 0 /\ count_cid 4 (frames S) < fs_frames 4 /\
  st_nev S + EV_CHECK_WORDS <= EV_MAX /\ blocks_bytes S + LIVE_CHECK_WORDS <= LIVE_MAX /\
  mo_ok MT S (XM_CHECK_WORDS MT ws) /\
  e_Wd e mod 8 = 0 /\ e_arr e mod 8 = 0.

(* tcheck_words_spec's conclusion (pass 4: apost_baseF, FP-existential at the ambient FP state) *)
Definition cw_post (e : cwE) : world SEGS -> config -> Prop :=
  apost_baseF SEGS B CHECK_WORDS_STK [] (e_regs e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) EV_CHECK_WORDS
  (fun ly' S' W' regs' mem' md' =>
   Permutation (ablocks B ly' S') (ablocks B (e_ly e) (e_S e)) /\
   rec_repA B ly' S' (rdW W' mem') (e_R e) (e_O e) /\
   mo_le MT (e_S e) S' (XM_CHECK_WORDS MT (e_ws e))).

(* ---------------------------------------------------------------------------------------------------------- *)
(* the parts of the state every point after the frame setup (0x87bf0) has *)
Definition cw_saves (rd : reader) (sp0 : Z) (regs : bvmap 5 word) : Prop :=
  forall j r, nth_error cw_saved j = Some r ->
  aval_mem rd (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))).

(* F = the class-0 side-stack frame (cid 0, position pos) the call took at 0x87b54, at frame_addr (e_ly e) 0 pos;
   sp1 = the realigned sp (0x87b28), the base of the scratch area s1; k = the allocator events so far. s0 = sp0
   (0x87b24), s6 = the shadow base (0x87b44) *)
Definition cw_core (e : cwE) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (regsc : bvmap 5 word)
  (memc : word -> option byte) (mdc : Model) (pos sp1 k : Z) : Prop :=
  let F := frame_addr (e_ly e) 0 pos in let rd := rdW Wc memc in
  ajournal SEGS B CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(0, pos)]
    lyc Sc Wc memc mdc k /\
  spZ regsc = sp1 /\ sp1 mod 32 = 0 /\ cw_sp0 e - 336 <= sp1 <= cw_sp0 e - 320 /\
  getr regsc 3 = getr (e_regs e) 3 /\ getr regsc 4 = getr (e_regs e) 4 /\
  getr regsc 8 = getr (e_regs e) 2 /\ getr regsc 9 = w64 sp1 /\ getr regsc 22 = w64 CW_SB /\
  cw_saves rd (cw_sp0 e) (e_regs e) /\
  aval_mem rd (sp1 + 16) 8 (CW_SB + F / 8) /\ aval_mem rd (sp1 + 24) 8 F /\ aval_mem rd (sp1 + 32) 8 F /\
  aval_mem rd (F + 56) 8 (flag_addr (e_ly e) 0 pos) /\
  rd (CW_SB + F / 8 + 4) = Some 0 /\ rd (CW_SB + F / 8 + 5) = Some 0.

(* joined's block `line` (fuzz_command.c:395) and the meter after it *)
Definition cw_line (e : cwE) (lyc : alayout) (Sc : astate) (rd : reader) (line : Z) : Prop :=
  Permutation (ablocks B lyc Sc) ((line, cw_JN e) :: ablocks B (e_ly e) (e_S e)) /\ 4096 <= line /\
  Forall (fun qk => iv_apart line (cw_JN e) (fst qk) (snd qk)) (ablocks B (e_ly e) (e_S e)) /\
  abytes_atR rd line (join_sp (e_ws e) ++ [Z_to_bv 8 0]) /\
  mo_le MT (e_S e) Sc (XM_JOINED MT (e_ws e)).

(* the scratch slots P1 .. LH stores (0x87c34 .. 0x87cb0) and the latch moves (112, 120), at call c *)
Definition cw_lscr (e : cwE) (rd : reader) (sp1 F line c : Z) : Prop :=
  aval_mem rd (sp1 + 152) 8 line /\
  aval_mem rd (sp1 + 8) 8 (A_G_REC + 8) /\ aval_mem rd (sp1 + 80) 8 (CW_SB + (A_G_REC + 8) / 8) /\
  aval_mem rd (sp1 + 88) 8 (F + 32) /\ aval_mem rd (sp1 + 144) 8 (e_Wd e + 16) /\
  aval_mem rd (sp1 + 64) 8 (A_G_REC + 16) /\ aval_mem rd (sp1 + 72) 8 (cw_not (A_G_REC + 16)) /\
  aval_mem rd (sp1 + 40) 8 0xa5920 /\ aval_mem rd (sp1 + 56) 8 (cw_not 0xa5920) /\
  aval_mem rd (sp1 + 176) 8 0x21160 /\ aval_mem rd (sp1 + 160) 8 (cw_read e) /\ aval_mem rd (sp1 + 48) 8 A_G_REC /\
  aval_mem rd (sp1 + 112) 8 (A_G_REC + 24 + 56 * c) /\ aval_mem rd (sp1 + 120) 8 (A_G_REC + 24 + 56 * c).
(* the slots call c's iteration stores (0x87cc0 .. 0x87d34): cp = &call->fn = A_G_REC + 16 + 56 c *)
Definition cw_cscr (e : cwE) (rd : reader) (sp1 c : Z) : Prop :=
  let cp := A_G_REC + 16 + 56 * c in
  aval_mem rd (sp1 + 104) 8 c /\ aval_mem rd (sp1 + 96) 8 (CW_SB + cp / 8) /\ aval_mem rd (sp1 + 128) 8 cp /\
  aval_mem rd (sp1 + 184) 8 (CW_SB + (cp + 4) / 8) /\ aval_mem rd (sp1 + 136) 8 ((e_Wd e + 16) / 8).

(* ---------------------------------------------------------------------------------------------------------- *)
(* the invariants at the cut points *)
Definition INV_J (e : cwE) lyc Sc Wc regsc memc mdc (pos sp1 : Z) : Prop :=
  cw_core e lyc Sc Wc regsc memc mdc pos sp1 0 /\ mo_le MT (e_S e) Sc 0 /\
  getr regsc 10 = w64 (e_Wd e) /\ getr regsc 11 = w64 (sp1 + 208) /\ getr regsc 1 = w64 (BASE + CW_PC_P1) /\
  getr regsc 20 = w64 (e_Wd e) /\ getr regsc 18 = w64 (cw_read e) /\
  Permutation (ablocks B lyc Sc) (ablocks B (e_ly e) (e_S e)) /\ blocks_bytes Sc = blocks_bytes (e_S e).

Definition INV_P1 (e : cwE) lyc Sc Wc regsc memc mdc (pos sp1 line : Z) : Prop :=
  cw_core e lyc Sc Wc regsc memc mdc pos sp1 EV_JOINED /\ cw_line e lyc Sc (rdW Wc memc) line /\
  getr regsc 10 = w64 line /\ getr regsc 20 = w64 (e_Wd e) /\ getr regsc 18 = w64 (cw_read e).

Definition INV_LH (e : cwE) lyc Sc Wc regsc memc mdc (pos sp1 line c : Z) : Prop :=
  cw_core e lyc Sc Wc regsc memc mdc pos sp1 EV_JOINED /\ cw_line e lyc Sc (rdW Wc memc) line /\
  cw_lscr e (rdW Wc memc) sp1 (frame_addr (e_ly e) 0 pos) line c /\
  getr regsc 21 = w64 c /\
  0 <= c < cw_ncalls e.

Definition INV_D (e : cwE) lyc Sc Wc regsc memc mdc (pos sp1 line c : Z) : Prop :=
  cw_core e lyc Sc Wc regsc memc mdc pos sp1 EV_JOINED /\ cw_line e lyc Sc (rdW Wc memc) line /\
  cw_lscr e (rdW Wc memc) sp1 (frame_addr (e_ly e) 0 pos) line c /\ cw_cscr e (rdW Wc memc) sp1 c /\
  0 <= c < cw_ncalls e.

(* the registers of the item loop of call c (fn, args) = nth c (r_calls R): cp = &call->fn, s10 = &call->nargs,
   s2 = a, s9 = 8 a, s8 = s11 = &call->args[a]; the template cursor is s4 at IH, s7 from IK on *)
Definition cw_iregs (regsc : bvmap 5 word) (c a : Z) : Prop :=
  let cp := A_G_REC + 16 + 56 * c in
  getr regsc 26 = w64 (cp + 4) /\ getr regsc 18 = w64 a /\ getr regsc 25 = w64 (8 * a) /\
  getr regsc 24 = w64 (cp + 8 + 8 * a) /\ getr regsc 27 = w64 (cp + 8 + 8 * a).
Definition cw_icommon (e : cwE) lyc Sc Wc regsc memc mdc (pos sp1 line c a : Z) (fn : Z) (args : list (list byte))
  : Prop :=
  cw_core e lyc Sc Wc regsc memc mdc pos sp1 EV_JOINED /\ cw_line e lyc Sc (rdW Wc memc) line /\
  cw_lscr e (rdW Wc memc) sp1 (frame_addr (e_ly e) 0 pos) line c /\ cw_cscr e (rdW Wc memc) sp1 c /\
  aval_mem (rdW Wc memc) (sp1 + 168) 8 (cw_not (A_G_REC + 16 + 56 * c + 8)) /\
  cw_iregs regsc c a /\
  0 <= c < cw_ncalls e /\
  nth_error (r_calls (e_R e)) (Z.to_nat c) = Some (fn, args) /\ 0 <= a < Z.of_nat (length args).

(* head of the item loop: items 0 .. a-1 are done, the template cursor s4 is at j *)
Definition INV_IH (e : cwE) lyc Sc Wc regsc memc mdc (pos sp1 line c a : Z) (j : nat) : Prop :=
  exists fn args, cw_icommon e lyc Sc Wc regsc memc mdc pos sp1 line c a fn args /\
  (j <= length (cw_tpl fn))%nat /\ getr regsc 20 = w64 (cw_tptr fn + Z.of_nat j) /\
  cw_parse (skipn j (cw_tpl fn)) = skipn (Z.to_nat a) (PCW.call_items fn).

(* item a: the cursor s7 = j1 is past the spaces (j1 = cw_kp tpl j for the head's j); the item's kind byte is next *)
Definition INV_IK (e : cwE) lyc Sc Wc regsc memc mdc (pos sp1 line c a : Z) (j1 : nat) : Prop :=
  exists fn args, cw_icommon e lyc Sc Wc regsc memc mdc pos sp1 line c a fn args /\
  (j1 <= length (cw_tpl fn))%nat /\ getr regsc 23 = w64 (cw_tptr fn + Z.of_nat j1) /\
  item_of_a (skipn j1 (cw_tpl fn)) :: cw_parse (skipn (cw_cs (cw_tpl fn) j1) (skipn j1 (cw_tpl fn)))
    = skipn (Z.to_nat a) (PCW.call_items fn).

(* the string the item's argument is compared with, held in s5 from ICMP on: its address q and bytes y, and where
   it lives (joined's block, the literal "" at 0x212c0, number[16] at F + 32, or a word of the message) *)
Definition cw_wsrc (e : cwE) lyc Sc (rd : reader) (pos line q : Z) (y : list byte) : Prop :=
  astr_atR rd q y /\ 0 < q /\
  ((q = line /\ y = join_sp (e_ws e)) \/
   (q = 0x212c0 /\ y = []) \/
   (q = frame_addr (e_ly e) 0 pos + 32 /\ (length y < 16)%nat) \/
   (exists k, (k < length (e_ws e))%nat /\ q = nth k (e_wp e) 0 /\ y = nth k (e_ws e) [] /\
      in_blockA (ablocks B lyc Sc) q (Z.of_nat (length y) + 1))).
(* s5 at ICMP: 0 for an item that asks for nothing (want_at's None: `*`, and `?k` with k past the words read),
   else the string it asks for *)
Definition cw_wq (e : cwE) lyc Sc (rd : reader) (pos line q : Z) (wq : option (list byte)) : Prop :=
  match wq with
  | None => q = 0
  | Some y => cw_wsrc e lyc Sc rd pos line q y
  end.

(* at ICMP (0x87ee4) the cursor s7 = j1 is at the item (strcspn skips it next), s3 = ~s7, s5 = q *)
Definition INV_ICMP (e : cwE) lyc Sc Wc regsc memc mdc (pos sp1 line c a : Z) (j1 : nat) (q : Z)
  (wq : option (list byte)) : Prop :=
  exists fn args, cw_icommon e lyc Sc Wc regsc memc mdc pos sp1 line c a fn args /\
  (j1 <= length (cw_tpl fn))%nat /\ getr regsc 23 = w64 (cw_tptr fn + Z.of_nat j1) /\
  getr regsc 19 = w64 (cw_not (cw_tptr fn + Z.of_nat j1)) /\
  item_of_a (skipn j1 (cw_tpl fn)) :: cw_parse (skipn (cw_cs (cw_tpl fn) j1) (skipn j1 (cw_tpl fn)))
    = skipn (Z.to_nat a) (PCW.call_items fn) /\
  getr regsc 21 = w64 q /\ cw_wq e lyc Sc (rdW Wc memc) pos line q wq /\
  want_at atoi_a (cw_read e) (e_ws e) (item_of_a (skipn j1 (cw_tpl fn))) = wq.

(* at ICMP2 (0x87f00) strcspn has returned: s7 = j1 still, s4 = its answer, the item asks for y in s5 = q *)
Definition INV_ICMP2 (e : cwE) lyc Sc Wc regsc memc mdc (pos sp1 line c a : Z) (j1 : nat) (q : Z) (y : list byte)
  : Prop :=
  exists fn args, cw_icommon e lyc Sc Wc regsc memc mdc pos sp1 line c a fn args /\
  (j1 <= length (cw_tpl fn))%nat /\ getr regsc 23 = w64 (cw_tptr fn + Z.of_nat j1) /\
  getr regsc 20 = w64 (Z.of_nat (cw_cs (cw_tpl fn) j1)) /\
  item_of_a (skipn j1 (cw_tpl fn)) :: cw_parse (skipn (cw_cs (cw_tpl fn) j1) (skipn j1 (cw_tpl fn)))
    = skipn (Z.to_nat a) (PCW.call_items fn) /\
  getr regsc 21 = w64 q /\ cw_wsrc e lyc Sc (rdW Wc memc) pos line q y /\
  want_at atoi_a (cw_read e) (e_ws e) (item_of_a (skipn j1 (cw_tpl fn))) = Some y.

(* latch of the item loop: item a is done; s7 = j1, s4 = the strcspn answer; the next head's cursor is s7 + s4 *)
Definition INV_IL (e : cwE) lyc Sc Wc regsc memc mdc (pos sp1 line c a : Z) (j1 : nat) : Prop :=
  exists fn args, cw_icommon e lyc Sc Wc regsc memc mdc pos sp1 line c a fn args /\
  (j1 <= length (cw_tpl fn))%nat /\ getr regsc 23 = w64 (cw_tptr fn + Z.of_nat j1) /\
  getr regsc 20 = w64 (Z.of_nat (cw_cs (cw_tpl fn) j1)) /\
  item_of_a (skipn j1 (cw_tpl fn)) :: cw_parse (skipn (cw_cs (cw_tpl fn) j1) (skipn j1 (cw_tpl fn)))
    = skipn (Z.to_nat a) (PCW.call_items fn).

Definition INV_REL (e : cwE) lyc Sc Wc regsc memc mdc (pos sp1 line : Z) : Prop :=
  cw_core e lyc Sc Wc regsc memc mdc pos sp1 EV_JOINED /\ cw_line e lyc Sc (rdW Wc memc) line /\
  aval_mem (rdW Wc memc) (sp1 + 152) 8 line.

(* ---------------------------------------------------------------------------------------------------------- *)
(* the statements of the points: from a state at the point that satisfies its invariant, check_words' post *)
Definition cw_at (e : cwE) (Wc : world SEGS) (regsc : bvmap 5 word) (pc : Z) memc mdc : Prop :=
  SRr SEGS Wc (mkCfg (mkst regsc (Z_to_bv 64 pc) memc (seg_rom SEGS)) mdc) (cw_post e).

Definition ST_J : Prop := forall e lyc Sc Wc regsc memc mdc pos sp1,
  cw_ent e -> INV_J e lyc Sc Wc regsc memc mdc pos sp1 -> cw_at e Wc regsc (SIG CS_joined) memc mdc.
Definition ST_P1 : Prop := forall e lyc Sc Wc regsc memc mdc pos sp1 line,
  cw_ent e -> INV_P1 e lyc Sc Wc regsc memc mdc pos sp1 line -> cw_at e Wc regsc (BASE + CW_PC_P1) memc mdc.
Definition ST_LH (c : Z) : Prop := forall e lyc Sc Wc regsc memc mdc pos sp1 line,
  cw_ent e -> INV_LH e lyc Sc Wc regsc memc mdc pos sp1 line c -> cw_at e Wc regsc (BASE + CW_PC_LH) memc mdc.
Definition ST_IH (c a : Z) : Prop := forall e lyc Sc Wc regsc memc mdc pos sp1 line j,
  cw_ent e -> INV_IH e lyc Sc Wc regsc memc mdc pos sp1 line c a j -> cw_at e Wc regsc (BASE + CW_PC_IH) memc mdc.
Definition ST_IK (c a : Z) : Prop := forall e lyc Sc Wc regsc memc mdc pos sp1 line j1,
  cw_ent e -> INV_IK e lyc Sc Wc regsc memc mdc pos sp1 line c a j1 -> cw_at e Wc regsc (BASE + CW_PC_IK) memc mdc.
Definition ST_ICMP (c a : Z) : Prop := forall e lyc Sc Wc regsc memc mdc pos sp1 line j1 q wq,
  cw_ent e -> INV_ICMP e lyc Sc Wc regsc memc mdc pos sp1 line c a j1 q wq ->
  cw_at e Wc regsc (BASE + CW_PC_ICMP) memc mdc.
Definition ST_ICMP2 (c a : Z) : Prop := forall e lyc Sc Wc regsc memc mdc pos sp1 line j1 q y,
  cw_ent e -> INV_ICMP2 e lyc Sc Wc regsc memc mdc pos sp1 line c a j1 q y ->
  cw_at e Wc regsc (BASE + CW_PC_ICMP2) memc mdc.
Definition ST_IL (c a : Z) : Prop := forall e lyc Sc Wc regsc memc mdc pos sp1 line j1,
  cw_ent e -> INV_IL e lyc Sc Wc regsc memc mdc pos sp1 line c a j1 -> cw_at e Wc regsc (BASE + CW_PC_IL) memc mdc.
Definition ST_D (c : Z) : Prop := forall e lyc Sc Wc regsc memc mdc pos sp1 line,
  cw_ent e -> INV_D e lyc Sc Wc regsc memc mdc pos sp1 line c -> cw_at e Wc regsc (BASE + CW_PC_D) memc mdc.
Definition ST_REL : Prop := forall e lyc Sc Wc regsc memc mdc pos sp1 line,
  cw_ent e -> INV_REL e lyc Sc Wc regsc memc mdc pos sp1 line -> cw_at e Wc regsc (BASE + CW_PC_REL) memc mdc.
(* the entry *)
Definition ST_ENTRY : Prop := forall e,
  cw_ent e -> SRr SEGS (e_W e) (cfg_at SEGS (BASE + AF_check_words) (e_regs e) (e_mem e) (e_md e)) (cw_post e).

(* the segment lemmas' shapes (each proved in its own file, under the walk's Section hypotheses, at that Section's
   ambient FP state fx; after its Section closes each lemma holds at every fx). Pass 4: two segments continue at the
   FP state fx1 a printf-reaching call returns (I2's snprintf in the '#' arm, D's call of check_words_chain), so
   they take the statement of the point they continue to at EVERY FP state (`forall fx0, ST_X (fx := fx0) ...`), use
   it at fx1 with `cw_ent_fx` below, and lift its apost_baseF from fx1 to fx with PaFx.v's srr_apost_baseF_lift:
     seg_A   : ST_J -> ST_ENTRY
     seg_J   : ST_P1 -> ST_J
     seg_B   : ST_LH 0 -> ST_REL -> ST_P1
     seg_C   : forall c, ST_IH c 0 -> ST_D c -> ST_LH c
     seg_I1h : forall c a, ST_IK c a -> ST_D c -> ST_IH c a
     seg_I1l : forall c a, ST_IH c (a + 1) -> ST_D c -> ST_IL c a
     seg_I2  : forall c a, (forall fx0, ST_ICMP (fx := fx0) c a) -> ST_IK c a
     seg_I3a : forall c a, ST_ICMP2 c a -> ST_IL c a -> ST_ICMP c a
     seg_I3b : forall c a, ST_IL c a -> ST_ICMP2 c a
     seg_D   : forall c, (forall fx0, ST_LH (fx := fx0) (c + 1)) -> (forall fx0, ST_REL (fx := fx0)) -> ST_D c
     seg_R   : ST_REL
   A's seg_I2 also takes ST_ICMP2 and ST_IL (A's '*' / '?' arms and its word arm call strcspn themselves) and A's
   seg_I3a takes only ST_ICMP2; on B the one strcspn call is in I3a, so I3a takes the latch too.
   check_words_asm.v closes the loops over the statements at every FP state. *)
End e.
End f.
End d.

(* cw_ent at the FP state fx1 a printf-reaching call returns: only its rounding-mode conjunct names the FP state, and
   PaFx.v's fxrel_frm0 gives it at fx1 *)
Lemma cw_ent_fx {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg cmd_listing} :
  forall (fx fx1 : YK11.FPState) B MT e, cw_ent (fx := fx) B MT e -> frm0 fx1 -> cw_ent (fx := fx1) B MT e.
Proof.
intros fx fx1 B MT e H F. unfold cw_ent in *. cbv zeta in *.
destruct H as (H1 & _ & H3). exact (conj H1 (conj F H3)).
Qed.
