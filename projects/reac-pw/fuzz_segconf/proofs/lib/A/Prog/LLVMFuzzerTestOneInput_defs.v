(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the boundary states and segment statements of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86530), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (the CL_*_stmtX statements: from a point of the function to its return, under the entry's context) and A/ACf5.v (rtcx, rt_base: the entry's facts bundled once). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths, module names, addresses and numbers changed; 469 of its 518 lines of code are new or changed and 289 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan image A (fuzz_segconf.asan, pin sha256 48c5355bdacb): the cut statements of the walk
   of the test harness's entry function LLVMFuzzerTestOneInput (0x84d34, 1,122 instructions), and the statement of
   every segment lemma between them. Statement text only: no function of the binary is proved here.

   THE FORM: plugin-hostd/fuzz_command's lib/A/Prog/LLVMFuzzerTestOneInput_defs.v (origin/ossv/recipes
   501c0d516c69): the context record lcx, lt_base (the contract's premises word for word, so lt_adapter is exact),
   lt_post / lt_Q (its post word for word), and one LT_<cut>_stmt per cut: "from this point of the function to its
   return, under the entry's context", concluding SRr of lt_post at the FP state of the point; LTA_<cut> is the
   same at every FP state (a callee that reaches printf returns at an FP state of its own). The side-stack frame
   part is chain_words' (its lib/A/Prog/chain_words_d.v:59-175): the frame position x_fpos in the context, the
   journal from the entry with own = [(3, x_fpos)].
   The cuts and segments are those of the harness's structure map, section 2.3 (its segment table); the registers and
   s1-slots each cut states are the map's live-register table's (section 6); the frame's shadow states section 3.4; the model
   content is the plain / UBSan owner's plain lib/Prog/seg_cuts.v (P_K138e8 .. P_K13f40) read through the ASan reader with
   SegABase's sa_ forms. Register numbers: ra 1, sp 2, gp 3, tp 4, t0 5, s0 8, s1 9, a0-a7 10-17, s2-s11 18-27.

   NAMES (the structure map's): SP0 = x_sp0 the entry sp; S1 = x_s1 = (SP0 - 320) & ~31, the base register s1;
   FR = x_fr the side-stack frame of class 3 (frame_addr of x_fpos), FL = x_fl its flag byte; SH(a) the shadow
   byte of a, shadow_addr a = 0x7fff8000 + a / 8 (the code: (a >> 3) + the base read from the cell 0xabff8, which
   the frame keeps at 176(s1)); c, m, t, tab, mt the blocks of the reader state, the model state, the file text and
   the two VLAN tables. Only the side-stack branch is stated (the flag cell is the record's constant 1 and the
   class-3 frame contract returns a frame, as chain_words_c.v states it): the real-stack fallback at 0x84dc4 and
   its probe loop are dead. The early return (0x84eb4, n >= 2 ^ 26) is refuted at ENTRY from lt_base's
   n < 2 ^ 26.

   SATISFIABILITY, one reason per cut (no premise contradicts another; checked by reading):
   - ENTRY: lt_base is the contract's premises and sa_frm0 its frm clause (the contract's own pre, nothing more).
   - K84eb8: the journal with own = [(3, pos)] is what frame_alloc_3's post gives from frames S = []; the frame
     words, the 36 entry shadow bytes and 176(s1) are the stores at 0x84d9c and 0x84e08-0x84eb0; k = 0, no block.
   - K84f84 / K84f98: one / two fresh blocks (malloc's and calloc's posts: 4096 <= res, appended, addressable by
     AR_shadow_law); flags / cap / the cursor are functions of the payload, the slots their stores 0x84ef4-0x84f38.
   - K85024 f: f < nfiles <= 4 (lt_nfiles in _s02.v); c, m hold seg_run of the payload at f; the counters' bounds
     hold of seg_run (gen + 1 per turn, refused and overflow by at most a text's length plus 64 per turn).
   - K850f8 f: as K85024 with the fresh text block of n + 1 bytes, n = seg_txt_n <= 65535.
   - K85208 f / K853bc f: the last turn (f + 1 = nfiles); m holds m_file (resp. m_cross of it) of the turn's
     text, the text block its C string; the label usable (0x85130).
   - K85414 f: c, m hold seg_after f; the label still usable (released at 0x85414, the cut's own pc).
   - K854a0 / K8559c / K856bc: c, m hold SegModel.run of the payload; the checks and queries write neither.
   - K857bc / K857cc: one / two fresh zeroed tables of 18 (cap + 1) and 20 (cap + 1) bytes (cap <= 39).
   - K858f4 i: i < m->n; tab holds vlan_init's entries and the guard, mt the model's table after seg[0 .. i)
     (m_decl_go over firstn i, which has not failed), n usable holding length tab.
   - K85ac4 i: as K858f4 i, with seg[i] not ignored, m_split of its name Some (p, vid), v usable holding (p, vid).
   - K85bd0: mt holds m_declared's table, 104(s1) its answer (-1 when the table filled up).
   - K85c1c .. K85c34: the blocks freed newest first, n still usable (released at 0x85c38).
   - K85c44: no harness block, the entry shadow pattern (both arrivals: the normal exit and the refuted early
     return), a6 = a7 = FR.
   - RET: the journal with own = [] (the frame released by meta_fill_f5 and the flag store), the callee-saved
     registers restored, a0 = 0, the entry's blocks. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI00 YC5d YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable SegSyms SegList SegPa SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import LLVMFuzzerTestOneInput_c SegInstA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ====================================== the frame (the harness's structure map section 3) ====================================== *)
(* the real frame (addi sp,sp,-320 at 0x84d34) and the registers it saves at SP0 - 8, - 16, ..., - 104
   (0x84d3c .. 0x84d6c): ra, s0, s1, s2, ..., s11 *)
Definition LT_FRAME : Z := 320.
Definition LT_SAVED : list (bv 5) := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
(* the side-stack frame: class 3 (li a0,288; jal frame_alloc_3 at 0x84da4 / 0x84da8), its header words (0x84e08 ..
   0x84e10: the magic, the description string, this function), the magic the release writes (0x85c4c), and the
   word at frame + 504 that holds the flag byte's address (ld a0,504(s2) at 0x85c64) *)
Definition LT_FCLS : Z := 3.
Definition LT_HDR0 : Z := 0x41b58ab3.
Definition LT_HDR0_DONE : Z := 0x45e0360e.
Definition LT_FLAGW : Z := 504.
(* the frame's objects (the description `5 32 20 7 v.i:357 96 40 9 label:602 176 4 5 r:625 192 18 9 probe:640
   256 4 8 n132:655`, the harness's structure map section 3.3) *)
Definition FO_V : Z := 32.
Definition FO_VID : Z := 48.
Definition FO_LABEL : Z := 96.
Definition FO_R : Z := 176.
Definition FO_PROBE : Z := 192.
Definition FO_N : Z := 256.
(* m_split's byte-class mask kept at 136(s1) (0x858c4 .. 0x858e0: '-', '.', ':', '_' as bits 0, 1, 13, 50) and the
   vid bound at 128(s1) (0x858cc) *)
Definition LT_MASK : Z := 0x4000000002003.
Definition LT_VIDMAX : Z := 4094.

(* the state of each frame object's shadow: true = usable (its bytes 00 / partial), false = out of scope (0xf8) *)
Record lfo := mkLFO { fo_v : bool; fo_label : bool; fo_r : bool; fo_probe : bool; fo_n : bool }.
Definition LFO0 : lfo := mkLFO false false false false false.
Definition LFO_L : lfo := mkLFO false true false false false.
Definition LFO_N : lfo := mkLFO false false false false true.
Definition LFO_NV : lfo := mkLFO true false false false true.
(* the 36 shadow bytes SH(FR) + 0 .. 35 (the harness's structure map section 3.4): the left guard f1 x 4, v (20 bytes: 00 00
   04), f2 x 5, label (40 bytes: 00 x 5), f2 x 5, r (4 bytes: 04), f2, probe (18 bytes: 00 00 02), f2 x 5, n (4
   bytes: 04), the right guard f3 x 3; each object 0xf8 when out of scope *)
Definition lt_fsh (o : lfo) : list Z :=
  [0xf1; 0xf1; 0xf1; 0xf1] ++ (if fo_v o then [0; 0; 4] else [0xf8; 0xf8; 0xf8]) ++ repeat 0xf2 5 ++
  (if fo_label o then repeat 0 5 else repeat 0xf8 5) ++ repeat 0xf2 5 ++
  (if fo_r o then [4] else [0xf8]) ++ [0xf2] ++ (if fo_probe o then [0; 0; 2] else [0xf8; 0xf8; 0xf8]) ++
  repeat 0xf2 5 ++ (if fo_n o then [4] else [0xf8]) ++ [0xf3; 0xf3; 0xf3].
Lemma lt_fsh_len : forall o, length (lt_fsh o) = 36%nat.
Proof. intros [[] [] [] [] []]; reflexivity. Qed.

(* ================================= the cut points (offsets from BASE = 0x84d34) ================================= *)
Definition LO_K84eb8 : Z := 0x184.  (* after the frame set-up and the size test *)
Definition LO_K84f84 : Z := 0x250.  (* malloc(16616) returned: c *)
Definition LO_K84f98 : Z := 0x264.  (* calloc(1, 9236) returned: m *)
Definition LO_K85024 : Z := 0x2f0.  (* the file loop's head, turn f *)
Definition LO_K850f8 : Z := 0x3c4.  (* malloc(n + 1) returned: the text *)
Definition LO_K85208 : Z := 0x4d4.  (* the last turn's m_file(m, text, NULL) returned *)
Definition LO_K853bc : Z := 0x688.  (* after m_cross, before reac_segconf_parse *)
Definition LO_K85414 : Z := 0x6e0.  (* free(text) returned *)
Definition LO_K854a0 : Z := 0x76c.  (* after the file loop *)
Definition LO_K8559c : Z := 0x868.  (* after the per-segment checks *)
Definition LO_K856bc : Z := 0x988.  (* after the refusal checks *)
Definition LO_K857bc : Z := 0xa88.  (* calloc(cap + 1, 18) returned: tab *)
Definition LO_K857cc : Z := 0xa98.  (* calloc(cap + 1, 20) returned: mt *)
Definition LO_K858f4 : Z := 0xbc0.  (* the head of the inlined m_declared loop, turn i *)
Definition LO_K85ac4 : Z := 0xd90.  (* m_split succeeded, v built *)
Definition LO_K85bd0 : Z := 0xe9c.  (* after m_declared *)
Definition LO_K85c1c : Z := 0xee8.  (* free(mt) returned *)
Definition LO_K85c24 : Z := 0xef0.  (* free(tab) returned *)
Definition LO_K85c2c : Z := 0xef8.  (* free(m) returned *)
Definition LO_K85c34 : Z := 0xf00.  (* free(c) returned *)
Definition LO_K85c44 : Z := 0xf10.  (* the frame release, reached from the normal exit *)
Definition LO_RET : Z := 0x100c.    (* ret *)

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

(* the s1 slots the file loop and the checks read (the map's live-register table at K85024 and its slot table): 8 FR (0x84fc8),
   16 flags, 24 FA0 = FR (0x84eb8), 32 and 40 cap, 48 &n, 56 &v, 64 SH(m + 0x14), 72 m + 0x20, 80 &label, 88
   nfiles, 96 &r, 104 &probe, 144 SH(FR), 160 c, 168 m, 184 &m->n (176 SHB is lt_frame's) *)
Definition LT_L (cx : lcx) (c m : Z) : list (Z * Z) :=
  [(8, x_fr cx); (16, x_flags cx); (24, x_fr cx); (32, x_cap cx); (40, x_cap cx); (48, x_fr cx + FO_N);
   (56, x_fr cx + FO_V); (64, shadow_addr (m + 0x14)); (72, m + 0x20); (80, x_fr cx + FO_LABEL); (88, x_nf cx);
   (96, x_fr cx + FO_R); (104, x_fr cx + FO_PROBE); (144, x_sh cx); (160, c); (168, m);
   (184, m + seg_spec.MC_N)].
(* the slots the m_declared loop reads that the file loop's list keeps *)
Definition LT_LV (cx : lcx) (c m : Z) : list (Z * Z) :=
  [(8, x_fr cx); (24, x_fr cx); (32, x_cap cx); (48, x_fr cx + FO_N); (56, x_fr cx + FO_V); (144, x_sh cx);
   (160, c); (168, m); (184, m + seg_spec.MC_N)].
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

(* LLVMFuzzerTestOneInput_contract's premises at image A's instance (lib/A/Prog/SegInstA.v), word for word
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

(* the frame part of every cut from K84eb8 to K85c44 (chain_words_d.v:141-155 with segconf's real-stack slots):
   the journal from the entry with the class-3 frame as its own frame and footprint longl, sp = s1 = S1, gp and
   tp kept, s0 = SP0, the 13 saved registers, the frame's three header words and its flag-byte word, the shadow
   base at 176(s1), and the 36 shadow bytes of the frame with each object as o says *)
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
  rdword (rdW W mem) (x_s1 cx + 176) = Some SHADOW_OFF /\
  sa_zs (rdW W mem) (x_sh cx) (lt_fsh o).
(* the image facts at the point: the read-only view, the contract's seg_himg (literals, table, m_key's words and
   roles, the stack-protector cells, longl) and longl[120] = 0, at the point's reader *)
Definition lt_img (cx : lcx) (rd : reader) : Prop :=
  arodata_okP SEGS RLO_A RHI_A B rd /\
  seg_himg SEGS B longlA mod40A catA wordsA rolesA gotwA guardA seg_litA_fz seg_litA_rc rd /\
  ltoi_GI longlA (x_j cx) rd.
(* the live blocks: the harness's own O (newest first) and the entry's *)
Definition lt_blocks (cx : lcx) ly S (O : list (Z * Z)) : Prop := Permutation (ablocks B ly S) (O ++ x_bl0 B cx).
(* a harness block: live, at or above 4096, 16-aligned, addressable (established at the allocator's return) *)
Definition lt_hblk ly S (rd : reader) (a n : Z) : Prop :=
  In (a, n) (ablocks B ly S) /\ 4096 <= a /\ a mod 16 = 0 /\ sa_addr rd a n.
(* the meter and the events: k spent (the journal's count), rem still to come, acc metered; every event is
   charged at most LT_U, XM_LTOI's unit *)
Definition LT_U : Z := mo_malloc MT 65536 + mo_free MT.
Definition lt_bud (cx : lcx) (S : astate) (k acc rem : Z) : Prop :=
  0 <= k /\ 0 <= rem /\ k + rem <= EV_LTOI (x_pl cx) /\
  mo_le MT (x_S cx) S acc /\ 0 <= acc /\ acc + rem * LT_U <= XM_LTOI MT (x_pl cx).
(* the part every cut from K84eb8 to K85c44 shares *)
Definition lt_core (cx : lcx) ly S (W : world SEGS) (regs : bvmap 5 word) mem md (k acc rem : Z) (o : lfo)
  (O : list (Z * Z)) : Prop :=
  lt_frame cx ly S W regs mem md k o /\ lt_img cx (rdW W mem) /\ lt_blocks cx ly S O /\ lt_bud cx S k acc rem.

(* ---------------- the cut statements: from a point to the return, under the entry's context ---------------- *)

(* 0x84d34: the function *)
Definition LT_ENTRY_stmt : Prop :=
  forall cx, lt_base cx -> sa_frm0 ->
  SRr SEGS (x_W cx) (cfg_at SEGS (BASE + AF_LLVMFuzzerTestOneInput) (x_regs cx) (x_mem cx) (x_md cx)) (lt_post cx).

(* 0x84eb8: the frame taken (a6 = a7 = FR), its header and 36 shadow bytes written, the size test passed;
   t0 = the shadow base, s4 = n, s8 = p, s5 = SH(FR); no block, no allocator event *)
Definition LT_K84eb8_stmt : Prop :=
  forall cx ly S W regs mem md acc,
  lt_base cx -> sa_frm0 ->
  lt_core cx ly S W regs mem md 0 acc (EV_LTOI (x_pl cx)) LFO0 [] ->
  getr regs 5 = w64 SHADOW_OFF -> getr regs 16 = w64 (x_fr cx) -> getr regs 17 = w64 (x_fr cx) ->
  getr regs 20 = w64 (x_n cx) -> getr regs 21 = w64 (x_sh cx) -> getr regs 24 = w64 (x_p cx) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_K84eb8) regs mem md) (lt_post cx).

(* 0x84f84: malloc(16616) returned c in a0; the three header bytes read: s4 / s8 the cursor, s9 = nfiles,
   s3 = FR; 16(s1) flags, 24(s1) FR, 40(s1) cap *)
Definition LT_K84f84_stmt : Prop :=
  forall cx ly S W regs mem md k acc (c : Z),
  lt_base cx -> sa_frm0 ->
  lt_core cx ly S W regs mem md k acc (7 + 2 * x_nf cx) LFO0 [(c, seg_spec.SEG_C_SIZE)] ->
  lt_hblk ly S (rdW W mem) c seg_spec.SEG_C_SIZE ->
  getr regs 10 = w64 c -> getr regs 19 = w64 (x_fr cx) -> getr regs 20 = w64 (x_curn cx 0) ->
  getr regs 21 = w64 (x_sh cx) -> getr regs 24 = w64 (x_cur cx 0) -> getr regs 25 = w64 (x_nf cx) ->
  lt_slots cx (rdW W mem) [(16, x_flags cx); (24, x_fr cx); (40, x_cap cx)] ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_K84f84) regs mem md) (lt_post cx).

(* 0x84f98: calloc(1, 9236) returned m in a0, all zero; s6 = c, s2 = 0x2000 *)
Definition LT_K84f98_stmt : Prop :=
  forall cx ly S W regs mem md k acc (c m : Z),
  lt_base cx -> sa_frm0 ->
  lt_core cx ly S W regs mem md k acc (6 + 2 * x_nf cx) LFO0 [(m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] ->
  lt_hblk ly S (rdW W mem) c seg_spec.SEG_C_SIZE -> lt_hblk ly S (rdW W mem) m seg_spec.SEG_M_SIZE ->
  zero_atA (rdW W mem) m seg_spec.SEG_M_SIZE ->
  getr regs 10 = w64 m -> getr regs 18 = w64 seg_spec.MC_N -> getr regs 19 = w64 (x_fr cx) ->
  getr regs 20 = w64 (x_curn cx 0) -> getr regs 21 = w64 (x_sh cx) -> getr regs 22 = w64 c ->
  getr regs 24 = w64 (x_cur cx 0) -> getr regs 25 = w64 (x_nf cx) ->
  lt_slots cx (rdW W mem) [(16, x_flags cx); (24, x_fr cx); (40, x_cap cx)] ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_K84f98) regs mem md) (lt_post cx).

(* 0x85024: the head of file turn f < nfiles: s2 = f, s4 / s8 the cursor after f records, s6 = returned, s9 =
   nfiles, s3 = -8; c and m hold the reader and model states after f turns (plain P_K138e8) *)
Definition LT_K85024_stmt (f : nat) : Prop :=
  forall cx ly S W regs mem md k acc (c m : Z),
  lt_base cx -> sa_frm0 -> Z.of_nat f < x_nf cx ->
  lt_core cx ly S W regs mem md k acc (6 + 2 * (x_nf cx - Z.of_nat f)) LFO0
    [(m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] ->
  lt_hblk ly S (rdW W mem) c seg_spec.SEG_C_SIZE -> lt_hblk ly S (rdW W mem) m seg_spec.SEG_M_SIZE ->
  getr regs 18 = w64 (Z.of_nat f) -> getr regs 19 = w64 (-8) -> getr regs 20 = w64 (x_curn cx f) ->
  getr regs 21 = w64 (x_sh cx) -> getr regs 22 = w64 (seg_spec.b2z (seg_spec.seg_ret (x_st cx f))) ->
  getr regs 24 = w64 (x_cur cx f) -> getr regs 25 = w64 (x_nf cx) ->
  lt_slots cx (rdW W mem) (LT_L cx c m) ->
  lt_cm (rdW W mem) c m (x_st cx f) ->
  lt_cnt f (seg_spec.seg_rc (x_st cx f)) (seg_spec.seg_mc (x_st cx f)) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_K85024) regs mem md) (lt_post cx).

(* 0x850f8: malloc(n + 1) returned the text block t in a0 (plain P_K13984): s4 = n, s8 = the cursor after the
   turn's lb and u16, s10 = lb, s11 = n' (the bytes taken); 152(s1) = the count after the header *)
Definition LT_K850f8_stmt (f : nat) : Prop :=
  forall cx ly S W regs mem md k acc (c m t : Z),
  lt_base cx -> sa_frm0 -> Z.of_nat f < x_nf cx ->
  lt_core cx ly S W regs mem md k acc (5 + 2 * (x_nf cx - Z.of_nat f)) LFO0
    [(t, x_tn cx f); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] ->
  lt_hblk ly S (rdW W mem) c seg_spec.SEG_C_SIZE -> lt_hblk ly S (rdW W mem) m seg_spec.SEG_M_SIZE ->
  lt_hblk ly S (rdW W mem) t (x_tn cx f) ->
  getr regs 10 = w64 t -> getr regs 18 = w64 (Z.of_nat f) -> getr regs 19 = w64 (-8) ->
  getr regs 20 = w64 (seg_spec.seg_txt_n (x_pl cx) f) -> getr regs 21 = w64 (x_sh cx) ->
  getr regs 22 = w64 (seg_spec.b2z (seg_spec.seg_ret (x_st cx f))) ->
  getr regs 24 = w64 (seg_spec.seg_turn_at (x_pl cx) (x_p cx) f) -> getr regs 25 = w64 (x_nf cx) ->
  getr regs 26 = w64 (seg_spec.seg_lb (x_pl cx) f) -> getr regs 27 = w64 (seg_spec.seg_turn_np (x_pl cx) f) ->
  lt_slots cx (rdW W mem) (LT_L cx c m ++ [(152, Z.of_nat (length (seg_spec.seg_turn_tail (x_pl cx) f)))]) ->
  lt_cm (rdW W mem) c m (x_st cx f) ->
  lt_cnt f (seg_spec.seg_rc (x_st cx f)) (seg_spec.seg_mc (x_st cx f)) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_K850f8) regs mem md) (lt_post cx).

(* 0x85208: the last turn (f + 1 = nfiles), after m_file(m, text, NULL): s7 = t, s10 = (m + 0x2000) >> 3,
   s11 = n'; 120(s1) returned, 128(s1) f + 1, 136(s1) the cursor after the header, 152(s1) its count; the label
   usable; t holds the turn's text *)
Definition LT_K85208_stmt (f : nat) : Prop :=
  forall cx ly S W regs mem md k acc (c m t : Z),
  lt_base cx -> sa_frm0 -> Z.of_nat f + 1 = x_nf cx ->
  lt_core cx ly S W regs mem md k acc (5 + 2 * (x_nf cx - Z.of_nat f)) LFO_L
    [(t, x_tn cx f); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] ->
  lt_hblk ly S (rdW W mem) c seg_spec.SEG_C_SIZE -> lt_hblk ly S (rdW W mem) m seg_spec.SEG_M_SIZE ->
  lt_hblk ly S (rdW W mem) t (x_tn cx f) ->
  getr regs 23 = w64 t -> getr regs 26 = w64 ((m + seg_spec.MC_N) / 8) ->
  getr regs 27 = w64 (seg_spec.seg_turn_np (x_pl cx) f) ->
  lt_slots cx (rdW W mem) (LT_L cx c m ++
    [(120, seg_spec.b2z (seg_spec.seg_ret (x_st cx f))); (128, Z.of_nat f + 1);
     (136, seg_spec.seg_turn_at (x_pl cx) (x_p cx) f);
     (152, Z.of_nat (length (seg_spec.seg_turn_tail (x_pl cx) f)))]) ->
  sa_rconf (rdW W mem) c (seg_spec.seg_rc (x_st cx f)) ->
  sa_mconf (rdW W mem) m (SegModel.m_file (seg_spec.seg_mc (x_st cx f)) (seg_spec.seg_txt (x_pl cx) f) None) ->
  sa_str (rdW W mem) t (seg_spec.seg_txt (x_pl cx) f) ->
  lt_cnt (Datatypes.S f) (seg_spec.seg_rc (x_st cx f))
    (SegModel.m_file (seg_spec.seg_mc (x_st cx f)) (seg_spec.seg_txt (x_pl cx) f) None) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_K85208) regs mem md) (lt_post cx).

(* 0x853bc: the last turn after m_cross: s2 = SH(m + 0x2000), s7 = t, s11 = n'; 112(s1) = (m + 0x2000) >> 3;
   m holds m_cross of K85208's model *)
Definition LT_K853bc_stmt (f : nat) : Prop :=
  forall cx ly S W regs mem md k acc (c m t : Z),
  lt_base cx -> sa_frm0 -> Z.of_nat f + 1 = x_nf cx ->
  lt_core cx ly S W regs mem md k acc (5 + 2 * (x_nf cx - Z.of_nat f)) LFO_L
    [(t, x_tn cx f); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] ->
  lt_hblk ly S (rdW W mem) c seg_spec.SEG_C_SIZE -> lt_hblk ly S (rdW W mem) m seg_spec.SEG_M_SIZE ->
  lt_hblk ly S (rdW W mem) t (x_tn cx f) ->
  getr regs 18 = w64 (shadow_addr (m + seg_spec.MC_N)) -> getr regs 23 = w64 t ->
  getr regs 27 = w64 (seg_spec.seg_turn_np (x_pl cx) f) ->
  lt_slots cx (rdW W mem) (LT_L cx c m ++
    [(112, (m + seg_spec.MC_N) / 8); (120, seg_spec.b2z (seg_spec.seg_ret (x_st cx f))); (128, Z.of_nat f + 1);
     (136, seg_spec.seg_turn_at (x_pl cx) (x_p cx) f);
     (152, Z.of_nat (length (seg_spec.seg_turn_tail (x_pl cx) f)))]) ->
  sa_rconf (rdW W mem) c (seg_spec.seg_rc (x_st cx f)) ->
  sa_mconf (rdW W mem) m
    (SegModel.m_cross (SegModel.m_file (seg_spec.seg_mc (x_st cx f)) (seg_spec.seg_txt (x_pl cx) f) None)) ->
  sa_str (rdW W mem) t (seg_spec.seg_txt (x_pl cx) f) ->
  lt_cnt (Datatypes.S f) (seg_spec.seg_rc (x_st cx f))
    (SegModel.m_cross (SegModel.m_file (seg_spec.seg_mc (x_st cx f)) (seg_spec.seg_txt (x_pl cx) f) None)) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_K853bc) regs mem md) (lt_post cx).

(* 0x85414: turn f done, free(text) returned (plain P_K13ad8): s2 = f + 1, s4 / s8 the cursor after f + 1
   records, s6 = returned, s10 = (m + 0x2000) >> 3, s3 = -8; the label still usable (released here); c and m hold
   seg_after f *)
Definition LT_K85414_stmt (f : nat) : Prop :=
  forall cx ly S W regs mem md k acc (c m : Z),
  lt_base cx -> sa_frm0 -> Z.of_nat f < x_nf cx ->
  lt_core cx ly S W regs mem md k acc (6 + 2 * (x_nf cx - Z.of_nat (Datatypes.S f))) LFO_L
    [(m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] ->
  lt_hblk ly S (rdW W mem) c seg_spec.SEG_C_SIZE -> lt_hblk ly S (rdW W mem) m seg_spec.SEG_M_SIZE ->
  getr regs 18 = w64 (Z.of_nat (Datatypes.S f)) -> getr regs 19 = w64 (-8) ->
  getr regs 20 = w64 (x_curn cx (Datatypes.S f)) -> getr regs 21 = w64 (x_sh cx) ->
  getr regs 22 = w64 (seg_spec.b2z (seg_spec.seg_ret (x_af cx f))) ->
  getr regs 24 = w64 (x_cur cx (Datatypes.S f)) -> getr regs 25 = w64 (x_nf cx) ->
  getr regs 26 = w64 ((m + seg_spec.MC_N) / 8) ->
  lt_slots cx (rdW W mem) (LT_L cx c m) ->
  lt_cm (rdW W mem) c m (x_af cx f) ->
  lt_cnt (Datatypes.S f) (seg_spec.seg_rc (x_af cx f)) (seg_spec.seg_mc (x_af cx f)) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_K85414) regs mem md) (lt_post cx).

(* 0x854a0: after the file loop (plain P_K13ae0): a1 = m, s6 = returned, s10 = (m + 0x2000) >> 3; c and m hold
   SegModel.run of the payload *)
Definition LT_K854a0_stmt : Prop :=
  forall cx ly S W regs mem md k acc (c m : Z),
  lt_base cx -> sa_frm0 ->
  lt_core cx ly S W regs mem md k acc 6 LFO0 [(m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] ->
  lt_hblk ly S (rdW W mem) c seg_spec.SEG_C_SIZE -> lt_hblk ly S (rdW W mem) m seg_spec.SEG_M_SIZE ->
  getr regs 11 = w64 m -> getr regs 22 = w64 (seg_spec.b2z (seg_spec.seg_ret (x_run cx))) ->
  getr regs 26 = w64 ((m + seg_spec.MC_N) / 8) ->
  lt_slots cx (rdW W mem) (LT_L cx c m) ->
  lt_cm (rdW W mem) c m (x_run cx) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_K854a0) regs mem md) (lt_post cx).

(* 0x8559c: after check_segments and the per-segment checks: s11 = SH(m + 0x2000) *)
Definition LT_K8559c_stmt : Prop :=
  forall cx ly S W regs mem md k acc (c m : Z),
  lt_base cx -> sa_frm0 ->
  lt_core cx ly S W regs mem md k acc 6 LFO0 [(m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] ->
  lt_hblk ly S (rdW W mem) c seg_spec.SEG_C_SIZE -> lt_hblk ly S (rdW W mem) m seg_spec.SEG_M_SIZE ->
  getr regs 27 = w64 (shadow_addr (m + seg_spec.MC_N)) ->
  lt_slots cx (rdW W mem) (LT_L cx c m) ->
  lt_cm (rdW W mem) c m (x_run cx) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_K8559c) regs mem md) (lt_post cx).

(* 0x856bc: after check_refusals and the refusal checks: 152(s1) = SH(m + 0x2000) *)
Definition LT_K856bc_stmt : Prop :=
  forall cx ly S W regs mem md k acc (c m : Z),
  lt_base cx -> sa_frm0 ->
  lt_core cx ly S W regs mem md k acc 6 LFO0 [(m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] ->
  lt_hblk ly S (rdW W mem) c seg_spec.SEG_C_SIZE -> lt_hblk ly S (rdW W mem) m seg_spec.SEG_M_SIZE ->
  lt_slots cx (rdW W mem) (LT_L cx c m ++ [(152, shadow_addr (m + seg_spec.MC_N))]) ->
  lt_cm (rdW W mem) c m (x_run cx) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_K856bc) regs mem md) (lt_post cx).

(* 0x857bc: calloc(cap + 1, 18) returned tab in a0, all zero: s2 = cap, s3 = cap + 1, s10 = SH(m + 0x2000) *)
Definition LT_K857bc_stmt : Prop :=
  forall cx ly S W regs mem md k acc (c m tab : Z),
  lt_base cx -> sa_frm0 ->
  lt_core cx ly S W regs mem md k acc 5 LFO0
    [(tab, x_tabn cx); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] ->
  lt_hblk ly S (rdW W mem) c seg_spec.SEG_C_SIZE -> lt_hblk ly S (rdW W mem) m seg_spec.SEG_M_SIZE ->
  lt_hblk ly S (rdW W mem) tab (x_tabn cx) -> zero_atA (rdW W mem) tab (x_tabn cx) ->
  getr regs 10 = w64 tab -> getr regs 18 = w64 (x_cap cx) -> getr regs 19 = w64 (x_cap cx + 1) ->
  getr regs 26 = w64 (shadow_addr (m + seg_spec.MC_N)) ->
  lt_slots cx (rdW W mem) (LT_L cx c m ++ [(152, shadow_addr (m + seg_spec.MC_N))]) ->
  lt_cm (rdW W mem) c m (x_run cx) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_K857bc) regs mem md) (lt_post cx).

(* 0x857cc: calloc(cap + 1, 20) returned mt in a0, all zero (plain P_K13cac): s2 = cap, s8 = tab *)
Definition LT_K857cc_stmt : Prop :=
  forall cx ly S W regs mem md k acc (c m tab mt : Z),
  lt_base cx -> sa_frm0 ->
  lt_core cx ly S W regs mem md k acc 4 LFO0
    [(mt, x_mtn cx); (tab, x_tabn cx); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] ->
  lt_hblk ly S (rdW W mem) c seg_spec.SEG_C_SIZE -> lt_hblk ly S (rdW W mem) m seg_spec.SEG_M_SIZE ->
  lt_hblk ly S (rdW W mem) tab (x_tabn cx) -> lt_hblk ly S (rdW W mem) mt (x_mtn cx) ->
  zero_atA (rdW W mem) tab (x_tabn cx) -> zero_atA (rdW W mem) mt (x_mtn cx) ->
  getr regs 10 = w64 mt -> getr regs 18 = w64 (x_cap cx) -> getr regs 24 = w64 tab ->
  getr regs 26 = w64 (shadow_addr (m + seg_spec.MC_N)) ->
  lt_slots cx (rdW W mem) (LT_L cx c m ++ [(152, shadow_addr (m + seg_spec.MC_N))]) ->
  lt_cm (rdW W mem) c m (x_run cx) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_K857cc) regs mem md) (lt_post cx).

(* the tables at the m_declared loop: tab holds vlan_init's entries and the guard tab[cap] (0x857f0, 0x85830,
   0x85850), n (frame + 256, usable) the count, mt the model's table after seg[0 .. i), 120(s1) its length mn,
   104(s1) the entries added *)
Definition lt_tabs (cx : lcx) (rd : reader) (tab mt : Z) (t : list (list Z * Z)) : Prop :=
  Z.of_nat (length (x_tab0 cx)) <= x_cap cx < 40 /\
  sa_rtab rd tab (x_tab0 cx) /\ sa_guardtab rd tab (x_cap cx) /\
  sa_val rd (x_fr cx + FO_N) 4 (Z.of_nat (length (x_tab0 cx))) /\
  sa_mtab rd mt t /\ Z.of_nat (length t) <= x_cap cx.

(* 0x858f4: the head of m_declared's turn i < m->n: a5 = the shadow base, a6 = m, s4 = 4, s5 = SH(FR), s6 =
   s11 = &m->seg[i], s10 = -&m->seg[i], s9 = i, s7 = -8, s8 = tab; n usable, v out of scope *)
Definition LT_K858f4_stmt (i : nat) : Prop :=
  forall cx ly S W regs mem md k acc (c m tab mt : Z),
  lt_base cx -> sa_frm0 -> (i < length (SegModel.mc_seg (x_mcF cx)))%nat ->
  lt_core cx ly S W regs mem md k acc 4 LFO_N
    [(mt, x_mtn cx); (tab, x_tabn cx); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] ->
  lt_hblk ly S (rdW W mem) c seg_spec.SEG_C_SIZE -> lt_hblk ly S (rdW W mem) m seg_spec.SEG_M_SIZE ->
  lt_hblk ly S (rdW W mem) tab (x_tabn cx) -> lt_hblk ly S (rdW W mem) mt (x_mtn cx) ->
  getr regs 15 = w64 SHADOW_OFF -> getr regs 16 = w64 m -> getr regs 20 = w64 4 -> getr regs 21 = w64 (x_sh cx) ->
  getr regs 22 = w64 (seg_spec.mseg_addr m i) -> getr regs 23 = w64 (-8) -> getr regs 24 = w64 tab ->
  getr regs 25 = w64 (Z.of_nat i) -> getr regs 26 = w64 (- seg_spec.mseg_addr m i) ->
  getr regs 27 = w64 (seg_spec.mseg_addr m i) ->
  0 <= fst (x_decl cx i) ->
  lt_slots cx (rdW W mem) (LT_LV cx c m ++
    [(96, mt + 16); (104, fst (x_decl cx i)); (112, mt); (120, Z.of_nat (length (snd (x_decl cx i))));
     (128, LT_VIDMAX); (136, LT_MASK); (152, shadow_addr (m + seg_spec.MC_N))]) ->
  lt_cm (rdW W mem) c m (x_run cx) ->
  lt_tabs cx (rdW W mem) tab mt (snd (x_decl cx i)) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_K858f4) regs mem md) (lt_post cx).

(* 0x85ac4: turn i, seg[i] not ignored and m_split of its name gave (p, vid): v = frame + 32 usable, holding p
   and its NUL (memcpy 0x85aa0, sb 0x85abc) and vid at frame + 48 (sw 0x85ac0); s2 = vid; 88(s1) = tab *)
Definition LT_K85ac4_stmt (i : nat) : Prop :=
  forall cx ly S W regs mem md k acc (c m tab mt : Z) (par : list Z) (vid : Z),
  lt_base cx -> sa_frm0 -> (i < length (SegModel.mc_seg (x_mcF cx)))%nat ->
  lt_core cx ly S W regs mem md k acc 4 LFO_NV
    [(mt, x_mtn cx); (tab, x_tabn cx); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] ->
  lt_hblk ly S (rdW W mem) c seg_spec.SEG_C_SIZE -> lt_hblk ly S (rdW W mem) m seg_spec.SEG_M_SIZE ->
  lt_hblk ly S (rdW W mem) tab (x_tabn cx) -> lt_hblk ly S (rdW W mem) mt (x_mtn cx) ->
  SegModel.ms_ignore (x_seg cx i) = false ->
  SegModel.m_split (SegModel.ms_name (x_seg cx i)) = Some (par, vid) ->
  getr regs 15 = w64 SHADOW_OFF -> getr regs 18 = w64 vid -> getr regs 22 = w64 (seg_spec.mseg_addr m i) ->
  getr regs 23 = w64 (-8) -> getr regs 25 = w64 (Z.of_nat i) -> getr regs 26 = w64 (- seg_spec.mseg_addr m i) ->
  getr regs 27 = w64 (seg_spec.mseg_addr m i) ->
  0 <= fst (x_decl cx i) ->
  lt_slots cx (rdW W mem) (LT_LV cx c m ++
    [(88, tab); (96, mt + 16); (104, fst (x_decl cx i)); (112, mt); (120, Z.of_nat (length (snd (x_decl cx i))));
     (128, LT_VIDMAX); (136, LT_MASK); (152, shadow_addr (m + seg_spec.MC_N))]) ->
  lt_cm (rdW W mem) c m (x_run cx) ->
  lt_tabs cx (rdW W mem) tab mt (snd (x_decl cx i)) ->
  sa_strz (rdW W mem) (x_fr cx + FO_V) par -> sa_val (rdW W mem) (x_fr cx + FO_VID) 4 vid ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_K85ac4) regs mem md) (lt_post cx).

(* 0x85bd0: after m_declared: a6 = m, s5 = SH(FR), s8 = tab; 104(s1) the answer (want; -1 as its 64-bit word
   when the table filled up), 112(s1) mt, 120(s1) mn; mt holds m_declared's table *)
Definition LT_K85bd0_stmt : Prop :=
  forall cx ly S W regs mem md k acc (c m tab mt : Z),
  lt_base cx -> sa_frm0 ->
  lt_core cx ly S W regs mem md k acc 4 LFO_N
    [(mt, x_mtn cx); (tab, x_tabn cx); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] ->
  lt_hblk ly S (rdW W mem) c seg_spec.SEG_C_SIZE -> lt_hblk ly S (rdW W mem) m seg_spec.SEG_M_SIZE ->
  lt_hblk ly S (rdW W mem) tab (x_tabn cx) -> lt_hblk ly S (rdW W mem) mt (x_mtn cx) ->
  getr regs 16 = w64 m -> getr regs 21 = w64 (x_sh cx) -> getr regs 24 = w64 tab ->
  lt_slots cx (rdW W mem)
    [(8, x_fr cx); (24, x_fr cx); (32, x_cap cx); (48, x_fr cx + FO_N);
     (104, fst (SegModel.m_declared (x_mcF cx) (x_tab0 cx) (x_cap cx)) mod 2 ^ 64); (112, mt);
     (120, Z.of_nat (length (snd (SegModel.m_declared (x_mcF cx) (x_tab0 cx) (x_cap cx))))); (160, c); (168, m)] ->
  lt_cm (rdW W mem) c m (x_run cx) ->
  lt_tabs cx (rdW W mem) tab mt (snd (SegModel.m_declared (x_mcF cx) (x_tab0 cx) (x_cap cx))) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_K85bd0) regs mem md) (lt_post cx).

(* 0x85c1c: free(mt) returned (plain P_K13f40 after the first free): s2 = c, s3 = m, s8 = tab *)
Definition LT_K85c1c_stmt : Prop :=
  forall cx ly S W regs mem md k acc (c m tab : Z),
  lt_base cx -> sa_frm0 ->
  lt_core cx ly S W regs mem md k acc 3 LFO_N [(tab, x_tabn cx); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] ->
  lt_hblk ly S (rdW W mem) c seg_spec.SEG_C_SIZE -> lt_hblk ly S (rdW W mem) m seg_spec.SEG_M_SIZE ->
  lt_hblk ly S (rdW W mem) tab (x_tabn cx) ->
  getr regs 18 = w64 c -> getr regs 19 = w64 m -> getr regs 21 = w64 (x_sh cx) -> getr regs 24 = w64 tab ->
  lt_slots cx (rdW W mem) [(8, x_fr cx); (24, x_fr cx)] ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_K85c1c) regs mem md) (lt_post cx).

(* 0x85c24: free(tab) returned: s2 = c, s3 = m *)
Definition LT_K85c24_stmt : Prop :=
  forall cx ly S W regs mem md k acc (c m : Z),
  lt_base cx -> sa_frm0 ->
  lt_core cx ly S W regs mem md k acc 2 LFO_N [(m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] ->
  lt_hblk ly S (rdW W mem) c seg_spec.SEG_C_SIZE -> lt_hblk ly S (rdW W mem) m seg_spec.SEG_M_SIZE ->
  getr regs 18 = w64 c -> getr regs 19 = w64 m -> getr regs 21 = w64 (x_sh cx) ->
  lt_slots cx (rdW W mem) [(8, x_fr cx); (24, x_fr cx)] ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_K85c24) regs mem md) (lt_post cx).

(* 0x85c2c: free(m) returned: s2 = c *)
Definition LT_K85c2c_stmt : Prop :=
  forall cx ly S W regs mem md k acc (c : Z),
  lt_base cx -> sa_frm0 ->
  lt_core cx ly S W regs mem md k acc 1 LFO_N [(c, seg_spec.SEG_C_SIZE)] ->
  lt_hblk ly S (rdW W mem) c seg_spec.SEG_C_SIZE ->
  getr regs 18 = w64 c -> getr regs 21 = w64 (x_sh cx) ->
  lt_slots cx (rdW W mem) [(8, x_fr cx); (24, x_fr cx)] ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_K85c2c) regs mem md) (lt_post cx).

(* 0x85c34: free(c) returned: no harness block, every event spent; n still usable *)
Definition LT_K85c34_stmt : Prop :=
  forall cx ly S W regs mem md k acc,
  lt_base cx -> sa_frm0 ->
  lt_core cx ly S W regs mem md k acc 0 LFO_N [] ->
  getr regs 21 = w64 (x_sh cx) ->
  lt_slots cx (rdW W mem) [(8, x_fr cx); (24, x_fr cx)] ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_K85c34) regs mem md) (lt_post cx).

(* 0x85c44: the release, with a6 = a7 = FR and s5 = SH(FR); the frame's shadow the entry pattern *)
Definition LT_K85c44_stmt : Prop :=
  forall cx ly S W regs mem md k acc,
  lt_base cx -> sa_frm0 ->
  lt_core cx ly S W regs mem md k acc 0 LFO0 [] ->
  getr regs 16 = w64 (x_fr cx) -> getr regs 17 = w64 (x_fr cx) -> getr regs 21 = w64 (x_sh cx) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_K85c44) regs mem md) (lt_post cx).

(* 0x85d40: the ret: the frame released (the journal's own frames []), the callee-saved registers and ra as at
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
Definition LTA_K84eb8 (B : asyms) (MT : ameter_ops) : Prop := forall fx1 : YK11.FPState, LT_K84eb8_stmt (fx := fx1) B MT.
Definition LTA_K84f84 (B : asyms) (MT : ameter_ops) : Prop := forall fx1 : YK11.FPState, LT_K84f84_stmt (fx := fx1) B MT.
Definition LTA_K84f98 (B : asyms) (MT : ameter_ops) : Prop := forall fx1 : YK11.FPState, LT_K84f98_stmt (fx := fx1) B MT.
Definition LTA_K85024 (B : asyms) (MT : ameter_ops) (f : nat) : Prop :=
  forall fx1 : YK11.FPState, LT_K85024_stmt (fx := fx1) B MT f.
Definition LTA_K850f8 (B : asyms) (MT : ameter_ops) (f : nat) : Prop :=
  forall fx1 : YK11.FPState, LT_K850f8_stmt (fx := fx1) B MT f.
Definition LTA_K85208 (B : asyms) (MT : ameter_ops) (f : nat) : Prop :=
  forall fx1 : YK11.FPState, LT_K85208_stmt (fx := fx1) B MT f.
Definition LTA_K853bc (B : asyms) (MT : ameter_ops) (f : nat) : Prop :=
  forall fx1 : YK11.FPState, LT_K853bc_stmt (fx := fx1) B MT f.
Definition LTA_K85414 (B : asyms) (MT : ameter_ops) (f : nat) : Prop :=
  forall fx1 : YK11.FPState, LT_K85414_stmt (fx := fx1) B MT f.
Definition LTA_K854a0 (B : asyms) (MT : ameter_ops) : Prop := forall fx1 : YK11.FPState, LT_K854a0_stmt (fx := fx1) B MT.
Definition LTA_K8559c (B : asyms) (MT : ameter_ops) : Prop := forall fx1 : YK11.FPState, LT_K8559c_stmt (fx := fx1) B MT.
Definition LTA_K856bc (B : asyms) (MT : ameter_ops) : Prop := forall fx1 : YK11.FPState, LT_K856bc_stmt (fx := fx1) B MT.
Definition LTA_K857bc (B : asyms) (MT : ameter_ops) : Prop := forall fx1 : YK11.FPState, LT_K857bc_stmt (fx := fx1) B MT.
Definition LTA_K857cc (B : asyms) (MT : ameter_ops) : Prop := forall fx1 : YK11.FPState, LT_K857cc_stmt (fx := fx1) B MT.
Definition LTA_K858f4 (B : asyms) (MT : ameter_ops) (i : nat) : Prop :=
  forall fx1 : YK11.FPState, LT_K858f4_stmt (fx := fx1) B MT i.
Definition LTA_K85ac4 (B : asyms) (MT : ameter_ops) (i : nat) : Prop :=
  forall fx1 : YK11.FPState, LT_K85ac4_stmt (fx := fx1) B MT i.
Definition LTA_K85bd0 (B : asyms) (MT : ameter_ops) : Prop := forall fx1 : YK11.FPState, LT_K85bd0_stmt (fx := fx1) B MT.
Definition LTA_K85c1c (B : asyms) (MT : ameter_ops) : Prop := forall fx1 : YK11.FPState, LT_K85c1c_stmt (fx := fx1) B MT.
Definition LTA_K85c24 (B : asyms) (MT : ameter_ops) : Prop := forall fx1 : YK11.FPState, LT_K85c24_stmt (fx := fx1) B MT.
Definition LTA_K85c2c (B : asyms) (MT : ameter_ops) : Prop := forall fx1 : YK11.FPState, LT_K85c2c_stmt (fx := fx1) B MT.
Definition LTA_K85c34 (B : asyms) (MT : ameter_ops) : Prop := forall fx1 : YK11.FPState, LT_K85c34_stmt (fx := fx1) B MT.
Definition LTA_K85c44 (B : asyms) (MT : ameter_ops) : Prop := forall fx1 : YK11.FPState, LT_K85c44_stmt (fx := fx1) B MT.
Definition LTA_RET (B : asyms) (MT : ameter_ops) : Prop := forall fx1 : YK11.FPState, LT_RET_stmt (fx := fx1) B MT.
End lta.

(* ---- the segment statements (the harness's structure map section 2.3): each file group proves one of these, with the callee
   contracts, the runtime entries and the walk hypotheses as Section hypotheses of its own file; the continuation
   at every FP state, the conclusion at the FP state of the segment's start ---- *)
Section st. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
Variable B : asyms.
Variable MT : ameter_ops.
(* S00 0x84d34 .. 0x84eb4: the prologue, the cells, frame_alloc_3(288), the header and the 36 shadow bytes, the
   size test (its taken edge to 0x85c44 refuted by n < 2 ^ 26; the real-stack fallback dead) *)
Definition lt_seg_S00_stmt : Prop := LTA_K84eb8 B MT -> LT_ENTRY_stmt B MT.
(* S01 0x84eb8 .. 0x84f80: the three header bytes (checks 1-3) and malloc(16616) *)
Definition lt_seg_S01_stmt : Prop := LTA_K84f84 B MT -> LT_K84eb8_stmt B MT.
(* S02 0x84f84 .. 0x84f94: calloc(1, 9236) *)
Definition lt_seg_S02_stmt : Prop := LTA_K84f98 B MT -> LT_K84f84_stmt B MT.
(* S03 0x84f98 .. 0x85020: the NULL tests of c and m (refuted), the slots, reac_segconf_init(c), to turn 0 *)
Definition lt_seg_S03_stmt : Prop := LTA_K85024 B MT 0 -> LT_K84f98_stmt B MT.
(* S04 0x85024 .. 0x850f4: lb, the u16, the take (checks 4-6), memchr, malloc(n + 1) *)
Definition lt_seg_S04_stmt : Prop := forall f, LTA_K850f8 B MT f -> LT_K85024_stmt B MT f.
(* S05 0x850f8 .. 0x85204 and 0x85404 .. 0x85410: the NULL test (refuted), memcpy, the NUL (check 7), the label
   (snprintf or memset of longl), and either m_file / parse_file (check 8) / free(text) to K85414 f, or, on the
   last turn, m_file(m, text, NULL) to K85208 f *)
Definition lt_seg_S05_stmt : Prop := forall f, LTA_K85208 B MT f -> LTA_K85414 B MT f -> LT_K850f8_stmt B MT f.
(* S06 0x85208 .. 0x853b8: the inlined m_cross loop with its m_refuse calls (checks 9-17) *)
Definition lt_seg_S06_stmt : Prop := forall f, LTA_K853bc B MT f -> LT_K85208_stmt B MT f.
(* S07 0x853bc .. 0x85410: reac_segconf_parse (check 18), returned, free(text) *)
Definition lt_seg_S07_stmt : Prop := forall f, LTA_K85414 B MT f -> LT_K853bc_stmt B MT f.
(* S08 0x85414 .. 0x85430: the label out of scope and the latch, to the next turn or out of the loop *)
Definition lt_seg_S08_stmt : Prop :=
  forall f, LTA_K85024 B MT (Datatypes.S f) -> LTA_K854a0 B MT -> LT_K85414_stmt B MT f.
(* S09 0x854a0 .. 0x85598: check_segments and the per-segment loop of nine calls (checks 19, 20) *)
Definition lt_seg_S09_stmt : Prop := LTA_K8559c B MT -> LT_K854a0_stmt B MT.
(* S10 0x8559c .. 0x856b8: check_refusals and the refusal loop (checks 21-24) *)
Definition lt_seg_S10_stmt : Prop := LTA_K856bc B MT -> LT_K8559c_stmt B MT.
(* S11 0x856bc .. 0x857b8: the probe loop, the "nosuch0" pair (checks 25, 26), calloc(cap + 1, 18) *)
Definition lt_seg_S11_stmt : Prop := LTA_K857bc B MT -> LT_K856bc_stmt B MT.
(* S12 0x857bc .. 0x857c8: calloc(cap + 1, 20) *)
Definition lt_seg_S12_stmt : Prop := LTA_K857cc B MT -> LT_K857bc_stmt B MT.
(* S13 0x857cc .. 0x858f0: the NULL tests (refuted), the guard memset, n in scope, the "enp1s0" entries (checks
   27-29), to m_declared's turn 0 or, m->n = 0, past it *)
Definition lt_seg_S13_stmt : Prop := LTA_K858f4 B MT 0 -> LTA_K85bd0 B MT -> LT_K857cc_stmt B MT.
(* S14 0x858f4 .. 0x85ac0 with the continue join: v in scope, ignore, strrchr, the digit and parent loops,
   memcpy (checks 30-35), to K85ac4 i, or the next turn, or past the loop *)
Definition lt_seg_S14_stmt : Prop :=
  forall i, LTA_K85ac4 B MT i -> LTA_K858f4 B MT (Datatypes.S i) -> LTA_K85bd0 B MT -> LT_K858f4_stmt B MT i.
(* S15 0x85ac4 .. 0x85b8c, the join and the -1 exit: the dup loop with strcmp, memcpy of v (checks 33, 36) *)
Definition lt_seg_S15_stmt : Prop :=
  forall i, LTA_K858f4 B MT (Datatypes.S i) -> LTA_K85bd0 B MT -> LT_K85ac4_stmt B MT i.
(* S16 0x85bd0 .. 0x85c18: reac_segconf_declared, check_declared, free(mt) *)
Definition lt_seg_S16_stmt : Prop := LTA_K85c1c B MT -> LT_K85bd0_stmt B MT.
(* S17 0x85c1c .. 0x85c20: free(tab) *)
Definition lt_seg_S17_stmt : Prop := LTA_K85c24 B MT -> LT_K85c1c_stmt B MT.
(* S18 0x85c24 .. 0x85c28: free(m) *)
Definition lt_seg_S18_stmt : Prop := LTA_K85c2c B MT -> LT_K85c24_stmt B MT.
(* S19 0x85c2c .. 0x85c30: free(c) *)
Definition lt_seg_S19_stmt : Prop := LTA_K85c34 B MT -> LT_K85c2c_stmt B MT.
(* S20 0x85c34 .. 0x85c40: n out of scope, a6 / a7 reloaded *)
Definition lt_seg_S20_stmt : Prop := LTA_K85c44 B MT -> LT_K85c34_stmt B MT.
(* S21 0x85c44 .. 0x85d3c: the frame-done word, meta_fill_f5(SH(FR), 64), the flag store, a0 = 0, the epilogue
   (the real-stack release 0x85c70 .. 0x85cfc dead) *)
Definition lt_seg_S21_stmt : Prop := LTA_RET B MT -> LT_K85c44_stmt B MT.
(* the ret at 0x85d40, to the post *)
Definition lt_seg_RET_stmt : Prop := LT_RET_stmt B MT.
End st.
