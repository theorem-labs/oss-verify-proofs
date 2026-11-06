(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the three parts of sup_call's ASan walk (plugin-hostd/fuzz_command, 0x8a95c)
   and the states where they meet, in the form of sup_connect's walk (sup_connect_s0.v):
   - the prologue (0x8a95c .. 0x8a9cc): the frame, g_rec.ncalls tested against 16, and record()'s two arms, the
     table arm (ncalls := n + 1, the slot g_rec + 16 + 56 n) and the spill arm (rec_calls_free on record.spill);
     they meet at the join 0x8a9d0 in the state `sc_mid`;
   - the body (0x8a9d0 .. 0x8aa40): the two inline checks and stores c->fn := REC_CALL, c->nargs := 0, arg_i(c, id),
     arg_line(c, line), the epilogue and `j answer`; it ends at answer's entry in the state `sc_tail`;
   - the tail: answer's contract at that state, which gives sup_call's post (`SC_T_stmt`).
   The post is the statement's with the freshness conjunct in the statements' settled form (sup_call_c.v:105's
   `~ In (q, n) (ablocks B ly S)` fails on the spill arm: a freed spill argument's (address, size) may be the one
   the new answer gets).

   Pass-4/5 re-fit: sc_pre carries the statement's rounding-mode-0 premise where it had
   astack_pres (statement pass 5 removed that premise, pass 4 added this one), and sc_post is apost_baseF (pass 4).
   Both take the FP state fx: the body applies the tail's statement SC_T_stmt at the FP state fx1 that arg_i
   returns, with sc_pre at fx1 (the same entry facts, rounding mode 0 at fx1 by PaFx.v's fxrel_frm0). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/sup_call_s3.v, with its module paths, module names and numbers changed; 91 of its 154 lines of code are new or changed and 106 lines of the source are left out. *)
(* sup_call's walk on the ASan+UBSan build of plugin-hostd/fuzz_command (fuzz_command.asan-ubsan, entry 0x8af34,
   125 instructions), part 3: the statement's pre and post, the states where the parts of the walk meet, and the
   statement of each part (the B twin of the A walk, an earlier version of lib/A/Prog/sup_call_s3.v, with
   the side-stack frame of A's sup_resp walk).

   The parts (each a lemma of its own file; the composition is sup_call.v):
   - a (sup_call_a.v), 0x8af34 .. 0x8b030: the 96-byte frame and its realignment, the use-after-return flag (1), the
     class-0 side-stack frame F of frame_alloc_0 (0x8af9c), its header and its 8 shadow bytes; it ends in `sc_at_a`;
   - b (sup_call_b.v), 0x8b030 .. 0x8b058: record(REC_CALL) (0x8b034), b's shadow 00 (0x8b03c), the snprintf wrapper on
     (F + 32, 16, "%d", id) (0x8b058); it ends at the wrapper's return 0x8b05c, at the FP state the wrapper returns,
     in `sc_at_b`;
   - l (sup_call_l.v), 0x8b05c .. 0x8b088: arg_s(c, F + 32) (0x8b064), b's shadow f8 (0x8b068), arg_line(c, line)
     (0x8b078) and answer's arguments; it ends at answer's entry (the `jal` at 0x8b08c taken) in `sc_at_l`;
   - t (sup_call_t.v): answer(c, "resp 0", 1), then 0x8b090 .. 0x8b124: the frame's magic, its shadow f5, the flag
     byte, the epilogue and `ret`; it gives the statement's post.
   Each state names the entry (ly S W regs mem md) and the state at that point (lyc Sc Wc regsc memc mdc); the frame
   (0, fpos) at F with flag address FL is the walk's own (the journal's own list). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdObj CmdRo PaSB PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import record_c arg_s_c arg_line_c answer_c sup_call_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* the footprint of sup_call, as its statement names it (sup_call_c.v:129-130) *)
Definition SC_FP (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC + OFF_NCALLS, A_G_REC + OFF_NCALLS + 4) :: (A_G_REC + OFF_CALLS, A_G_REC + OFF_ANSWER + 8) ::
(A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.

(* the realigned stack pointer: `addi sp,sp,-96` then `andi sp,sp,-32` (0x8af34, 0x8af6c) *)
Definition sc_sp1 (sp0 : Z) : Z := 32 * ((sp0 - 96) / 32).
(* the registers the prologue saves, in the order of their slots below the entry sp: ra at sp0 - 8, s0 at sp0 - 16,
   s1 at sp0 - 24, s2 .. s9 at sp0 - 32 .. sp0 - 88 (0x8af3c .. 0x8af64) *)
Definition sc_saved : list Z := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25].
(* the entry's offsets of the walk's states, from the disassembly of sup_call: 0x8b030, 0x8b05c, 0x8b090 *)
Definition SC_PC_A : Z := 0xfc.
Definition SC_PC_B : Z := 0x128.
Definition SC_PC_R : Z := 0x15c.
(* the arguments sup_call records (sup_call_m, RecModel.v:115-116) *)
Definition sc_args (id : Z) (line : list byte) : list (list byte) := [dec id; canon line].

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the saved registers at their slots below the entry sp (cgif's cl_frame) *)
Definition sc_frame (rd : reader) (sp0 : Z) (regs0 : bvmap 5 word) : Prop :=
forall j r, nth_error sc_saved j = Some r ->
aval_mem rd (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs0 (Z_to_bv 5 r))).

(* the registers the walk keeps from 0x8b030 on (regs0: the entry's): sp = sp1, s0 = sp0 (0x8af68), s2 = s8 = F
   (0x8afa0, 0x8afac), s3 = line (0x8af74), s4 = id (0x8af90), s5 = F + 32 = b (0x8afd4), s7 = F's shadow
   (F >> 3) + SB (0x8afe8), s9 = -8 (0x8b008, the f8 byte); gp, tp, s10, s11 are the entry's *)
Definition sc_regs (regs0 regsc : bvmap 5 word) (F : Z) : Prop :=
spZ regsc = sc_sp1 (spZ regs0) /\
getr regsc 8 = getr regs0 2 /\
getr regsc 18 = w64 F /\ getr regsc 24 = w64 F /\
getr regsc 19 = getr regs0 11 /\ getr regsc 20 = getr regs0 10 /\
getr regsc 21 = w64 (F + 32) /\ getr regsc 23 = w64 (SB + F / 8) /\ getr regsc 25 = w64 (-8) /\
getr regsc 3 = getr regs0 3 /\ getr regsc 4 = getr regs0 4 /\
getr regsc 26 = getr regs0 26 /\ getr regsc 27 = getr regs0 27.

(* the line lies in a live block that is none of the recorder's (the statement's in_blockA and its iv_apart
   conjunct against O, sup_call_c.v:119-120), in the form the walk's calls use *)
Definition sc_line_blk (B : asyms) ly S (O : list (Z * Z)) (pl : Z) (line : list byte) : Prop :=
exists p k, In (p, k) (ablocks B ly S) /\ ~ In (p, k) O /\ p <= pl /\ pl + Z.of_nat (length line) + 1 <= p + k.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.

(* the premises of the statement after afn_pre's rounding-mode clause, premise for premise (sup_call_c.v:97-124);
   the rounding mode is a separate premise of each part (frm0 fx, at that part's FP state) *)
Definition sc_pre ly S (W : world SEGS) (regs : bvmap 5 word) mem md ch (id pl : Z) (line : list byte)
(R : rstate) (O : list (Z * Z)) (t : list byte) : Prop :=
afn_pre SEGS B SUP_CALL_STK ly S W regs mem md ch /\
Z.of_nat (length (frames S)) <= 7 /\
arodata_okP SEGS RLO RHI B (rdW W mem) /\
cmd_ro_ok (rdW W mem) /\
getr regs 10 = w64 id /\ -2 ^ 31 <= id < 2 ^ 31 /\
getr regs 11 = w64 pl /\ 0 <= pl < 2 ^ 64 /\
(in_blockA (ablocks B ly S) pl (Z.of_nat (length line) + 1) /\
 Forall (fun qk => iv_apart pl (Z.of_nat (length line) + 1) (fst qk) (snd qk)) O /\
 astr_atR (rdW W mem) pl line /\ Z.of_nat (length line) + 1 <= LMAX + 1) /\
rec_repA B ly S (rdW W mem) R O /\
st_nev S + EV_SUP_CALL R <= EV_MAX /\ blocks_bytes S + LIVE_SUP_CALL id line t <= LIVE_MAX /\
mo_ok MT S (XM_SUP_CALL MT R id line t).

(* the statement's post predicate (sup_call_c.v:132-146) *)
Definition sc_Q ly S (W : world SEGS) (mem : word -> option byte) (id : Z) (line : list byte) (R : rstate) (O : list (Z * Z)) (t : list byte)
: alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' => exists R' O' q,
 sup_call_m R id line = (R', t) /\
 let n := Z.of_nat (length t) + 1 in
 getr regs' 10 = w64 q /\ 4096 <= q < 2 ^ 64 /\
 rec_repA B ly' S' (rdW W' mem') R' O' /\
 (forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
 (forall pn, In pn (ablocks B ly' S') -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O' \/ pn = (q, n)) /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly' S')) /\
 In (q, n) (ablocks B ly' S') /\ (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> pn <> (q, n)) /\
 ~ In q (map fst O') /\
 astr_atR (rdW W' mem') q t /\
 blocks_bytes S' <= blocks_bytes S + LIVE_SUP_CALL id line t /\
 mo_le MT S S' (XM_SUP_CALL MT R id line t).

(* the statement's post (sup_call_c.v:125-146), at the ambient FP state *)
Definition sc_post ly S (W : world SEGS) (regs : bvmap 5 word) mem md (id : Z) (line : list byte)
(R : rstate) (O : list (Z * Z)) (t : list byte) : world SEGS -> config -> Prop :=
apost_baseF SEGS B SUP_CALL_STK (SC_FP O) regs ly S W mem md (EV_SUP_CALL R) (sc_Q ly S W mem id line R O t).

(* the walk's frame from 0x8b030 on: the journal from the entry with the frame (0, fpos) its own, F and FL that
   frame's addresses, the registers it keeps, its saved registers, and the frame's flag-byte word at F + 56
   (frame_alloc_0's post, fs_frame_bytes 0 - 8 = 56) *)
Definition sc_live ly S (W : world SEGS) (regs : bvmap 5 word) mem md (O : list (Z * Z)) (fpos F FL : Z)
lyc Sc (Wc : world SEGS) (regsc : bvmap 5 word) memc mdc (k : Z) : Prop :=
ajournal SEGS B SUP_CALL_STK (spZ regs) (SC_FP O) ly S W mem md [(0, fpos)] lyc Sc Wc memc mdc k /\
frame_addr lyc 0 fpos = F /\ flag_addr lyc 0 fpos = FL /\
sc_regs regs regsc F /\
sc_frame (rdW Wc memc) (spZ regs) regs /\
rdword (rdW Wc memc) (F + 56) = Some FL.

(* the recorder's blocks Oc at a point of the walk against the entry's O: every block of Oc is one of O or new
   since the entry, every live block is a kept caller block or one of Oc, and no caller block is lost *)
Definition sc_blk ly S (O : list (Z * Z)) lyc Sc (Oc : list (Z * Z)) : Prop :=
(forall pn, In pn Oc -> In pn O \/ ~ In pn (ablocks B ly S)) /\
(forall pn, In pn (ablocks B lyc Sc) -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn Oc) /\
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc)).

(* the state at 0x8b030 (`li a0,1`): the frame and its 8 shadow bytes are set up, no event is spent, the blocks,
   the recorder and the line are the entry's *)
Definition sc_at_a ly S (W : world SEGS) (regs : bvmap 5 word) mem md (pl : Z) (line : list byte)
(R : rstate) (O : list (Z * Z)) (fpos F FL : Z) lyc Sc (Wc : world SEGS) (regsc : bvmap 5 word) memc mdc : Prop :=
sc_live ly S W regs mem md O fpos F FL lyc Sc Wc regsc memc mdc 0 /\
ablocks B lyc Sc = ablocks B ly S /\ blocks_bytes Sc = blocks_bytes S /\ mo_le MT S Sc 0 /\
rec_repA B lyc Sc (rdW Wc memc) R O /\
astr_atR (rdW Wc memc) pl line.

(* the state at 0x8b05c, the snprintf wrapper's return: record() has recorded (REC_CALL, []) in the slot
   c = rec_slot R (s6, 0x8b038), its spill arm's frees are spent, b holds the printed id with its shadow usable *)
Definition sc_at_b ly S (W : world SEGS) (regs : bvmap 5 word) mem md (id pl : Z) (line : list byte)
(R : rstate) (O : list (Z * Z)) (fpos F FL : Z) lyc Sc (Wc : world SEGS) (regsc : bvmap 5 word) memc mdc : Prop :=
sc_live ly S W regs mem md O fpos F FL lyc Sc Wc regsc memc mdc (EV_RECORD R) /\
getr regsc 22 = w64 (rec_slot R) /\
exists O1, rec_repA B lyc Sc (rdW Wc memc) (rec_record R REC_CALL []) O1 /\
 sc_blk ly S O lyc Sc O1 /\
 blocks_bytes Sc <= blocks_bytes S /\ mo_le MT S Sc (XM_RECORD MT R) /\
 astr_atR (rdW Wc memc) pl line /\
 astr_atR (rdW Wc memc) (F + 32) (dec id) /\
 rdW Wc memc (SB + F / 8 + 4) = Some 0 /\ rdW Wc memc (SB + F / 8 + 5) = Some 0.

(* the state at answer's entry (the `jal answer` at 0x8b08c taken): ra = 0x8b090, a0 = c, a1 = the shape "resp 0"
   (0x21d20), a2 = 1; the recorder holds (REC_CALL, [dec id; canon line]) in the slot *)
Definition sc_at_l ly S (W : world SEGS) (regs : bvmap 5 word) mem md (id : Z) (line : list byte)
(R : rstate) (O : list (Z * Z)) (fpos F FL : Z) lyc Sc (Wc : world SEGS) (regsc : bvmap 5 word) memc mdc : Prop :=
sc_live ly S W regs mem md O fpos F FL lyc Sc Wc regsc memc mdc (EV_RECORD R + EV_ARG_S + EV_ARG_LINE) /\
getr regsc 22 = w64 (rec_slot R) /\
getr regsc 1 = w64 (BASE + AF_sup_call + SC_PC_R) /\
getr regsc 10 = w64 (rec_slot R) /\ getr regsc 11 = w64 0x21d20 /\ getr regsc 12 = w64 1 /\
exists O2, rec_repA B lyc Sc (rdW Wc memc) (rec_record R REC_CALL (sc_args id line)) O2 /\
 sc_blk ly S O lyc Sc O2 /\
 blocks_bytes Sc <= blocks_bytes S + LIVE_ARG_S (Some (dec id)) + LIVE_ARG_LINE line /\
 mo_le MT S Sc (XM_RECORD MT R + XM_ARG_S MT (Some (dec id)) + XM_ARG_LINE MT line).

(* the whole walk, from the entry *)
Definition SC_main_stmt : Prop :=
forall ly S W regs mem md ch id pl line R O,
let t := snd (sup_call_m R id line) in
frm0 fx ->
sc_pre ly S W regs mem md ch id pl line R O t ->
SRr SEGS W (cfg_at SEGS (BASE + AF_sup_call) regs mem md) (sc_post ly S W regs mem md id line R O t).

(* the walk from 0x8b030 (part b, then l and t) *)
Definition SC_A_stmt : Prop :=
forall ly S W regs mem md ch id pl line R O fpos F FL lyc Sc Wc regsc memc mdc,
let t := snd (sup_call_m R id line) in
frm0 fx ->
sc_pre ly S W regs mem md ch id pl line R O t ->
sc_at_a ly S W regs mem md pl line R O fpos F FL lyc Sc Wc regsc memc mdc ->
SRr SEGS Wc (mkCfg (mkst regsc (Z_to_bv 64 (BASE + AF_sup_call + SC_PC_A)) memc (seg_rom SEGS)) mdc)
(sc_post ly S W regs mem md id line R O t).

(* the walk from 0x8b05c (part l, then t); the ambient FP state is the one the snprintf wrapper returned *)
Definition SC_B_stmt : Prop :=
forall ly S W regs mem md ch id pl line R O fpos F FL lyc Sc Wc regsc memc mdc,
let t := snd (sup_call_m R id line) in
frm0 fx ->
sc_pre ly S W regs mem md ch id pl line R O t ->
sc_at_b ly S W regs mem md id pl line R O fpos F FL lyc Sc Wc regsc memc mdc ->
SRr SEGS Wc (mkCfg (mkst regsc (Z_to_bv 64 (BASE + AF_sup_call + SC_PC_B)) memc (seg_rom SEGS)) mdc)
(sc_post ly S W regs mem md id line R O t).

(* the walk from answer's entry (part t) *)
Definition SC_L_stmt : Prop :=
forall ly S W regs mem md ch id pl line R O fpos F FL lyc Sc Wc regsc memc mdc,
let t := snd (sup_call_m R id line) in
frm0 fx ->
sc_pre ly S W regs mem md ch id pl line R O t ->
sc_at_l ly S W regs mem md id line R O fpos F FL lyc Sc Wc regsc memc mdc ->
SRr SEGS Wc (mkCfg (mkst regsc (Z_to_bv 64 (BASE + AF_answer)) memc (seg_rom SEGS)) mdc)
(sc_post ly S W regs mem md id line R O t).
End e.
End f.
End w.
