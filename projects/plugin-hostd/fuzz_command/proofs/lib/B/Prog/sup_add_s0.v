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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply.v, with its module paths and module names changed; 293 of its 317 lines of code are new or changed and 128 lines of the source are left out. *)
(* The walk of sup_add on the ASan+UBSan build of plugin-hostd/fuzz_command: the shared vocabulary of its stages.

   The walk proves `tsup_add_spec` (lib/B/Prog/sup_add_c.v) in the form of the A walk (lib/A/Prog/sup_add_s0.v on
   a working branch 87f17ee4716): stage lemmas from one program point to the next, each from a machine-level
   mid-state predicate at a label to the call's post-condition, and one assembly lemma (lib/B/Prog/sup_add.v). This
   file holds only definitions: the entry bundle, the post-condition the walk proves, the mid-state predicates and
   the stage statements.

   B calls record() and arg_s() where A inlined them (lib/B/Prog/record_c.v, arg_s_c.v state the recorder at
   recorder level: rec_record R REC_ADD A in the slot rec_slot R), and inlines arg_i: snprintf(b, 16, "%d", id) into
   b[16] at F + 32 of this call's class-1 side-stack frame F, then arg_s(c, b).

   The FP state. Every definition below lives in a section with an ambient FP state fx; a stage statement is the
   machine run from its label AT THE AMBIENT fx to apost_baseF AT THE SAME fx, with rounding mode 0 at fx as a
   premise. The snprintf wrapper (0x8a570, 0x8a628) and answer (0x8a5fc) return at some fx1 related to fx
   (PaFx.v's fxrel): a stage that ends at such a call's return proves the rest with the next stage statement taken
   at fx1 (its premise is `forall fx1, @SA_<next>_stmt fx1 ...`) and lifts the post (PaFx.v srr_after_callF /
   srr_after_artF); rounding mode 0 at fx1 comes from the wrapper's post or fxrel_frm0.

   Program points (BASE + AF_sup_add = 0x8a400; the listing lib/B/Prog/CmdList.v and the pinned image; every label
   after the first is a call's return address or the shared snprintf call):
     entry 0x8a400
     M1  0x8a538  after record(REC_ADD = 0) (`jal` 0x8a534): a0 = c = rec_slot R, the recorder rec_record R 0 []
     M2  0x8a554  after arg_s(c, uri) (`jal` 0x8a550): buf's shadow 0, s8 = c, args [sarg uri]
     M3  0x8a574  after snprintf(b, 16, "%d", id) (`jal` 0x8a570): b's shadow 0, b holds dec id   [FP state changes]
     M4  0x8a580  after arg_s(c, b) (`jal` 0x8a57c): args [sarg uri; dec id]
     M5  0x8a5a4  after arg_s(c, placement or "-") (`jal` 0x8a5a0): s6 = "-" (0x21d80)
     M6  0x8a5bc  after arg_s(c, client or "-") (`jal` 0x8a5b8): s4 = buf = F + 64, the four arguments recorded
     M7  0x8a628  the snprintf call: a0 = buf = F + 64, a1 = 32, a2 = "resp %d" (0x21d40), a3 = v
                  (from the out-of-range arm `j` 0x8a5dc, or the accepted arm after mix_call 0x8a60c)
     M8  0x8a62c  after snprintf(buf, 32, "resp %d", v): buf holds resp v                       [FP state changes]
     M9  0x8a634  after hand_back(buf) (`jal` 0x8a630) or answer(c, NULL, 0) (`jal` 0x8a5fc)   [answer: FP changes]
   then the epilogue: buf re-poisoned (f8), the magic 0x45e0360e at F, f5 over the 16 shadow bytes, the flag byte
   through F + 120, the restores, `ret`. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith List Bool Lia Permutation.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
record_c arg_s_c mix_call_c hand_back_c answer_c sup_add_c.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Open Scope Z_scope.

(* the program points, as offsets from the listing's base (CmdList.v: AF_sup_add = 0x3ed0) *)
Definition L_M1 : Z := AF_sup_add + 0x138.   (* 0x8a538 *)
Definition L_M2 : Z := AF_sup_add + 0x154.   (* 0x8a554 *)
Definition L_M3 : Z := AF_sup_add + 0x174.   (* 0x8a574 *)
Definition L_M4 : Z := AF_sup_add + 0x180.   (* 0x8a580 *)
Definition L_M5 : Z := AF_sup_add + 0x1a4.   (* 0x8a5a4 *)
Definition L_M6 : Z := AF_sup_add + 0x1bc.   (* 0x8a5bc *)
Definition L_M7 : Z := AF_sup_add + 0x228.   (* 0x8a628 *)
Definition L_M8 : Z := AF_sup_add + 0x22c.   (* 0x8a62c *)
Definition L_M9 : Z := AF_sup_add + 0x234.   (* 0x8a634 *)

(* the read-only literals the walk passes: "-" (0x8a584), "%d" (0x8a560), "resp %d" (0x8a5d0, 0x8a618) *)
Definition SA_DASH : Z := 0x21d80.
Definition SA_FMT_D : Z := 0x21f40.
Definition SA_FMT_RESP : Z := 0x21d40.

(* the realigned frame base: `andi sp,sp,-32` (0x8a440) on sp0 - 128; s1 holds it from 0x8a444 *)
Definition sa_s1 (sp0 : Z) : Z := sp0 - 128 - (sp0 - 128) mod 32.
(* the callee-saved registers in the order of their slots sp0 - 8 - 8 j (0x8a408..0x8a438): ra s0 s1 s2 .. s11 *)
Definition sa_saved : list Z := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition sa_frame (rd : reader) (sp0 : Z) (regs : bvmap 5 word) : Prop :=
forall j r, nth_error sa_saved j = Some r ->
aval_mem rd (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))).
(* the four arguments record()'s slot receives (RecModel.v sup_add_m) *)
Definition sa_A (uri : option (list byte)) (id : Z) (placement client : option (list byte)) : list (list byte) :=
[sarg uri; dec id; darg placement (bstr "-"%string); darg client (bstr "-"%string)].
(* the footprint of the statement (sup_add_c.v:151-152) *)
Definition sa_FP (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC + OFF_NCALLS, A_G_REC + OFF_NCALLS + 4) :: (A_G_REC + OFF_CALLS, A_G_REC + OFF_ANSWER + 8) ::
(A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.
(* the event budget spent up to M1, M2 (= M3), M4, M5 and M6 (= M7 = M8); EV_SUP_ADD R is sa_ev6 R plus
   Z.max EV_ANSWER EV_HAND_BACK, by conversion *)
Definition sa_ev1 (R : rstate) : Z := EV_RECORD R.
Definition sa_ev2 (R : rstate) : Z := sa_ev1 R + EV_ARG_S.
Definition sa_ev4 (R : rstate) : Z := sa_ev2 R + EV_ARG_S.
Definition sa_ev5 (R : rstate) : Z := sa_ev4 R + EV_ARG_S.
Definition sa_ev6 (R : rstate) : Z := sa_ev5 R + EV_ARG_S.
(* the live bytes added up to M2, M4, M5 and M6; LIVE_SUP_ADD is sa_live6 plus the Z.max, by conversion *)
Definition sa_live2 (uri : option (list byte)) : Z := LIVE_ARG_S uri.
Definition sa_live4 (uri : option (list byte)) (id : Z) : Z := sa_live2 uri + LIVE_ARG_S (Some (dec id)).
Definition sa_live5 (uri : option (list byte)) (id : Z) (placement : option (list byte)) : Z :=
sa_live4 uri id + LIVE_ARG_S (Some (darg placement (bstr "-"%string))).
Definition sa_live6 (uri : option (list byte)) (id : Z) (placement client : option (list byte)) : Z :=
sa_live5 uri id placement + LIVE_ARG_S (Some (darg client (bstr "-"%string))).
(* the meter spent up to M1, M2, M4, M5 and M6; XM_SUP_ADD is sa_acc6 plus the Z.max, by conversion *)
Definition sa_acc1 (MT : ameter_ops) (R : rstate) : Z := XM_RECORD MT R.
Definition sa_acc2 (MT : ameter_ops) (R : rstate) (uri : option (list byte)) : Z := sa_acc1 MT R + XM_ARG_S MT uri.
Definition sa_acc4 (MT : ameter_ops) (R : rstate) (uri : option (list byte)) (id : Z) : Z :=
sa_acc2 MT R uri + XM_ARG_S MT (Some (dec id)).
Definition sa_acc5 (MT : ameter_ops) (R : rstate) (uri : option (list byte)) (id : Z) (placement : option (list byte)) : Z :=
sa_acc4 MT R uri id + XM_ARG_S MT (Some (darg placement (bstr "-"%string))).
Definition sa_acc6 (MT : ameter_ops) (R : rstate) (uri : option (list byte)) (id : Z)
(placement client : option (list byte)) : Z :=
sa_acc5 MT R uri id placement + XM_ARG_S MT (Some (darg client (bstr "-"%string))).

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

(* the uri (sup_add_c.v:134-136): a string in a live block that is none of the recorder's, never NULL; the walk
   keeps uri as an option so that its mid-states read sarg uri, and this conjunct says it is Some *)
Definition sa_uri ly S (rd : reader) (O : list (Z * Z)) (pu : Z) (uri : option (list byte)) : Prop :=
match uri with
| None => False
| Some u =>
  in_blockA (ablocks B ly S) pu (Z.of_nat (length u) + 1) /\
  Forall (fun qk => iv_apart pu (Z.of_nat (length u) + 1) (fst qk) (snd qk)) O /\
  astr_atR rd pu u /\ Z.of_nat (length u) + 1 <= LMAX + 1
end.

(* the entry: the statement's premises (sup_add_c.v:114-146, statement pass 5), in its order, without the
   rounding-mode premise (fcsr of the ambient FP state; each stage statement takes it at its own FP state) *)
Definition sa_cx ly S W (regs : bvmap 5 word) mem md ch (pu id pp pc : Z) (uri placement client : option (list byte))
(R : rstate) (O : list (Z * Z)) : Prop :=
let t := snd (sup_add_m R uri id placement client) in
afn_pre SEGS B SUP_ADD_STK ly S W regs mem md ch /\
Z.of_nat (length (frames S)) <= 7 /\
arodata_okP SEGS RLO RHI B (rdW W mem) /\
cmd_ro_ok (rdW W mem) /\
getr regs 10 = w64 pu /\ 0 <= pu < 2 ^ 64 /\ getr regs 11 = w64 id /\ -2 ^ 31 <= id < 2 ^ 31 /\
getr regs 12 = w64 pp /\ 0 <= pp < 2 ^ 64 /\ getr regs 13 = w64 pc /\ 0 <= pc < 2 ^ 64 /\
sa_uri ly S (rdW W mem) O pu uri /\
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O pp placement /\
(forall x, placement = Some x -> atail_vis SEGS W mem (pp + Z.of_nat (length x))) /\
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O pc client /\
(forall x, client = Some x -> atail_vis SEGS W mem (pc + Z.of_nat (length x))) /\
rec_repA B ly S (rdW W mem) R O /\
st_nev S + EV_SUP_ADD R <= EV_MAX /\ blocks_bytes S + LIVE_SUP_ADD uri id placement client t <= LIVE_MAX /\
mo_ok MT S (XM_SUP_ADD MT R uri id placement client t).

(* what the call leaves (sup_add_c.v:154-168), word for word *)
Definition sa_postQ ly S (R : rstate) (O : list (Z * Z)) (uri : option (list byte)) (id : Z)
(placement client : option (list byte)) (t : list byte)
: alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' => exists R' O' q,
 sup_add_m R uri id placement client = (R', t) /\
 let n := Z.of_nat (length t) + 1 in
 getr regs' 10 = w64 q /\ 4096 <= q < 2 ^ 64 /\
 rec_repA B ly' S' (rdW W' mem') R' O' /\
 (forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
 (forall pn, In pn (ablocks B ly' S') -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O' \/ pn = (q, n)) /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly' S')) /\
 In (q, n) (ablocks B ly' S') /\ (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> pn <> (q, n)) /\
 ~ In q (map fst O') /\
 astr_atR (rdW W' mem') q t /\
 blocks_bytes S' <= blocks_bytes S + LIVE_SUP_ADD uri id placement client t /\
 mo_le MT S S' (XM_SUP_ADD MT R uri id placement client t).
(* the post-condition at the ambient FP state *)
Definition sa_final ly S W (regs : bvmap 5 word) mem md (R : rstate) (O : list (Z * Z)) (uri : option (list byte))
(id : Z) (placement client : option (list byte)) : world SEGS -> config -> Prop :=
apost_baseF SEGS B SUP_ADD_STK (sa_FP O) regs ly S W mem md (EV_SUP_ADD R)
(sa_postQ ly S R O uri id placement client (snd (sup_add_m R uri id placement client))).

(* the facts every mid-state after the side-stack frame's allocation carries: the journal from the entry (the
   frame (1, pos) is the call's own), the saved registers of the real frame, the frame's flag pointer at F + 120,
   and the registers that hold the same value from the frame's setup (0x8a4e4) to the epilogue:
   sp = s1 = the realigned base, gp, tp, s0 = sp0, s2 = s10 = F, s3 = id, s7 = b = F + 32,
   s9 = the frame's shadow SHADOW_OFF + F / 8, s11 = -8 (the f8 poison byte) *)
Definition sa_core ly S W (regs : bvmap 5 word) mem md (O : list (Z * Z))
lyc Sc (Wc : world SEGS) (regs1 : bvmap 5 word) memc mdc (k pos : Z) : Prop :=
let sp0 := spZ regs in let s1 := sa_s1 sp0 in let F := frame_addr lyc 1 pos in
ajournal SEGS B SUP_ADD_STK sp0 (sa_FP O) ly S W mem md [(1, pos)] lyc Sc Wc memc mdc k /\
sa_frame (rdW Wc memc) sp0 regs /\
rdword (rdW Wc memc) (F + fs_frame_bytes 1 - 8) = Some (flag_addr lyc 1 pos) /\
getr regs1 2 = w64 s1 /\ getr regs1 3 = w64 (as_gp B) /\ getr regs1 4 = w64 (as_tp B) /\
getr regs1 8 = w64 sp0 /\ getr regs1 9 = w64 s1 /\ getr regs1 18 = w64 F /\ getr regs1 19 = getr regs 11 /\
getr regs1 23 = w64 (F + 32) /\ getr regs1 25 = w64 (SHADOW_OFF + F / 8) /\ getr regs1 26 = w64 F /\
getr regs1 27 = w64 (-8).

(* the block accounting against the entry, with Oc the recorder's blocks now and live the bytes added so far *)
Definition sa_acct ly S (O : list (Z * Z)) lyc Sc (Oc : list (Z * Z)) (live : Z) : Prop :=
(forall pn, In pn Oc -> In pn O \/ ~ In pn (ablocks B ly S)) /\
(forall pn, In pn (ablocks B lyc Sc) -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn Oc) /\
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc)) /\
(forall pn, In pn Oc -> In pn (ablocks B lyc Sc)) /\
blocks_bytes Sc <= blocks_bytes S + live.

(* buf[32] at F + 64 is unpoisoned (0x8a53c-0x8a548): its four shadow bytes 8..11 are 0 *)
Definition sa_buf0 (rd : reader) (F : Z) : Prop := forall i, 0 <= i < 4 -> rd (SHADOW_OFF + F / 8 + 8 + i) = Some 0.
(* b[16] at F + 32 is unpoisoned (0x8a554-0x8a558): its two shadow bytes 4..5 are 0 *)
Definition sa_b0 (rd : reader) (F : Z) : Prop := forall i, 0 <= i < 2 -> rd (SHADOW_OFF + F / 8 + 4 + i) = Some 0.

(* M1 (0x8a538): record() returned the slot c in a0; s4, s5, s6 still hold client, placement, uri *)
Definition sa_M1m ly S W (regs : bvmap 5 word) mem md (R : rstate) (O : list (Z * Z))
lyc Sc (Wc : world SEGS) (regs1 : bvmap 5 word) memc mdc (pos : Z) : Prop :=
sa_core ly S W regs mem md O lyc Sc Wc regs1 memc mdc (sa_ev1 R) pos /\
getr regs1 10 = w64 (rec_slot R) /\
getr regs1 20 = getr regs 13 /\ getr regs1 21 = getr regs 12 /\ getr regs1 22 = getr regs 10 /\
exists O1, rec_repA B lyc Sc (rdW Wc memc) (rec_record R REC_ADD []) O1 /\
sa_acct ly S O lyc Sc O1 0 /\
mo_le MT S Sc (sa_acc1 MT R).

(* M2 (0x8a554): s8 = c; the call holds [sarg uri]; buf's shadow is 0 *)
Definition sa_M2m ly S W (regs : bvmap 5 word) mem md (R : rstate) (O : list (Z * Z)) (uri : option (list byte))
lyc Sc (Wc : world SEGS) (regs1 : bvmap 5 word) memc mdc (pos : Z) : Prop :=
let F := frame_addr lyc 1 pos in
sa_core ly S W regs mem md O lyc Sc Wc regs1 memc mdc (sa_ev2 R) pos /\
getr regs1 20 = getr regs 13 /\ getr regs1 21 = getr regs 12 /\ getr regs1 24 = w64 (rec_slot R) /\
sa_buf0 (rdW Wc memc) F /\
exists O2, rec_repA B lyc Sc (rdW Wc memc) (rec_record R REC_ADD [sarg uri]) O2 /\
sa_acct ly S O lyc Sc O2 (sa_live2 uri) /\
mo_le MT S Sc (sa_acc2 MT R uri).

(* M3 (0x8a574): b's shadow is 0 and b holds the decimal text of id (the snprintf wrapper's "%d") *)
Definition sa_M3m ly S W (regs : bvmap 5 word) mem md (R : rstate) (O : list (Z * Z)) (uri : option (list byte))
(id : Z) lyc Sc (Wc : world SEGS) (regs1 : bvmap 5 word) memc mdc (pos : Z) : Prop :=
let F := frame_addr lyc 1 pos in
sa_core ly S W regs mem md O lyc Sc Wc regs1 memc mdc (sa_ev2 R) pos /\
getr regs1 20 = getr regs 13 /\ getr regs1 21 = getr regs 12 /\ getr regs1 24 = w64 (rec_slot R) /\
sa_buf0 (rdW Wc memc) F /\ sa_b0 (rdW Wc memc) F /\ astr_atR (rdW Wc memc) (F + 32) (dec id) /\
exists O2, rec_repA B lyc Sc (rdW Wc memc) (rec_record R REC_ADD [sarg uri]) O2 /\
sa_acct ly S O lyc Sc O2 (sa_live2 uri) /\
mo_le MT S Sc (sa_acc2 MT R uri).

(* M4 (0x8a580): the call holds [sarg uri; dec id] *)
Definition sa_M4m ly S W (regs : bvmap 5 word) mem md (R : rstate) (O : list (Z * Z)) (uri : option (list byte))
(id : Z) lyc Sc (Wc : world SEGS) (regs1 : bvmap 5 word) memc mdc (pos : Z) : Prop :=
let F := frame_addr lyc 1 pos in
sa_core ly S W regs mem md O lyc Sc Wc regs1 memc mdc (sa_ev4 R) pos /\
getr regs1 20 = getr regs 13 /\ getr regs1 21 = getr regs 12 /\ getr regs1 24 = w64 (rec_slot R) /\
sa_buf0 (rdW Wc memc) F /\
exists O4, rec_repA B lyc Sc (rdW Wc memc) (rec_record R REC_ADD [sarg uri; dec id]) O4 /\
sa_acct ly S O lyc Sc O4 (sa_live4 uri id) /\
mo_le MT S Sc (sa_acc4 MT R uri id).

(* M5 (0x8a5a4): the call holds [sarg uri; dec id; placement or "-"]; s6 = "-", s4 = client *)
Definition sa_M5m ly S W (regs : bvmap 5 word) mem md (R : rstate) (O : list (Z * Z)) (uri : option (list byte))
(id : Z) (placement : option (list byte)) lyc Sc (Wc : world SEGS) (regs1 : bvmap 5 word) memc mdc (pos : Z) : Prop :=
let F := frame_addr lyc 1 pos in
sa_core ly S W regs mem md O lyc Sc Wc regs1 memc mdc (sa_ev5 R) pos /\
getr regs1 20 = getr regs 13 /\ getr regs1 22 = w64 SA_DASH /\ getr regs1 24 = w64 (rec_slot R) /\
sa_buf0 (rdW Wc memc) F /\
exists O5, rec_repA B lyc Sc (rdW Wc memc)
  (rec_record R REC_ADD [sarg uri; dec id; darg placement (bstr "-"%string)]) O5 /\
sa_acct ly S O lyc Sc O5 (sa_live5 uri id placement) /\
mo_le MT S Sc (sa_acc5 MT R uri id placement).

(* M6 (0x8a5bc): the four arguments recorded; s4 = buf = F + 64 *)
Definition sa_M6m ly S W (regs : bvmap 5 word) mem md (R : rstate) (O : list (Z * Z)) (uri : option (list byte))
(id : Z) (placement client : option (list byte)) lyc Sc (Wc : world SEGS) (regs1 : bvmap 5 word) memc mdc (pos : Z)
: Prop :=
let F := frame_addr lyc 1 pos in
sa_core ly S W regs mem md O lyc Sc Wc regs1 memc mdc (sa_ev6 R) pos /\
getr regs1 20 = w64 (F + 64) /\ getr regs1 24 = w64 (rec_slot R) /\
sa_buf0 (rdW Wc memc) F /\
exists O6, rec_repA B lyc Sc (rdW Wc memc) (rec_record R REC_ADD (sa_A uri id placement client)) O6 /\
sa_acct ly S O lyc Sc O6 (sa_live6 uri id placement client) /\
mo_le MT S Sc (sa_acc6 MT R uri id placement client).

(* the text sup_add_m returns on the two arms that reach the shared snprintf: v = -1 out of range (the recorder
   R1), v = id accepted (R1 with its state mixed) *)
Definition sa_arm (R : rstate) (uri : option (list byte)) (id : Z) (placement client : option (list byte))
(v : Z) (R2 : rstate) : Prop :=
let A := sa_A uri id placement client in let R1 := rec_record R REC_ADD A in
(v = -1 /\ ((id <? 0) || (10000 <=? id))%bool = true /\ R2 = R1) \/
(v = id /\ 0 <= id < 10000 /\ r_refuse R1 = 0 /\ R2 = rec_mix R1 (REC_ADD, A)).

(* M7 (0x8a628): at the snprintf call on either arm *)
Definition sa_M7m ly S W (regs : bvmap 5 word) mem md (R : rstate) (O : list (Z * Z)) (uri : option (list byte))
(id : Z) (placement client : option (list byte)) lyc Sc (Wc : world SEGS) (regs1 : bvmap 5 word) memc mdc (pos : Z)
: Prop :=
let F := frame_addr lyc 1 pos in
sa_core ly S W regs mem md O lyc Sc Wc regs1 memc mdc (sa_ev6 R) pos /\
getr regs1 10 = w64 (F + 64) /\ getr regs1 11 = w64 32 /\ getr regs1 12 = w64 SA_FMT_RESP /\
getr regs1 20 = w64 (F + 64) /\
sa_buf0 (rdW Wc memc) F /\
exists v R2 O6, sa_arm R uri id placement client v R2 /\ getr regs1 13 = w64 v /\
rec_repA B lyc Sc (rdW Wc memc) R2 O6 /\
sa_acct ly S O lyc Sc O6 (sa_live6 uri id placement client) /\
mo_le MT S Sc (sa_acc6 MT R uri id placement client).

(* M8 (0x8a62c): buf holds resp v *)
Definition sa_M8m ly S W (regs : bvmap 5 word) mem md (R : rstate) (O : list (Z * Z)) (uri : option (list byte))
(id : Z) (placement client : option (list byte)) lyc Sc (Wc : world SEGS) (regs1 : bvmap 5 word) memc mdc (pos : Z)
: Prop :=
let F := frame_addr lyc 1 pos in
sa_core ly S W regs mem md O lyc Sc Wc regs1 memc mdc (sa_ev6 R) pos /\
getr regs1 20 = w64 (F + 64) /\
sa_buf0 (rdW Wc memc) F /\
exists v R2 O6, sa_arm R uri id placement client v R2 /\
astr_atR (rdW Wc memc) (F + 64) (resp v) /\
rec_repA B lyc Sc (rdW Wc memc) R2 O6 /\
sa_acct ly S O lyc Sc O6 (sa_live6 uri id placement client) /\
mo_le MT S Sc (sa_acc6 MT R uri id placement client).

(* M9 (0x8a634): after hand_back / answer: what sa_postQ asks, at the state before the epilogue *)
Definition sa_M9m ly S W (regs : bvmap 5 word) mem md (R : rstate) (O : list (Z * Z)) (uri : option (list byte))
(id : Z) (placement client : option (list byte)) lyc Sc (Wc : world SEGS) (regs1 : bvmap 5 word) memc mdc (pos : Z)
: Prop :=
let t := snd (sup_add_m R uri id placement client) in
sa_core ly S W regs mem md O lyc Sc Wc regs1 memc mdc (EV_SUP_ADD R) pos /\
sa_postQ ly S R O uri id placement client t lyc Sc Wc regs1 memc mdc.

(* the stage statements: from a mid-state at its label, at the ambient FP state fx with rounding mode 0, the call's
   post-condition at fx *)
Definition SA_ENTRY_at : Prop :=
forall ly S W regs mem md ch pu id pp pc uri placement client R O,
sa_cx ly S W regs mem md ch pu id pp pc uri placement client R O ->
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
SRr SEGS W (cfg_at SEGS (BASE + AF_sup_add) regs mem md) (sa_final ly S W regs mem md R O uri id placement client).
Definition SA_M1_at : Prop :=
forall ly S W regs mem md ch pu id pp pc uri placement client R O lyc Sc Wc regs1 memc mdc pos,
sa_cx ly S W regs mem md ch pu id pp pc uri placement client R O ->
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
sa_M1m ly S W regs mem md R O lyc Sc Wc regs1 memc mdc pos ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + L_M1)) memc (seg_rom SEGS)) mdc)
(sa_final ly S W regs mem md R O uri id placement client).
Definition SA_M2_at : Prop :=
forall ly S W regs mem md ch pu id pp pc uri placement client R O lyc Sc Wc regs1 memc mdc pos,
sa_cx ly S W regs mem md ch pu id pp pc uri placement client R O ->
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
sa_M2m ly S W regs mem md R O uri lyc Sc Wc regs1 memc mdc pos ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + L_M2)) memc (seg_rom SEGS)) mdc)
(sa_final ly S W regs mem md R O uri id placement client).
Definition SA_M3_at : Prop :=
forall ly S W regs mem md ch pu id pp pc uri placement client R O lyc Sc Wc regs1 memc mdc pos,
sa_cx ly S W regs mem md ch pu id pp pc uri placement client R O ->
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
sa_M3m ly S W regs mem md R O uri id lyc Sc Wc regs1 memc mdc pos ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + L_M3)) memc (seg_rom SEGS)) mdc)
(sa_final ly S W regs mem md R O uri id placement client).
Definition SA_M4_at : Prop :=
forall ly S W regs mem md ch pu id pp pc uri placement client R O lyc Sc Wc regs1 memc mdc pos,
sa_cx ly S W regs mem md ch pu id pp pc uri placement client R O ->
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
sa_M4m ly S W regs mem md R O uri id lyc Sc Wc regs1 memc mdc pos ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + L_M4)) memc (seg_rom SEGS)) mdc)
(sa_final ly S W regs mem md R O uri id placement client).
Definition SA_M5_at : Prop :=
forall ly S W regs mem md ch pu id pp pc uri placement client R O lyc Sc Wc regs1 memc mdc pos,
sa_cx ly S W regs mem md ch pu id pp pc uri placement client R O ->
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
sa_M5m ly S W regs mem md R O uri id placement lyc Sc Wc regs1 memc mdc pos ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + L_M5)) memc (seg_rom SEGS)) mdc)
(sa_final ly S W regs mem md R O uri id placement client).
Definition SA_M6_at : Prop :=
forall ly S W regs mem md ch pu id pp pc uri placement client R O lyc Sc Wc regs1 memc mdc pos,
sa_cx ly S W regs mem md ch pu id pp pc uri placement client R O ->
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
sa_M6m ly S W regs mem md R O uri id placement client lyc Sc Wc regs1 memc mdc pos ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + L_M6)) memc (seg_rom SEGS)) mdc)
(sa_final ly S W regs mem md R O uri id placement client).
Definition SA_M7_at : Prop :=
forall ly S W regs mem md ch pu id pp pc uri placement client R O lyc Sc Wc regs1 memc mdc pos,
sa_cx ly S W regs mem md ch pu id pp pc uri placement client R O ->
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
sa_M7m ly S W regs mem md R O uri id placement client lyc Sc Wc regs1 memc mdc pos ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + L_M7)) memc (seg_rom SEGS)) mdc)
(sa_final ly S W regs mem md R O uri id placement client).
Definition SA_M8_at : Prop :=
forall ly S W regs mem md ch pu id pp pc uri placement client R O lyc Sc Wc regs1 memc mdc pos,
sa_cx ly S W regs mem md ch pu id pp pc uri placement client R O ->
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
sa_M8m ly S W regs mem md R O uri id placement client lyc Sc Wc regs1 memc mdc pos ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + L_M8)) memc (seg_rom SEGS)) mdc)
(sa_final ly S W regs mem md R O uri id placement client).
Definition SA_M9_at : Prop :=
forall ly S W regs mem md ch pu id pp pc uri placement client R O lyc Sc Wc regs1 memc mdc pos,
sa_cx ly S W regs mem md ch pu id pp pc uri placement client R O ->
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
sa_M9m ly S W regs mem md R O uri id placement client lyc Sc Wc regs1 memc mdc pos ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + L_M9)) memc (seg_rom SEGS)) mdc)
(sa_final ly S W regs mem md R O uri id placement client).
End e.
End f.
End d.

(* the stage statements at every FP state: a stage lemma (proved in a section with an ambient fx) takes the next
   stages' statements in this form, so that it can apply them at the FP state a call returns *)
Definition SA_ENTRY_stmt {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg cmd_listing} (B : asyms) (MT : ameter_ops)
: Prop := forall fx : YK11.FPState, @SA_ENTRY_at fx rc SK PI B MT.
Definition SA_M1_stmt {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg cmd_listing} (B : asyms) (MT : ameter_ops)
: Prop := forall fx : YK11.FPState, @SA_M1_at fx rc SK PI B MT.
Definition SA_M2_stmt {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg cmd_listing} (B : asyms) (MT : ameter_ops)
: Prop := forall fx : YK11.FPState, @SA_M2_at fx rc SK PI B MT.
Definition SA_M3_stmt {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg cmd_listing} (B : asyms) (MT : ameter_ops)
: Prop := forall fx : YK11.FPState, @SA_M3_at fx rc SK PI B MT.
Definition SA_M4_stmt {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg cmd_listing} (B : asyms) (MT : ameter_ops)
: Prop := forall fx : YK11.FPState, @SA_M4_at fx rc SK PI B MT.
Definition SA_M5_stmt {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg cmd_listing} (B : asyms) (MT : ameter_ops)
: Prop := forall fx : YK11.FPState, @SA_M5_at fx rc SK PI B MT.
Definition SA_M6_stmt {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg cmd_listing} (B : asyms) (MT : ameter_ops)
: Prop := forall fx : YK11.FPState, @SA_M6_at fx rc SK PI B MT.
Definition SA_M7_stmt {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg cmd_listing} (B : asyms) (MT : ameter_ops)
: Prop := forall fx : YK11.FPState, @SA_M7_at fx rc SK PI B MT.
Definition SA_M8_stmt {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg cmd_listing} (B : asyms) (MT : ameter_ops)
: Prop := forall fx : YK11.FPState, @SA_M8_at fx rc SK PI B MT.
Definition SA_M9_stmt {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg cmd_listing} (B : asyms) (MT : ameter_ops)
: Prop := forall fx : YK11.FPState, @SA_M9_at fx rc SK PI B MT.
