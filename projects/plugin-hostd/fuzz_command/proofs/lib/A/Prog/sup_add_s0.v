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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply.v, with its module paths and module names changed; 205 of its 230 lines of code are new or changed and 127 lines of the source are left out. *)
(* The walk of sup_add on the ASan build of plugin-hostd/fuzz_command: the shared vocabulary of its stages.

   The walk proves `tsup_add_spec` (lib/A/Prog/sup_add_c.v) in the form of cgif_file_fuzzer's cgif_close walk
   (lib/A/ACh1.v..ACh8.v, AChc.v at c8557374ad2e): stage lemmas from one program point to the next, each from a
   machine-level mid-state predicate at a label to the call's post-condition, and one assembly lemma
   (lib/A/Prog/sup_add.v). This file holds only definitions: the entry bundle, the post-condition the walk proves,
   the mid-state predicates and the stage statements.

   Program points (BASE + AF_sup_add = 0x89dbc; M, the listing lib/A/Prog/CmdList.v and the pinned image):
     entry 0x89dbc
     M0T  0x89f00  table arm of record(): ncalls < 16 (after `bne a0,a1` at 0x89ee4 is taken)
     M0S  0x89ee8  spill arm of record(): ncalls = 16 (`bne` not taken)
     M1   0x89f48  both arms joined, c->fn = 0 and c->nargs = 0 stored (after the store at 0x89f44)
     M2   0x89fc0  args[0] (copy of uri) and args[1] (arg_i's copy of dec id) recorded, nargs = 2
     M3   0x8a050  args[2], args[3] recorded, nargs = 4: the call is recorded
     M3b  0x8a0b8  the snprintf call: a0 = buf = F + 32, a1 = 32, a2 = "resp %d" (0x21d00), a3 = v
     M4   0x8a0c4  after hand_back (or answer, by `jal` at 0x8a08c): a0 = q, the caller's copy of the text
   then the epilogue: buf re-poisoned, magic at F, f5 over the 16 shadow bytes, the flag byte, restores, `ret`. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdObj CmdRo PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c xstrdup_c arg_i_c mix_call_c hand_back_c answer_c sup_add_c.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Open Scope Z_scope.

(* the program points, as offsets from the listing's base (CmdList.v: AF_sup_add = 0x38d8) *)
Definition L_M0S : Z := AF_sup_add + 0x12c.   (* 0x89ee8 *)
Definition L_M0T : Z := AF_sup_add + 0x144.   (* 0x89f00 *)
Definition L_M1 : Z := AF_sup_add + 0x18c.    (* 0x89f48 *)
Definition L_M2 : Z := AF_sup_add + 0x204.    (* 0x89fc0 *)
Definition L_M3 : Z := AF_sup_add + 0x294.    (* 0x8a050 *)
Definition L_M3b : Z := AF_sup_add + 0x2fc.   (* 0x8a0b8 *)
Definition L_M4 : Z := AF_sup_add + 0x308.    (* 0x8a0c4 *)

(* the realigned frame base: `andi sp,sp,-32` (0x89dfc) on sp0 - 160; s1 holds it from 0x89e00 *)
Definition sa_s1 (sp0 : Z) : Z := sp0 - 160 - (sp0 - 160) mod 32.
(* the callee-saved registers in the order of their slots sp0 - 8 - 8 j (0x89dc4..0x89df4): ra s0 s1 s2 .. s11 *)
Definition sa_saved : list Z := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition sa_frame (rd : reader) (sp0 : Z) (regs : bvmap 5 word) : Prop :=
forall j r, nth_error sa_saved j = Some r ->
aval_mem rd (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))).
(* the record slot record() fills: the next table slot, or record.spill when the table holds 16 calls *)
Definition sa_c (R : rstate) : Z :=
if Nat.ltb (length (r_calls R)) 16 then A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R))
else A_REC_SPILL.
(* the four arguments record() appends *)
Definition sa_A (uri : option (list byte)) (id : Z) (placement client : option (list byte)) : list (list byte) :=
[sarg uri; dec id; darg placement (bstr "-"%string); darg client (bstr "-"%string)].
(* the footprint of the statement (sup_add_c.v:126-127) *)
Definition sa_FP (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC + OFF_NCALLS, A_G_REC + OFF_NCALLS + 4) :: (A_G_REC + OFF_CALLS, A_G_REC + OFF_ANSWER + 8) ::
(A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.
(* the event budget spent up to M1, M2 and M3 *)
Definition sa_ev1 (R : rstate) : Z := rec_spill_frees R.
Definition sa_ev2 (R : rstate) : Z := sa_ev1 R + EV_XSTRDUP + EV_ARG_I.
Definition sa_ev3 (R : rstate) : Z := sa_ev2 R + EV_XSTRDUP + EV_XSTRDUP.
(* the live bytes added up to M2 and M3 *)
Definition sa_live2 (uri : option (list byte)) (id : Z) : Z := LIVE_XSTRDUP (sarg uri) + LIVE_ARG_I id.
Definition sa_live3 (uri : option (list byte)) (id : Z) (placement client : option (list byte)) : Z :=
sa_live2 uri id + LIVE_XSTRDUP (darg placement (bstr "-"%string)) + LIVE_XSTRDUP (darg client (bstr "-"%string)).
(* the meter spent up to M1, M2 and M3 *)
Definition sa_acc1 (MT : ameter_ops) (R : rstate) : Z := rec_spill_frees R * mo_free MT.
Definition sa_acc2 (MT : ameter_ops) (R : rstate) (uri : option (list byte)) (id : Z) : Z :=
sa_acc1 MT R + XM_XSTRDUP MT (sarg uri) + XM_ARG_I MT id.
Definition sa_acc3 (MT : ameter_ops) (R : rstate) (uri : option (list byte)) (id : Z) (placement client : option (list byte)) : Z :=
sa_acc2 MT R uri id + XM_XSTRDUP MT (darg placement (bstr "-"%string)) + XM_XSTRDUP MT (darg client (bstr "-"%string)).

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

(* the uri (sup_add_c.v:115-117): a string in a live block that is none of the recorder's, never NULL; the walk
   keeps uri as an option so that its mid-states read sarg uri, and this conjunct says it is Some *)
Definition sa_uri ly S (rd : reader) (O : list (Z * Z)) (pu : Z) (uri : option (list byte)) : Prop :=
match uri with
| None => False
| Some u =>
  in_blockA (ablocks B ly S) pu (Z.of_nat (length u) + 1) /\
  Forall (fun qk => iv_apart pu (Z.of_nat (length u) + 1) (fst qk) (snd qk)) O /\
  astr_atR rd pu u /\ Z.of_nat (length u) + 1 <= LMAX + 1
end.

(* the entry: the statement's premises (sup_add_c.v:101-130), in its order, less its rounding-mode premise: the stages
   that call printf-reaching code take that as `frm0 fx` (PaFx.v), as it changes at those calls *)
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

(* what the call leaves (sup_add_c.v:138-152), word for word *)
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
Definition sa_final ly S W (regs : bvmap 5 word) mem md (R : rstate) (O : list (Z * Z)) (uri : option (list byte))
(id : Z) (placement client : option (list byte)) : world SEGS -> config -> Prop :=
apost_baseF SEGS B SUP_ADD_STK (sa_FP O) regs ly S W mem md (EV_SUP_ADD R)
(sa_postQ ly S R O uri id placement client (snd (sup_add_m R uri id placement client))).

(* the facts every mid-state after the side-stack frame's allocation carries: the journal from the entry (the
   frame (1, pos) is the call's own), the saved registers and the three spills of the real frame, the frame's flag
   pointer, and the registers that hold the same value from 0x89e68 to the epilogue *)
Definition sa_core ly S W (regs : bvmap 5 word) mem md (O : list (Z * Z))
lyc Sc (Wc : world SEGS) (regs1 : bvmap 5 word) memc mdc (k pos : Z) : Prop :=
let sp0 := spZ regs in let s1 := sa_s1 sp0 in let F := frame_addr lyc 1 pos in
ajournal SEGS B SUP_ADD_STK sp0 (sa_FP O) ly S W mem md [(1, pos)] lyc Sc Wc memc mdc k /\
sa_frame (rdW Wc memc) sp0 regs /\
aval_mem (rdW Wc memc) (s1 + 16) 8 (bv_unsigned (getr regs 13)) /\
aval_mem (rdW Wc memc) (s1 + 24) 8 (bv_unsigned (getr regs 12)) /\
aval_mem (rdW Wc memc) (s1 + 48) 8 F /\
rdword (rdW Wc memc) (F + fs_frame_bytes 1 - 8) = Some (flag_addr lyc 1 pos) /\
getr regs1 2 = w64 s1 /\ getr regs1 3 = w64 (as_gp B) /\ getr regs1 4 = w64 (as_tp B) /\
getr regs1 8 = w64 sp0 /\ getr regs1 9 = w64 s1 /\ getr regs1 18 = w64 F /\ getr regs1 19 = getr regs 11 /\
getr regs1 21 = w64 A_G_REC /\ getr regs1 25 = w64 (SHADOW_OFF + F / 8) /\ getr regs1 26 = w64 F.

(* the block accounting against the entry, with Oc the recorder's blocks now and live the bytes added so far *)
Definition sa_acct ly S (R : rstate) (O : list (Z * Z)) lyc Sc (Oc : list (Z * Z)) (live : Z) : Prop :=
(forall pn, In pn Oc -> In pn O \/ ~ In pn (ablocks B ly S)) /\
(forall pn, In pn (ablocks B lyc Sc) -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn Oc) /\
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc)) /\
(forall pn, In pn Oc -> In pn (ablocks B lyc Sc)) /\
blocks_bytes Sc <= blocks_bytes S + live.

(* the buffer buf[32] at F + 32 is unpoisoned (0x89f48-0x89f54): its four shadow bytes are 0 *)
Definition sa_buf0 (rd : reader) (F : Z) : Prop := forall i, 0 <= i < 4 -> rd (SHADOW_OFF + F / 8 + 4 + i) = Some 0.

(* M0T / M0S: at the branch on ncalls; the recorder untouched, n = the table's length *)
Definition sa_M0 ly S W (regs : bvmap 5 word) mem md (R : rstate) (O : list (Z * Z))
lyc Sc (Wc : world SEGS) (regs1 : bvmap 5 word) memc mdc (pos : Z) : Prop :=
let F := frame_addr lyc 1 pos in
sa_core ly S W regs mem md O lyc Sc Wc regs1 memc mdc 0 pos /\
getr regs1 10 = w64 (Z.of_nat (length (r_calls R))) /\ getr regs1 11 = w64 16 /\
getr regs1 20 = w64 SHADOW_OFF /\ getr regs1 24 = getr regs 10 /\
rec_repA B lyc Sc (rdW Wc memc) R O /\
sa_acct ly S R O lyc Sc O 0 /\
mo_le MT S Sc 0.

(* M1: the slot c holds fn = 0 and nargs = 0; the recorder is rec_record R REC_ADD [] *)
Definition sa_M1m ly S W (regs : bvmap 5 word) mem md (R : rstate) (O : list (Z * Z))
lyc Sc (Wc : world SEGS) (regs1 : bvmap 5 word) memc mdc (pos : Z) : Prop :=
let c := sa_c R in
sa_core ly S W regs mem md O lyc Sc Wc regs1 memc mdc (sa_ev1 R) pos /\
getr regs1 20 = w64 SHADOW_OFF /\ getr regs1 22 = w64 c /\ getr regs1 23 = w64 (c + 4) /\
getr regs1 24 = getr regs 10 /\ getr regs1 27 = w64 (SHADOW_OFF + (c + 4) / 8) /\
exists O1, rec_repA B lyc Sc (rdW Wc memc) (rec_record R REC_ADD []) O1 /\
sa_acct ly S R O lyc Sc O1 0 /\
mo_le MT S Sc (sa_acc1 MT R).

(* M2: args[0] = a copy of sarg uri, args[1] = a copy of dec id, nargs = 2 *)
Definition sa_M2m ly S W (regs : bvmap 5 word) mem md (R : rstate) (O : list (Z * Z)) (uri : option (list byte)) (id : Z)
lyc Sc (Wc : world SEGS) (regs1 : bvmap 5 word) memc mdc (pos : Z) : Prop :=
let c := sa_c R in let F := frame_addr lyc 1 pos in
sa_core ly S W regs mem md O lyc Sc Wc regs1 memc mdc (sa_ev2 R) pos /\
getr regs1 20 = w64 SHADOW_OFF /\ getr regs1 22 = w64 c /\ getr regs1 23 = w64 (c + 4) /\
getr regs1 24 = w64 (c + 8) /\ getr regs1 27 = w64 (SHADOW_OFF + (c + 4) / 8) /\
sa_buf0 (rdW Wc memc) F /\
exists O2, rec_repA B lyc Sc (rdW Wc memc) (rec_record R REC_ADD [sarg uri; dec id]) O2 /\
sa_acct ly S R O lyc Sc O2 (sa_live2 uri id) /\
mo_le MT S Sc (sa_acc2 MT R uri id).

(* M3: the four arguments recorded *)
Definition sa_M3m ly S W (regs : bvmap 5 word) mem md (R : rstate) (O : list (Z * Z)) (uri : option (list byte)) (id : Z)
(placement client : option (list byte)) lyc Sc (Wc : world SEGS) (regs1 : bvmap 5 word) memc mdc (pos : Z) : Prop :=
let c := sa_c R in let F := frame_addr lyc 1 pos in
sa_core ly S W regs mem md O lyc Sc Wc regs1 memc mdc (sa_ev3 R) pos /\
getr regs1 22 = w64 c /\
sa_buf0 (rdW Wc memc) F /\
exists O3, rec_repA B lyc Sc (rdW Wc memc) (rec_record R REC_ADD (sa_A uri id placement client)) O3 /\
sa_acct ly S R O lyc Sc O3 (sa_live3 uri id placement client) /\
mo_le MT S Sc (sa_acc3 MT R uri id placement client).

(* M3b: at the snprintf call, on the out-of-range arm (v = -1, the recorder R1) or the accepted arm (v = id, the
   recorder R1 with its state mixed); t = resp v is the text sup_add_m returns on both *)
Definition sa_M3bm ly S W (regs : bvmap 5 word) mem md (R : rstate) (O : list (Z * Z)) (uri : option (list byte)) (id : Z)
(placement client : option (list byte)) lyc Sc (Wc : world SEGS) (regs1 : bvmap 5 word) memc mdc (pos : Z) : Prop :=
let A := sa_A uri id placement client in let R1 := rec_record R REC_ADD A in let F := frame_addr lyc 1 pos in
sa_core ly S W regs mem md O lyc Sc Wc regs1 memc mdc (sa_ev3 R) pos /\
getr regs1 10 = w64 (F + 32) /\ getr regs1 11 = w64 32 /\ getr regs1 12 = w64 0x21d00 /\
getr regs1 20 = w64 (F + 32) /\
sa_buf0 (rdW Wc memc) F /\
exists v R2 O3,
((v = -1 /\ ((id <? 0) || (10000 <=? id))%bool = true /\ R2 = R1 /\ getr regs1 13 = w64 (-1)) \/
 (v = id /\ 0 <= id < 10000 /\ r_refuse R1 = 0 /\ R2 = rec_mix R1 (REC_ADD, A) /\ getr regs1 13 = getr regs 11)) /\
rec_repA B lyc Sc (rdW Wc memc) R2 O3 /\
sa_acct ly S R O lyc Sc O3 (sa_live3 uri id placement client) /\
mo_le MT S Sc (sa_acc3 MT R uri id placement client).

(* M4: after hand_back / answer: what sa_postQ asks, at the state before the epilogue *)
Definition sa_M4m ly S W (regs : bvmap 5 word) mem md (R : rstate) (O : list (Z * Z)) (uri : option (list byte)) (id : Z)
(placement client : option (list byte)) lyc Sc (Wc : world SEGS) (regs1 : bvmap 5 word) memc mdc (pos : Z) : Prop :=
let t := snd (sup_add_m R uri id placement client) in
sa_core ly S W regs mem md O lyc Sc Wc regs1 memc mdc (EV_SUP_ADD R) pos /\
sa_postQ ly S R O uri id placement client t lyc Sc Wc regs1 memc mdc.

(* the stage statements: from a mid-state at its label, the call's post-condition *)
Definition SA_ENTRY_stmt : Prop :=
forall ly S W regs mem md ch pu id pp pc uri placement client R O,
sa_cx ly S W regs mem md ch pu id pp pc uri placement client R O ->
SRr SEGS W (cfg_at SEGS (BASE + AF_sup_add) regs mem md) (sa_final ly S W regs mem md R O uri id placement client).
Definition SA_M0T_stmt : Prop :=
forall ly S W regs mem md ch pu id pp pc uri placement client R O lyc Sc Wc regs1 memc mdc pos,
sa_cx ly S W regs mem md ch pu id pp pc uri placement client R O ->
sa_M0 ly S W regs mem md R O lyc Sc Wc regs1 memc mdc pos -> (length (r_calls R) < 16)%nat ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + L_M0T)) memc (seg_rom SEGS)) mdc)
(sa_final ly S W regs mem md R O uri id placement client).
Definition SA_M0S_stmt : Prop :=
forall ly S W regs mem md ch pu id pp pc uri placement client R O lyc Sc Wc regs1 memc mdc pos,
sa_cx ly S W regs mem md ch pu id pp pc uri placement client R O ->
sa_M0 ly S W regs mem md R O lyc Sc Wc regs1 memc mdc pos -> length (r_calls R) = 16%nat ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + L_M0S)) memc (seg_rom SEGS)) mdc)
(sa_final ly S W regs mem md R O uri id placement client).
Definition SA_M1_stmt : Prop :=
forall ly S W regs mem md ch pu id pp pc uri placement client R O lyc Sc Wc regs1 memc mdc pos,
sa_cx ly S W regs mem md ch pu id pp pc uri placement client R O ->
sa_M1m ly S W regs mem md R O lyc Sc Wc regs1 memc mdc pos ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + L_M1)) memc (seg_rom SEGS)) mdc)
(sa_final ly S W regs mem md R O uri id placement client).
Definition SA_M2_stmt : Prop :=
forall ly S W regs mem md ch pu id pp pc uri placement client R O lyc Sc Wc regs1 memc mdc pos,
sa_cx ly S W regs mem md ch pu id pp pc uri placement client R O ->
sa_M2m ly S W regs mem md R O uri id lyc Sc Wc regs1 memc mdc pos ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + L_M2)) memc (seg_rom SEGS)) mdc)
(sa_final ly S W regs mem md R O uri id placement client).
Definition SA_M3_stmt : Prop :=
forall ly S W regs mem md ch pu id pp pc uri placement client R O lyc Sc Wc regs1 memc mdc pos,
sa_cx ly S W regs mem md ch pu id pp pc uri placement client R O ->
sa_M3m ly S W regs mem md R O uri id placement client lyc Sc Wc regs1 memc mdc pos ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + L_M3)) memc (seg_rom SEGS)) mdc)
(sa_final ly S W regs mem md R O uri id placement client).
Definition SA_M3b_stmt : Prop :=
forall ly S W regs mem md ch pu id pp pc uri placement client R O lyc Sc Wc regs1 memc mdc pos,
sa_cx ly S W regs mem md ch pu id pp pc uri placement client R O ->
sa_M3bm ly S W regs mem md R O uri id placement client lyc Sc Wc regs1 memc mdc pos ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + L_M3b)) memc (seg_rom SEGS)) mdc)
(sa_final ly S W regs mem md R O uri id placement client).
Definition SA_M4_stmt : Prop :=
forall ly S W regs mem md ch pu id pp pc uri placement client R O lyc Sc Wc regs1 memc mdc pos,
sa_cx ly S W regs mem md ch pu id pp pc uri placement client R O ->
sa_M4m ly S W regs mem md R O uri id placement client lyc Sc Wc regs1 memc mdc pos ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + L_M4)) memc (seg_rom SEGS)) mdc)
(sa_final ly S W regs mem md R O uri id placement client).
End e.
End f.
End d.
