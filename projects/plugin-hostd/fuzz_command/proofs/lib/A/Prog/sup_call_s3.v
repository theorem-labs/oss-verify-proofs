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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaSB PaDenot PaLibG PaLibH PaCall CmdBase CmdRep CmdObj CmdZsh CmdAddr CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c arg_i_c arg_line_c answer_c sup_call_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import sup_call_s1 sup_call_s0.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the registers the frame holds, in the order of their slots below the entry sp: ra at sp0 - 8, s0 at sp0 - 16,
   s1 at sp0 - 24, s2 at sp0 - 32, s3 at sp0 - 40 (0x8a960 .. 0x8a970) *)
Definition sc_saved : list Z := [1; 8; 9; 18; 19].
(* the two arguments the call records (sup_call_m, RecModel.v:115-116) *)
Definition sc_args (id : Z) (line : list byte) : list (list byte) := [dec id; canon line].
(* the events the prologue and the body spend: the spill's frees, arg_i's and arg_line's *)
Definition EV_SC_ARGS (R : rstate) : Z := rec_spill_frees R + EV_ARG_I + EV_ARG_LINE.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the frame of the walk: the five saved registers at their slots below the entry sp (cgif's cl_frame) *)
Definition sc_frame (rd : reader) (sp0 : Z) (regs0 : bvmap 5 word) : Prop :=
forall j r, nth_error sc_saved j = Some r ->
aval_mem rd (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs0 (Z_to_bv 5 r))).

(* the registers at the join 0x8a9d0: sp is 48 below the entry's, s1 the call slot, s3 the shadow base, s2 the id
   and s0 the line; gp, tp and s4..s11 are the entry's *)
Definition sc_regs_join (regs0 regsc : bvmap 5 word) (c : Z) : Prop :=
spZ regsc = spZ regs0 - 48 /\
getr regsc 9 = w64 c /\ getr regsc 19 = w64 SB /\
getr regsc 18 = getr regs0 10 /\ getr regsc 8 = getr regs0 11 /\
getr regsc 3 = getr regs0 3 /\ getr regsc 4 = getr regs0 4 /\
(forall r : Z, 20 <= r <= 27 -> getr regsc (Z_to_bv 5 r) = getr regs0 (Z_to_bv 5 r)).

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.

(* the meter the prologue and the body spend *)
Definition XM_SC_ARGS (R : rstate) (id : Z) (line : list byte) : Z :=
rec_spill_frees R * mo_free MT + XM_ARG_I MT id + XM_ARG_LINE MT line.

(* the entry of the statement, premise for premise (sup_call_c.v:72-94) *)
Definition sc_pre ly S (W : world SEGS) (regs : bvmap 5 word) mem md ch (id pl : Z) (line : list byte)
(R : rstate) (O : list (Z * Z)) (t : list byte) : Prop :=
afn_pre SEGS B SUP_CALL_STK ly S W regs mem md ch /\
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 /\
Z.of_nat (length (frames S)) <= 8 /\
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

(* the line lies in a live block that is none of the recorder's: the statement's block premise with its
   `Forall iv_apart ... O` conjunct (sup_call_c.v:92-95), in the form the walk's calls use *)
Definition sc_line_blk ly S (O : list (Z * Z)) (pl : Z) (line : list byte) : Prop :=
exists p k, In (p, k) (ablocks B ly S) /\ ~ In (p, k) O /\ p <= pl /\ pl + Z.of_nat (length line) + 1 <= p + k.

(* the post of the statement (sup_call_c.v:95-116), with the statements' settled freshness conjunct
   (`forall pn, In pn (ablocks B ly S) -> ~ In pn O -> pn <> (q, n)`) *)
Definition sc_post ly S (W : world SEGS) (regs : bvmap 5 word) mem md (id : Z) (line : list byte)
(R : rstate) (O : list (Z * Z)) (t : list byte) : world SEGS -> config -> Prop :=
apost_baseF SEGS B SUP_CALL_STK (SC_FP O) regs ly S W mem md (EV_SUP_CALL R)
(fun ly' S' W' regs' mem' md' => exists R' O' q,
 sup_call_m R id line = (R', t) /\
 let n := Z.of_nat (length t) + 1 in
 getr regs' 10 = w64 q /\ 4096 <= q < 2 ^ 64 /\
 rec_repA B ly' S' (rdW W' mem') R' O' /\
 (forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
 (forall pn, In pn (ablocks B ly' S') -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O' \/ pn = (q, n)) /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly' S')) /\
 In (q, n) (ablocks B ly' S') /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> pn <> (q, n)) /\
 ~ In q (map fst O') /\
 astr_atR (rdW W' mem') q t /\
 blocks_bytes S' <= blocks_bytes S + LIVE_SUP_CALL id line t /\
 mo_le MT S S' (XM_SUP_CALL MT R id line t)).

(* the state at the join 0x8a9d0 (ly S W regs mem md: the entry; lyc Sc Wc regsc memc mdc: the join; k: the
   events so far; c: the call slot). record() has picked the slot and, on the spill arm, rec_calls_free has freed
   the spill's arguments; the slot's fields fn / nargs / args are not yet written. What the recorder step
   (sup_call_s2.v's sc_rep_slot / sc_rep_spill) asks about the bytes and blocks since the entry is kept per arm,
   with the entry's recorder layout Q. *)
Definition sc_mid ly S (W : world SEGS) (regs : bvmap 5 word) mem md (R : rstate) (O : list (Z * Z))
lyc Sc (Wc : world SEGS) (regsc : bvmap 5 word) memc mdc (k c : Z) : Prop :=
ajournal SEGS B SUP_CALL_STK (spZ regs) (SC_FP O) ly S W mem md [] lyc Sc Wc memc mdc k /\
0 <= k <= rec_spill_frees R /\
sc_slot c /\
sc_regs_join regs regsc c /\
sc_frame (rdW Wc memc) (spZ regs) regs /\
frames Sc = frames S /\ blocks_bytes Sc <= blocks_bytes S /\
mo_le MT S Sc (rec_spill_frees R * mo_free MT) /\
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc)) /\
exists Q, arep_at (ablocks B ly S) (rdW W mem) A_G_REC A_REC_SPILL R Q /\
 (forall pn, In pn O <-> In pn (lay_blocks Q)) /\
 (((length (r_calls R) < 16)%nat /\ c = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) /\
   ablocks B lyc Sc = ablocks B ly S /\
   aval_mem (rdW Wc memc) (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls R)) + 1) /\
   (forall a, A_G_REC <= a < A_G_REC + REC_SIZE ->
      ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) -> rdW Wc memc a = rdW W mem a) /\
   (forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> rdW Wc memc a = rdW W mem a) /\
   (forall p m i, In (p, m) (ablocks B ly S) -> 0 <= i < m -> rdW Wc memc (p + i) = rdW W mem (p + i))) \/
  ((length (r_calls R) = 16)%nat /\ c = A_REC_SPILL /\
   (forall pn, In pn (ablocks B lyc Sc) <-> In pn (ablocks B ly S) /\ ~ In pn (l_spill Q)) /\
   (forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> rdW Wc memc a = rdW W mem a) /\
   (forall p m i, In (p, m) (ablocks B ly S) -> ~ In (p, m) (l_spill Q) -> 0 <= i < m ->
      rdW Wc memc (p + i) = rdW W mem (p + i)))).

(* the body and the tail: from the join to sup_call's post *)
Definition SC_B_stmt : Prop :=
forall ly S W regs mem md ch id pl line R O lyc Sc Wc regsc memc mdc k c,
let t := snd (sup_call_m R id line) in
sc_pre ly S W regs mem md ch id pl line R O t ->
sc_line_blk ly S O pl line ->
sc_mid ly S W regs mem md R O lyc Sc Wc regsc memc mdc k c ->
SRr SEGS Wc (mkCfg (mkst regsc (Z_to_bv 64 (BASE + sc_mid_pc)) memc (seg_rom SEGS)) mdc)
(sc_post ly S W regs mem md id line R O t).

(* the state at answer's entry, after the epilogue and `j answer` (0x8aa40): the frame is popped, so sp, ra, gp,
   tp and every callee-saved register are the entry's; a0 = the slot, a1 = the shape "resp 0", a2 = 1; the call
   (REC_CALL, [dec id; canon line]) is recorded in the slot, with its two new blocks among the recorder's
   blocks Ot. The guard cell answer's snprintf reads is not here: the tail takes it at its own state from the
   record (cmd_rec_cells). *)
Definition sc_tail ly S (W : world SEGS) (regs : bvmap 5 word) mem md ch (R : rstate) (O : list (Z * Z))
(id : Z) (line : list byte) (t : list byte)
lyt St (Wt : world SEGS) (regst : bvmap 5 word) memt mdt (kt : Z) (c : Z) (Ot : list (Z * Z)) : Prop :=
ajournal SEGS B SUP_CALL_STK (spZ regs) (SC_FP O) ly S W mem md [] lyt St Wt memt mdt kt /\
0 <= kt <= EV_SC_ARGS R /\
spZ regst = spZ regs /\ getr regst 1 = getr regs 1 /\ aregs_preserved regs regst /\
getr regst 3 = w64 (as_gp B) /\ getr regst 4 = w64 (as_tp B) /\
getr regst 10 = w64 c /\ getr regst 11 = w64 0x21ce0 /\ getr regst 12 = w64 1 /\
achain lyt (rdW Wt memt) (spZ regst) (s0Z regst) ch /\
((length (r_calls R) < 16)%nat /\ c = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) \/
 (16 <= length (r_calls R))%nat /\ c = A_REC_SPILL) /\
rec_repA B lyt St (rdW Wt memt) (rec_record R REC_CALL (sc_args id line)) Ot /\
(forall pn, In pn Ot -> In pn O \/ ~ In pn (ablocks B ly S)) /\
(forall pn, In pn (ablocks B lyt St) -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn Ot) /\
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyt St)) /\
frames St = frames S /\
(* the live bytes the two argument calls added (arg_i's and arg_line's posts); with sc_pre's LIVE_MAX premise it
   gives answer's own `blocks_bytes St + LIVE_ANSWER t <= LIVE_MAX`, and the statement's post bound *)
blocks_bytes St <= blocks_bytes S + LIVE_ARG_I id + LIVE_ARG_LINE line /\
mo_le MT S St (XM_SC_ARGS R id line) /\
arodata_okP SEGS RLO RHI B (rdW Wt memt) /\ cmd_ro_ok (rdW Wt memt).

(* the tail: answer's contract at that state gives sup_call's post *)
Definition SC_T_stmt : Prop :=
forall ly S W regs mem md ch id pl line R O lyt St Wt regst memt mdt kt c Ot,
let t := snd (sup_call_m R id line) in
sc_pre ly S W regs mem md ch id pl line R O t ->
sc_tail ly S W regs mem md ch R O id line t lyt St Wt regst memt mdt kt c Ot ->
SRr SEGS Wt (mkCfg (mkst regst (Z_to_bv 64 (BASE + AF_answer)) memt (seg_rom SEGS)) mdt)
(sc_post ly S W regs mem md id line R O t).
End e.
End f.
End w.
