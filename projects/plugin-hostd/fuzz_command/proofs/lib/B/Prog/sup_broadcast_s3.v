(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the stage interfaces of the sup_broadcast walk on fuzz_command.asan-ubsan
   (0x8b4f0, 19 instructions): the walk's state at each of its three calls and at the two return points, and the
   form of what each call step gives. B's code is three straight-line runs around three calls:
     0x8b4f0 .. `jal record` (0x8b508)    the own frame (ra, s0, s1 at sp + 24, 16, 8), s0 := line, a0 := 5;
     0x8b50c .. `jal arg_line` (0x8b514)  s1 := the slot record returned, a1 := line;
     0x8b518 .. `j answer` (0x8b538)      a1 := the shape 0x21d20, a2 := 1, a0 := the slot, the frame restored.
   The states are relative to the entry state (ly S W regs mem md): sp0 = spZ regs, the statement's footprint
   sb_FP O, the journal from the entry. The call steps' forms are the conclusion of the kit's call rule for a callee whose
   footprint holds program statics (PaCallPg.v cl_callS_pg, from PaNoChain.v cl_callS_wide) with the callee's
   post-condition: record_c.v:107-119, arg_line_c.v:102-113 (m = 0), and for the tail call of answer
   (answer_c.v:140-155) the FP-existential form of PaFx.v's cl_callS_pgF and apost_baseF (CmdBase.v:77-85). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
record_c arg_line_c answer_c sup_broadcast_c sup_broadcast_s1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the three words the prologue saves: ra at sp0 - 8, s0 at sp0 - 16, s1 at sp0 - 24 (sd at 0x8b4f4 .. 0x8b4fc) *)
Definition sbb_frame (regs : bvmap 5 word) (rd : reader) : Prop :=
aval_mem rd (spZ regs - 8) 8 (raZ regs) /\ aval_mem rd (spZ regs - 16) 8 (s0Z regs) /\
aval_mem rd (spZ regs - 24) 8 (bv_unsigned (getr regs 9)).

(* record's footprint (record_c.v:104-105) *)
Definition sbb_rec_FP (R : rstate) (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC + OFF_NCALLS, A_G_REC + OFF_NCALLS + 4) :: (rec_slot R, rec_slot R + 8) ::
(if Nat.ltb (length (r_calls R)) 16 then [] else ablocks_fp O).

(* arg_line's footprint for nargs = 0 (arg_line_c.v:98-100) *)
Definition sbb_al_FP (c : Z) : list (Z * Z) :=
if 0 <? REC_ARGS_MAX
then [(c + CALL_OFF_NARGS, c + CALL_OFF_NARGS + 4); (c + CALL_OFF_ARGS + 8 * 0, c + CALL_OFF_ARGS + 8 * 0 + 8)]
else [].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.

(* the statement's premises (sup_broadcast_c.v:78-100) less cmd_ro_ok, which cmd_ro_ok_of_aro gives from
   arodata_okP *)
Definition sbb_ent ly S (W : world SEGS) regs mem md ch (pl : Z) (line : list byte) (R : rstate) (O : list (Z * Z)) : Prop :=
afn_pre SEGS B SUP_BROADCAST_STK ly S W regs mem md ch /\
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 /\
Z.of_nat (length (frames S)) <= 8 /\
arodata_okP SEGS RLO RHI B (rdW W mem) /\
getr regs 10 = w64 pl /\ 0 <= pl < 2 ^ 64 /\
in_blockA (ablocks B ly S) pl (Z.of_nat (length line) + 1) /\
Forall (fun qk => iv_apart pl (Z.of_nat (length line) + 1) (fst qk) (snd qk)) O /\
astr_atR (rdW W mem) pl line /\ Z.of_nat (length line) + 1 <= LMAX + 1 /\
rec_repA B ly S (rdW W mem) R O /\
st_nev S + EV_SUP_BROADCAST R <= EV_MAX /\
blocks_bytes S + LIVE_SUP_BROADCAST line (snd (sup_broadcast_m R line)) <= LIVE_MAX /\
mo_ok MT S (XM_SUP_BROADCAST MT R line (snd (sup_broadcast_m R line))).

(* ---------------------------------------------------------------- the call of record (0x8b508) *)
(* the state at record's entry, after the prologue and `jal record`: the frame written, s0 = line, a0 = 5 *)
Definition sbb_at_rec ly S (W : world SEGS) regs mem md (pl : Z) (R : rstate) (O : list (Z * Z))
(regsX : bvmap 5 word) memX mdX : Prop :=
ajournal SEGS B SUP_BROADCAST_STK (spZ regs) (sb_FP O) ly S W mem md [] ly S W memX mdX 0 /\
spZ regsX = spZ regs - 32 /\
getr regsX 1 = Z_to_bv 64 (BASE + SBB_RET_REC) /\
getr regsX 8 = w64 pl /\ getr regsX 10 = w64 REC_BROADCAST /\
(forall r, acallee_saved r -> r <> 2 -> r <> 8 -> getr regsX (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
sbb_frame regs (rdW W memX) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) -> rdW W memX a = rdW W mem a) /\
arodata_okP SEGS RLO RHI B (rdW W memX) /\
rec_repA B ly S (rdW W memX) R O.

(* record's post-condition at fn = REC_BROADCAST (record_c.v:107-119) *)
Definition sbb_rec_Q ly S (R : rstate) (O : list (Z * Z)) :
alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' => exists (F O' : list (Z * Z)),
 getr regs' 10 = w64 (rec_slot R) /\
 Permutation (ablocks B ly S) (ablocks B ly' S' ++ F) /\
 Z.of_nat (length F) = rec_spill_frees R /\
 (forall pn, In pn F -> In pn O) /\
 rec_repA B ly' S' (rdW W' mem') (rec_record R REC_BROADCAST []) O' /\
 (forall pn, In pn O' <-> In pn O /\ ~ In pn F) /\
 blocks_bytes S' <= blocks_bytes S /\
 mo_le MT S S' (XM_RECORD MT R).

(* what the call step gives at record's return (cl_callS_pg's conclusion with record's post) *)
Definition sbb_post_rec ly S (W : world SEGS) regs mem md (R : rstate) (O : list (Z * Z))
(regsX : bvmap 5 word) memX mdX : world SEGS -> config -> Prop :=
fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
 c2 = mkCfg (mkst regs2 (Z_to_bv 64 (BASE + SBB_RET_REC)) mem2 (seg_rom SEGS)) md2 /\
 ajournal SEGS B SUP_BROADCAST_STK (spZ regs) (sb_FP O) ly S W mem md [] ly2 S2 W2 mem2 md2 (0 + EV_RECORD R) /\
 ajournal SEGS B RECORD_STK (spZ regs + -32) (sbb_rec_FP R O) ly S W memX mdX [] ly2 S2 W2 mem2 md2 (EV_RECORD R) /\
 aregs_preserved regsX regs2 /\
 sbb_rec_Q ly S R O ly2 S2 W2 regs2 mem2 md2.

(* the state at record's return (0x8b50c): the slot in a0, the recorder holds (5, []) in it, the blocks F freed *)
Definition sbb_ret_rec ly S (W : world SEGS) regs mem md (pl : Z) (line : list byte) (R : rstate) (O : list (Z * Z))
ly1 S1 (W1 : world SEGS) (regs1 : bvmap 5 word) mem1 md1 (F O1 : list (Z * Z)) : Prop :=
ajournal SEGS B SUP_BROADCAST_STK (spZ regs) (sb_FP O) ly S W mem md [] ly1 S1 W1 mem1 md1 (EV_RECORD R) /\
spZ regs1 = spZ regs - 32 /\
getr regs1 8 = w64 pl /\ getr regs1 10 = w64 (rec_slot R) /\
(forall r, acallee_saved r -> r <> 2 -> r <> 8 -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
sbb_frame regs (rdW W1 mem1) /\
arodata_okP SEGS RLO RHI B (rdW W1 mem1) /\
rec_repA B ly1 S1 (rdW W1 mem1) (rec_record R REC_BROADCAST []) O1 /\
(forall pn, In pn O1 <-> In pn O /\ ~ In pn F) /\
Permutation (ablocks B ly S) (ablocks B ly1 S1 ++ F) /\ (forall pn, In pn F -> In pn O) /\
Z.of_nat (length F) = rec_spill_frees R /\
in_blockA (ablocks B ly1 S1) pl (Z.of_nat (length line) + 1) /\
astr_atR (rdW W1 mem1) pl line /\
blocks_bytes S1 <= blocks_bytes S /\
mo_le MT S S1 (XM_RECORD MT R).

(* ---------------------------------------------------------------- the call of arg_line (0x8b514) *)
(* the state at arg_line's entry: s1 = a0 = the slot, a1 = s0 = line; the slot's nargs field is 0 (RecBridge.v
   rec_bridge_slot) *)
Definition sbb_at_al ly S (W : world SEGS) regs mem md (pl : Z) (line : list byte) (R : rstate) (O : list (Z * Z))
ly1 S1 (W1 : world SEGS) (regsX : bvmap 5 word) memX mdX (F O1 : list (Z * Z)) : Prop :=
ajournal SEGS B SUP_BROADCAST_STK (spZ regs) (sb_FP O) ly S W mem md [] ly1 S1 W1 memX mdX (EV_RECORD R) /\
spZ regsX = spZ regs - 32 /\
getr regsX 1 = Z_to_bv 64 (BASE + SBB_RET_AL) /\
getr regsX 8 = w64 pl /\ getr regsX 9 = w64 (rec_slot R) /\
getr regsX 10 = w64 (rec_slot R) /\ getr regsX 11 = w64 pl /\
(forall r, acallee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> getr regsX (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
sbb_frame regs (rdW W1 memX) /\
arodata_okP SEGS RLO RHI B (rdW W1 memX) /\
rec_repA B ly1 S1 (rdW W1 memX) (rec_record R REC_BROADCAST []) O1 /\
(forall pn, In pn O1 <-> In pn O /\ ~ In pn F) /\
Permutation (ablocks B ly S) (ablocks B ly1 S1 ++ F) /\ (forall pn, In pn F -> In pn O) /\
Z.of_nat (length F) = rec_spill_frees R /\
in_blockA (ablocks B ly1 S1) pl (Z.of_nat (length line) + 1) /\
astr_atR (rdW W1 memX) pl line /\
blocks_bytes S1 <= blocks_bytes S /\
mo_le MT S S1 (XM_RECORD MT R) /\
sb_slot (rec_slot R) /\
aval_mem (rdW W1 memX) (rec_slot R + CALL_OFF_NARGS) 4 0.

(* arg_line's post-condition at nargs m = 0 (arg_line_c.v:102-113) *)
Definition sbb_al_Q ly1 S1 (line : list byte) (c : Z) :
alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' =>
 blocks_bytes S' <= blocks_bytes S1 + LIVE_ARG_LINE line /\
 mo_le MT S1 S' (XM_ARG_LINE MT line) /\
 ((0 = REC_ARGS_MAX /\ Permutation (ablocks B ly' S') (ablocks B ly1 S1)) \/
  (0 < REC_ARGS_MAX /\ exists p,
    let n := Z.of_nat (length line) + 1 in
    4096 <= p < 2 ^ 64 /\
    Permutation (ablocks B ly' S') ((p, n) :: ablocks B ly1 S1) /\
    Forall (fun qk => iv_apart p n (fst qk) (snd qk)) (ablocks B ly1 S1) /\
    aval_mem (rdW W' mem') (c + CALL_OFF_NARGS) 4 (0 + 1) /\
    aval_mem (rdW W' mem') (c + CALL_OFF_ARGS + 8 * 0) 8 p /\
    astr_atR (rdW W' mem') p (canon line))).

(* what the call step gives at arg_line's return *)
Definition sbb_post_al ly S (W : world SEGS) regs mem md (line : list byte) (R : rstate) (O : list (Z * Z))
ly1 S1 (W1 : world SEGS) (regsX : bvmap 5 word) memX mdX : world SEGS -> config -> Prop :=
fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
 c2 = mkCfg (mkst regs2 (Z_to_bv 64 (BASE + SBB_RET_AL)) mem2 (seg_rom SEGS)) md2 /\
 ajournal SEGS B SUP_BROADCAST_STK (spZ regs) (sb_FP O) ly S W mem md [] ly2 S2 W2 mem2 md2 (EV_RECORD R + EV_ARG_LINE) /\
 ajournal SEGS B ARG_LINE_STK (spZ regs + -32) (sbb_al_FP (rec_slot R)) ly1 S1 W1 memX mdX [] ly2 S2 W2 mem2 md2 EV_ARG_LINE /\
 aregs_preserved regsX regs2 /\
 sbb_al_Q ly1 S1 line (rec_slot R) ly2 S2 W2 regs2 mem2 md2.

(* the state at arg_line's return (0x8b518): the recorder holds (5, [canon line]) in the slot and owns the new block
   (p, |line| + 1) (RecBridge.v rec_bridge_add); the history of the blocks for the post-condition *)
Definition sbb_ret_al ly S (W : world SEGS) regs mem md (line : list byte) (R : rstate) (O : list (Z * Z))
ly1 S1 (F O1 : list (Z * Z)) lyA SA (WA : world SEGS) (regsA : bvmap 5 word) memA mdA (p : Z) : Prop :=
ajournal SEGS B SUP_BROADCAST_STK (spZ regs) (sb_FP O) ly S W mem md [] lyA SA WA memA mdA (EV_RECORD R + EV_ARG_LINE) /\
spZ regsA = spZ regs - 32 /\
getr regsA 9 = w64 (rec_slot R) /\
(forall r, acallee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> getr regsA (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
sbb_frame regs (rdW WA memA) /\
arodata_okP SEGS RLO RHI B (rdW WA memA) /\
rec_repA B lyA SA (rdW WA memA) (rec_record R REC_BROADCAST [canon line]) ((p, Z.of_nat (length line) + 1) :: O1) /\
(forall pn, In pn O1 <-> In pn O /\ ~ In pn F) /\
Permutation (ablocks B ly S) (ablocks B ly1 S1 ++ F) /\ (forall pn, In pn F -> In pn O) /\
(forall pn, In pn O1 -> In pn (ablocks B ly1 S1)) /\
Permutation (ablocks B lyA SA) ((p, Z.of_nat (length line) + 1) :: ablocks B ly1 S1) /\
Forall (fun qk => iv_apart p (Z.of_nat (length line) + 1) (fst qk) (snd qk)) (ablocks B ly1 S1) /\
4096 <= p < 2 ^ 64 /\
blocks_bytes SA <= blocks_bytes S1 + LIVE_ARG_LINE line /\ blocks_bytes S1 <= blocks_bytes S /\
mo_le MT S SA (XM_RECORD MT R + XM_ARG_LINE MT line).

(* ---------------------------------------------------------------- the tail call of answer (0x8b538) *)
(* the state at answer's entry, after the frame is restored and `j answer`: answer's premises (answer_c.v:105-133)
   less afn_pre, which the call rule gives; the call rule's facts (the journal, sp = sp0, ra and the callee-saved
   registers the entry's, the entry's frame chain); the block history *)
Definition sbb_at_ans ly S (W : world SEGS) regs mem md ch (line : list byte) (R : rstate) (O : list (Z * Z))
ly1 S1 (F O1 : list (Z * Z)) lyT ST (WT : world SEGS) (regsT : bvmap 5 word) memT mdT (p old : Z) : Prop :=
ajournal SEGS B SUP_BROADCAST_STK (spZ regs) (sb_FP O) ly S W mem md [] lyT ST WT memT mdT (EV_RECORD R + EV_ARG_LINE) /\
spZ regsT = spZ regs + 0 /\
getr regsT 1 = getr regs 1 /\
aregs_preserved regs regsT /\
achain lyT (rdW WT memT) (spZ regs + 0) (s0Z regsT) ch /\
Z.of_nat (length (frames ST)) <= 8 /\
arodata_okP SEGS RLO RHI B (rdW WT memT) /\
cmd_ro_ok (rdW WT memT) /\
getr regsT 10 = w64 (rec_slot R) /\ 0 <= rec_slot R < 2 ^ 64 /\
getr regsT 11 = w64 SBB_SHAPE_ADDR /\ 0 <= SBB_SHAPE_ADDR < 2 ^ 64 /\
true = negb (bv_unsigned (getr regsT 12) =? 0) /\
rec_repA B lyT ST (rdW WT memT) (rec_record R REC_BROADCAST [canon line]) ((p, Z.of_nat (length line) + 1) :: O1) /\
aval_mem (rdW WT memT) (A_G_REC + OFF_ANSWER) 8 old /\ 0 <= old < 2 ^ 64 /\
(old = 0 \/ exists ko, In (old, ko) ((p, Z.of_nat (length line) + 1) :: O1)) /\
(r_refuse (rec_record R REC_BROADCAST [canon line]) = 0 ->
 astr_argA B lyT ST (rdW WT memT) (in_roP SEGS RLO RHI) ((p, Z.of_nat (length line) + 1) :: O1) SBB_SHAPE_ADDR
   (Some REC_MOD_HOST_SHAPE) /\ fits REC_MOD_HOST_SHAPE) /\
(r_refuse (rec_record R REC_BROADCAST [canon line]) = 0 -> true = true ->
 (exists kk, nth_error (r_calls (rec_record R REC_BROADCAST [canon line])) kk = Some (REC_BROADCAST, [canon line]) /\
   rec_slot R = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat kk) \/
 (rec_slot R = A_REC_SPILL /\ (REC_BROADCAST, [canon line]) = r_spill (rec_record R REC_BROADCAST [canon line]))) /\
st_nev ST + EV_ANSWER <= EV_MAX /\
blocks_bytes ST + LIVE_ANSWER (snd (sup_broadcast_m R line)) <= LIVE_MAX /\
mo_ok MT ST (XM_ANSWER MT (snd (sup_broadcast_m R line))) /\
(forall pn, In pn O1 <-> In pn O /\ ~ In pn F) /\
Permutation (ablocks B ly S) (ablocks B ly1 S1 ++ F) /\ (forall pn, In pn F -> In pn O) /\
(forall pn, In pn O1 -> In pn (ablocks B ly1 S1)) /\
Permutation (ablocks B lyT ST) ((p, Z.of_nat (length line) + 1) :: ablocks B ly1 S1) /\
Forall (fun qk => iv_apart p (Z.of_nat (length line) + 1) (fst qk) (snd qk)) (ablocks B ly1 S1) /\
blocks_bytes ST <= blocks_bytes S1 + LIVE_ARG_LINE line /\ blocks_bytes S1 <= blocks_bytes S /\
mo_le MT S ST (XM_RECORD MT R + XM_ARG_LINE MT line).

(* answer's post-condition at e = (REC_BROADCAST, [canon line]), x = the shape, chg = true, over the recorder
   rec_record R REC_BROADCAST [canon line] (answer_c.v:140-155; rec_answer of that state is sup_broadcast_m R line,
   RecModel.v:73-75, :128-129) *)
Definition sbb_ans_Q lyT ST (line : list byte) (R : rstate) (O2 : list (Z * Z)) (old : Z) :
alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' => exists p1 p2 O',
 let n := Z.of_nat (length (snd (sup_broadcast_m R line))) + 1 in
 getr regs' 10 = w64 p2 /\ 4096 <= p2 < 2 ^ 64 /\ p1 <> p2 /\
 (forall pn, In pn (ablocks B lyT ST) -> fst pn <> old -> pn <> (p1, n) /\ pn <> (p2, n)) /\
 (forall pn, In pn (ablocks B ly' S') <->
   (In pn (ablocks B lyT ST) /\ fst pn <> old) \/ pn = (p1, n) \/ pn = (p2, n)) /\
 rec_repA B ly' S' (rdW W' mem') (fst (sup_broadcast_m R line)) O' /\
 (forall pn, In pn O' <-> (In pn O2 /\ fst pn <> old) \/ pn = (p1, n)) /\
 astr_atR (rdW W' mem') p2 (snd (sup_broadcast_m R line)) /\
 blocks_bytes S' <= blocks_bytes ST + LIVE_ANSWER (snd (sup_broadcast_m R line)) /\
 mo_le MT ST S' (XM_ANSWER MT (snd (sup_broadcast_m R line))).

(* what the tail-call step gives: the FP-existential return (apost_baseF's configuration and f-register clauses),
   the journal from sup_broadcast's entry, answer's registers and post-condition *)
Definition sbb_post_ans ly S (W : world SEGS) regs mem md (line : list byte) (R : rstate) (O : list (Z * Z))
lyT ST (regsT : bvmap 5 word) (O2 : list (Z * Z)) (old : Z) : world SEGS -> config -> Prop :=
fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 regs2 mem2 md2,
 c2 = mkCfg (@mkst fx' regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
 (forall kr : bv 5, bv_unsigned kr <> 10 -> Sem.reg_get (@fp_regs fx') kr = Sem.reg_get (@fp_regs fx) kr) /\
 (@fp_csr fx' = @fp_csr fx \/ Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = 0) /\
 ajournal SEGS B SUP_BROADCAST_STK (spZ regs) (sb_FP O) ly S W mem md [] ly2 S2 W2 mem2 md2
   (EV_RECORD R + EV_ARG_LINE + EV_ANSWER) /\
 aregs_preserved regsT regs2 /\
 sbb_ans_Q lyT ST line R O2 old ly2 S2 W2 regs2 mem2 md2.

End e.
End f.
End d.
