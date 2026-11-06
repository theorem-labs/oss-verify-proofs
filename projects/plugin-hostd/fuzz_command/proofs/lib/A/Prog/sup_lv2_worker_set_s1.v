(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: restated for the statement of an earlier commit (heap-block string arguments, the
   kept-blocks freshness form, the blocks_bytes bound).
   Modified by Theorem Labs, 2026-10: the segment interface of sup_lv2_worker_set's ASan walk (plugin-hostd/fuzz_command,
   0x8be80, 120 instructions), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v and ACh1.v (a segment
   statement per return address, each proved from the next one). *)

(* sup_lv2_worker_set (recorder.c:445-452): block P (the inlined record(15)), two inlined arg_s blocks and the tail
   TA(.str.13 "lv2_worker_set", 14, 1) of the recorder-call walk plan template. The walk is cut at the return
   addresses of its calls:
     +0xc0  (0x8bf40) after the first xstrdup returns   SLW_C_stmt  (the state MID1, slw_mid1)
     +0x110 (0x8bf90) after the second xstrdup returns  SLW_D_stmt  (the state MID2, slw_mid2)
   Each statement says: from that state, the run reaches the statement's post (slw_post, the apost_baseF of
   lib/A/Prog/sup_lv2_worker_set_c.v:93-113 verbatim). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c xstrdup_c rec_shape_of_c answer_c sup_lv2_worker_set_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the return addresses the walk is cut at, and the call sites, as offsets from the listing's text atom *)
Definition SLW_RET1 : Z := AF_sup_lv2_worker_set + 0xc0.   (* 0x8bf40: after the first xstrdup *)
Definition SLW_RET2 : Z := AF_sup_lv2_worker_set + 0x110.  (* 0x8bf90: after the second xstrdup *)
Definition SLW_RET3 : Z := AF_sup_lv2_worker_set + 0x150.  (* 0x8bfd0: after rec_shape_of *)
(* the registers the 64-byte frame saves, in the order of their slots from the top: ra at sp0 - 8, s0 at sp0 - 16,
   ..., s5 at sp0 - 56 *)
Definition slw_saved : list Z := [1; 8; 9; 18; 19; 20; 21].
(* the slot the inlined record() fills: the next entry of g_rec's call table, or record.spill when the table holds
   16 calls (recorder.c:209-217) *)
Definition slw_slot (R : rstate) : Z :=
if Nat.ltb (length (r_calls R)) 16 then A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) else A_REC_SPILL.
(* the statement's footprint (sup_lv2_worker_set_c.v:95) *)
Definition slw_FP (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.
(* the two recorded arguments' block sizes *)
Definition slw_n (x : option (list byte)) : Z := Z.of_nat (length (sarg x)) + 1.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.

(* a string argument as the statement states it (sup_lv2_worker_set_c.v:89-96): a string in a live heap block,
   apart from the recorder's blocks O *)
Definition slw_harg ly S (rd : reader) (O : list (Z * Z)) (p : Z) (v : option (list byte)) : Prop :=
exists x, v = Some x /\
 in_blockA (ablocks B ly S) p (Z.of_nat (length x) + 1) /\ astr_atR rd p x /\
 Z.of_nat (length x) + 1 <= LMAX + 1 /\
 Forall (fun qk => iv_apart p (Z.of_nat (length x) + 1) (fst qk) (snd qk)) O.

(* the statement's premises (sup_lv2_worker_set_c.v:76-101), bundled *)
Definition slw_pre ly S (W : world SEGS) (regs : bvmap 5 word) mem md ch (pu pw : Z) (uri worker : option (list byte))
(R : rstate) (O : list (Z * Z)) : Prop :=
afn_pre SEGS B SUP_LV2_WORKER_SET_STK ly S W regs mem md ch /\
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 /\
arodata_okP SEGS RLO RHI B (rdW W mem) /\
cmd_ro_ok (rdW W mem) /\
getr regs 10 = w64 pu /\ 0 <= pu < 2 ^ 64 /\
getr regs 11 = w64 pw /\ 0 <= pw < 2 ^ 64 /\
slw_harg ly S (rdW W mem) O pu uri /\
slw_harg ly S (rdW W mem) O pw worker /\
rec_repA B ly S (rdW W mem) R O /\
Z.of_nat (length (frames S)) <= 8 /\
st_nev S + EV_SUP_LV2_WORKER_SET R <= EV_MAX /\ blocks_bytes S + LIVE_SUP_LV2_WORKER_SET R uri worker <= LIVE_MAX /\
mo_ok MT S (XM_SUP_LV2_WORKER_SET MT R uri worker).

(* the statement's post (sup_lv2_worker_set_c.v:106-125), verbatim *)
Definition slw_Q ly S (R : rstate) (uri worker : option (list byte)) (O : list (Z * Z))
: alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' => exists (R' : rstate) (t : list byte) (q : Z) (O' : list (Z * Z)),
 sup_lv2_worker_set_m R uri worker = (R', t) /\
 getr regs' 10 = w64 q /\ 4096 <= q < 2 ^ 64 /\
 rec_repA B ly' S' (rdW W' mem') R' O' /\
 (forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
 In (q, Z.of_nat (length t) + 1) (ablocks B ly' S') /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> pn <> (q, Z.of_nat (length t) + 1)) /\ ~ In q (map fst O') /\
 astr_atR (rdW W' mem') q t /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O ->
    In pn (ablocks B ly' S') /\ iv_apart (fst pn) (snd pn) q (Z.of_nat (length t) + 1)) /\
 (forall pn, In pn (ablocks B ly' S') ->
    (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O' \/ pn = (q, Z.of_nat (length t) + 1)) /\
 blocks_bytes S' <= blocks_bytes S + LIVE_SUP_LV2_WORKER_SET R uri worker /\
 mo_le MT S S' (XM_SUP_LV2_WORKER_SET MT R uri worker).
Definition slw_post ly S (W : world SEGS) (regs : bvmap 5 word) mem md (R : rstate) (uri worker : option (list byte))
(O : list (Z * Z)) : world SEGS -> config -> Prop :=
apost_baseF SEGS B SUP_LV2_WORKER_SET_STK (slw_FP O) regs ly S W mem md (EV_SUP_LV2_WORKER_SET R)
(slw_Q ly S R uri worker O).

(* the frame at a point of the walk: the entry values of ra, s0 .. s5 in their slots below the entry sp *)
Definition slw_frame (rd : reader) (sp0 : Z) (regs : bvmap 5 word) : Prop :=
forall j r, nth_error slw_saved j = Some r ->
aval_mem rd (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))).

(* MID1, the state at +0xc0 (0x8bf40), just after the first xstrdup returned the copy p1 of the first argument.
   - the journal from the entry, with the events spent so far (record()'s spill frees, one malloc);
   - the frame, and the registers the rest of the function reads (s0 = the slot c, s1 = the second argument,
     s2 = c + 4, s4 = the shadow base, s5 = the shadow byte address of c + 4, a0 = p1) and the ones it keeps
     (s6 .. s11, gp, tp);
   - the recorder: the slot holds FN = 15 with no argument (rec_record R 15 []), over the owned blocks O1 = O
     less the blocks Df record() freed on the spill arm (Df = [] on the slot arm);
   - the blocks: the entry's are Df ++ Lk, the current ones are p1's copy and Lk, the copy apart from every Lk
     block (xstrdup_c.v:92);
   - the second argument in the statement's form, at this state and against O1;
   - the meter spent so far. *)
Definition slw_mid1 ly S (W : world SEGS) (regs : bvmap 5 word) mem md (pw : Z) (uri worker : option (list byte))
(R : rstate) (O : list (Z * Z))
lyc Sc (Wc : world SEGS) (regs1 : bvmap 5 word) memc mdc (k p1 : Z) (Df Lk O1 : list (Z * Z)) : Prop :=
let sp0 := spZ regs in
let c := slw_slot R in
ajournal SEGS B SUP_LV2_WORKER_SET_STK sp0 (slw_FP O) ly S W mem md [] lyc Sc Wc memc mdc k /\
0 <= k <= rec_spill_frees R + EV_XSTRDUP /\
slw_frame (rdW Wc memc) sp0 regs /\
getr regs1 2 = w64 (sp0 - 64) /\ getr regs1 3 = getr regs 3 /\ getr regs1 4 = getr regs 4 /\
getr regs1 8 = w64 c /\ getr regs1 9 = w64 pw /\ getr regs1 18 = w64 (c + 4) /\
getr regs1 20 = w64 SHADOW_OFF /\ getr regs1 21 = w64 (SHADOW_OFF + (c + 4) / 8) /\
getr regs1 10 = w64 p1 /\
(forall r, 22 <= r <= 27 -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
rec_repA B lyc Sc (rdW Wc memc) (rec_record R REC_LV2_WORKER_SET []) O1 /\
(forall pn, In pn O1 <-> In pn O /\ ~ In pn Df) /\
(forall pn, In pn Df -> In pn O) /\
((length (r_calls R) < 16)%nat -> Df = []) /\
Permutation (ablocks B ly S) (Df ++ Lk) /\
Permutation (ablocks B lyc Sc) ((p1, slw_n uri) :: Lk) /\
Forall (fun qk => iv_apart p1 (slw_n uri) (fst qk) (snd qk)) Lk /\
4096 <= p1 < 2 ^ 64 /\ astr_atR (rdW Wc memc) p1 (sarg uri) /\
slw_harg lyc Sc (rdW Wc memc) O1 pw worker /\
mo_le MT S Sc (rec_spill_frees R * mo_free MT + XM_XSTRDUP MT (sarg uri)).

(* the statement of the segment from +0xc0 to the end *)
Definition SLW_C_stmt : Prop :=
forall ly S W regs mem md ch pu pw uri worker R O lyc Sc Wc regs1 memc mdc k p1 Df Lk O1,
slw_pre ly S W regs mem md ch pu pw uri worker R O ->
slw_mid1 ly S W regs mem md pw uri worker R O lyc Sc Wc regs1 memc mdc k p1 Df Lk O1 ->
SRr SEGS Wc (cfg_at SEGS (BASE + SLW_RET1) regs1 memc mdc) (slw_post ly S W regs mem md R uri worker O).

End e.
End f.
End d.
