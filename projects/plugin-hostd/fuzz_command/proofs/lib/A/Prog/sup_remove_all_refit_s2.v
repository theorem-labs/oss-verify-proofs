(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the assembly of sup_pin_accept's ASan walk (plugin-hostd/fuzz_command) from
   its two halves, after proofs/cgif/cgif_file_fuzzer/lib/A/ACke.v (the instantiation file of a cgif walk). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/sup_pin_accept.v, with its module names changed; 62 of its 89 lines of code are new or changed and 40 lines of the source are left out. *)
(* sup_remove_all's walk on the ASan build of plugin-hostd/fuzz_command, the shared statements: the footprint and
   the post-condition of lib/A/Prog/sup_remove_all_c.v, the statement as the walk proves it, and the step at the
   tail jump `j answer` (0x8acf8) that both arms of record() reach.

   tsup_remove_all_specF is tsup_remove_all_spec (sup_remove_all_c.v:65-106) with its footprint named sra_FP and
   its post-condition named sra_post; the two are convertible, so the walk's theorem gives tsup_remove_all_spec by
   `exact`.

   Pass-4/5 re-fit (the re-fit recipe's worked example; copied from an earlier version of
   lib/A/Prog/sup_remove_all_s2.v): both statements take the rounding-mode-0 premise after afn_pre and end in
   apost_baseF (statement pass 4), and have no astack_pres premise (statement pass 5), as sup_remove_all_c.v. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import rec_calls_free_c answer_c sup_remove_all_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
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
(* the footprint of sup_remove_all_c.v:84-85 *)
Definition sra_FP (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC + OFF_NCALLS, A_G_REC + OFF_NCALLS + 4) :: (A_G_REC + OFF_CALLS, A_G_REC + OFF_ANSWER + 8) ::
(A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.
(* the post-condition of sup_remove_all_c.v:88-103 *)
Definition sra_post (ly : alayout) (S : astate) (R : rstate) (O : list (Z * Z)) (t : list byte)
: alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' => exists R' O' q,
 sup_remove_all_m R = (R', t) /\
 let n := Z.of_nat (length t) + 1 in
 getr regs' 10 = w64 q /\ 4096 <= q < 2 ^ 64 /\
 rec_repA B ly' S' (rdW W' mem') R' O' /\
 (forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
 (forall pn, In pn (ablocks B ly' S') -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O' \/ pn = (q, n)) /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly' S')) /\
 In (q, n) (ablocks B ly' S') /\ (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> pn <> (q, n)) /\
 ~ In q (map fst O') /\
 astr_atR (rdW W' mem') q t /\
 blocks_bytes S' <= blocks_bytes S + LIVE_SUP_REMOVE_ALL t /\
 mo_le MT S S' (XM_SUP_REMOVE_ALL MT R t).
(* tsup_remove_all_spec (sup_remove_all_c.v:63-103) with that footprint and post-condition *)
Definition tsup_remove_all_specF : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (R : rstate) (O : list (Z * Z)),
let t := snd (sup_remove_all_m R) in
afn_pre SEGS B SUP_REMOVE_ALL_STK ly S W regs mem md ch ->
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
Z.of_nat (length (frames S)) <= 8 ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
cmd_ro_ok (rdW W mem) ->
rec_repA B ly S (rdW W mem) R O ->
st_nev S + EV_SUP_REMOVE_ALL R <= EV_MAX -> blocks_bytes S + LIVE_SUP_REMOVE_ALL t <= LIVE_MAX ->
mo_ok MT S (XM_SUP_REMOVE_ALL MT R t) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_sup_remove_all) regs mem md)
(apost_baseF SEGS B SUP_REMOVE_ALL_STK (sra_FP O) regs ly S W mem md (EV_SUP_REMOVE_ALL R) (sra_post ly S R O t)).
(* the step at the tail jump `j answer` (0x8acf8): the walk has reached answer's entry (world Wt) with its frame
   released, a0 = the slot c that record() filled, a1 = the shape "resp 0" (0x21ce0), a2 = 1, and every other
   register the entry's (aregs_preserved; ra = the entry's ra). The journal from the entry is J1 (k1 events: the
   spill's frees when the table was full, none otherwise); the blocks freed on the way are `freed`, all of them
   the recorder's; the recorder now holds R1 = rec_record R REC_REMOVE_ALL [] with the blocks O1 = O less
   `freed`. *)
Definition sra_tail_stmt : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (R : rstate) (O : list (Z * Z))
  lyc Sc (Wt : world SEGS) memT mdT (regsT : bvmap 5 word) k1 freed O1 c,
let t := snd (sup_remove_all_m R) in
afn_pre SEGS B SUP_REMOVE_ALL_STK ly S W regs mem md ch ->
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
Z.of_nat (length (frames S)) <= 8 ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
rec_repA B ly S (rdW W mem) R O ->
st_nev S + EV_SUP_REMOVE_ALL R <= EV_MAX -> blocks_bytes S + LIVE_SUP_REMOVE_ALL t <= LIVE_MAX ->
mo_ok MT S (XM_SUP_REMOVE_ALL MT R t) ->
ajournal SEGS B SUP_REMOVE_ALL_STK (spZ regs) (sra_FP O) ly S W mem md [] lyc Sc Wt memT mdT k1 ->
k1 = rec_spill_frees R ->
Permutation (ablocks B ly S) (ablocks B lyc Sc ++ freed) ->
(forall pn, In pn freed -> In pn O) ->
(forall pn, In pn O1 <-> In pn O /\ ~ In pn freed) ->
mo_le MT S Sc (k1 * mo_free MT) ->
rec_repA B lyc Sc (rdW Wt memT) (rec_record R REC_REMOVE_ALL []) O1 ->
((exists k, nth_error (r_calls (rec_record R REC_REMOVE_ALL [])) k = Some (REC_REMOVE_ALL, []) /\
   c = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat k) \/
 (c = A_REC_SPILL /\ r_spill (rec_record R REC_REMOVE_ALL []) = (REC_REMOVE_ALL, []))) ->
0 <= c < 2 ^ 64 ->
aregs_preserved regs regsT -> getr regsT 1 = getr regs 1 ->
getr regsT 10 = w64 c -> getr regsT 11 = w64 0x21ce0 -> getr regsT 12 = w64 1 ->
SRr SEGS Wt (cfg_at SEGS (BASE + AF_answer) regsT memT mdT)
(apost_baseF SEGS B SUP_REMOVE_ALL_STK (sra_FP O) regs ly S W mem md (EV_SUP_REMOVE_ALL R) (sra_post ly S R O t)).
End e.
End f.
End d.
