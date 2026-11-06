(* The contract of sup_instance_verb on the ASan build of plugin-hostd/fuzz_command.
   The post is FP-existential (apost_baseF, the printf wrappers' shared post); the pre carries rounding mode 0.
   The callees' contracts are taken at every FP state (forall fx0), so a walk can use them at the fx' a call returns.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return; the fresh block the caller gets as cgif's trawnew_specX states one
   (lib/YC7x.v:93-101), the meter as there (:88, :92). Functional content: fuzz_command's own released plain
   contract lib/Prog/sup_instance_verb_c.v:18-65 and the model lib/Prog/RecModel.v:135-136
   (`sup_instance_verb_m`, `rec_stub` of the REC id 7 with the canonical line and the ledger number, and the
   reply shape of the line's first word, `shape_of (first_word line)`, RecModel.v:68, :73-75).
   sup_instance_verb (recorder.c:379-388) records the call with record() (inlined, recorder.c:205-221: a new slot
   of g_rec.calls, or record.spill with its arguments freed when the table already holds 16 calls), adds the
   canonical line with arg_line and the ledger number with arg_i, steps the line past its leading spaces and tabs
   (the strspn wrapper) and measures its first word (the strcspn wrapper), asks rec_shape_of for the shape that
   word declares, and tail-jumps to answer with changes = 1. It releases its own frame before the jump, so answer
   runs at this function's entry stack pointer.

   Addresses: entry BASE + AF_sup_instance_verb = 0x8b3b8 (M, the pinned image). 78 instructions, 2 (store4:2)
   inline checks, no loop, no side-stack frame of its own. The error path of each check (a call of
   `__asan_report_*`) is not reached: the slot lies in g_rec or record.spill, whose shadow CmdRecFacts'
   cmd_addressable_chk gives as usable. Callees: rec_calls_free, arg_line, arg_i, rec_shape_of, answer; the strspn
   and strcspn wrappers (`___interceptor_strspn` and `___interceptor_strcspn`, reached through their 4-byte
   trampolines). What those wrappers ask beyond the premises comes from CmdRecFacts: the stack-protector GOT word
   0xa7098 and guard cell 0x6045d8 (aguard_ok, lib/A/Rt/RtDefs.v, also read by the snprintf wrapper under arg_i and
   answer) from cmd_rec_cells; the separators' aread_ok and tail from cmd_aread_ok_chk and cmd_tail_vis; the line's tail
   (atail_vis, lib/A/Rt/RtDefs.v, also read by arg_line's strlen) from its heap block by cmd_heap_tail_vis. s0 holds the
   slot (record.spill or a g_rec slot) at every program call, not a value of the caller. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import rec_calls_free_c arg_line_c arg_i_c rec_shape_of_c answer_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the stack this call needs: its own 48-byte frame and the deepest callee reached with the frame up (the
   strspn and strcspn wrappers ask for 2 * ESTACK, astrspn_realizes of lib/A/Rt/RtString.v); the tail jump `j answer`
   runs answer at this function's entry sp, so its need is taken beside the frame, not on top of it *)
Definition SUP_INSTANCE_VERB_OWN : Z :=
  48 + Z.max REC_CALLS_FREE_STK (Z.max ARG_LINE_STK
       (Z.max ARG_I_STK (Z.max REC_SHAPE_OF_STK (2 * ESTACK)))).
Definition SUP_INSTANCE_VERB_STK : Z := Z.max SUP_INSTANCE_VERB_OWN ANSWER_STK.
(* the allocator events: the frees of record()'s spill arm, the canonical line and the ledger number, and
   answer's free of the old answer with the two copies of the reply text *)
Definition EV_SUP_INSTANCE_VERB (R : rstate) : Z := rec_spill_frees R + EV_ARG_LINE + EV_ARG_I + EV_ANSWER.
(* the live bytes the call adds at its peak: the two recorded arguments and answer's two copies *)
Definition LIVE_SUP_INSTANCE_VERB (R : rstate) (line : list byte) (ledger : Z) : Z :=
  LIVE_ARG_LINE line + LIVE_ARG_I ledger + LIVE_ANSWER (snd (sup_instance_verb_m R line ledger)).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the meter the call spends: the spill arm's frees, the two recorded arguments, and answer's *)
Definition XM_SUP_INSTANCE_VERB (R : rstate) (line : list byte) (ledger : Z) : Z :=
  rec_spill_frees R * mo_free MT + XM_ARG_LINE MT line +
  XM_ARG_I MT ledger + XM_ANSWER MT (snd (sup_instance_verb_m R line ledger)).
(* the callees' contracts, and the bridge from the image's object addresses to the listing's atoms *)
Hypothesis TRCF : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT.
Hypothesis TARG_LINE : forall fx0 : YK11.FPState, @targ_line_spec fx0 rc SK PI B MT.
Hypothesis TARG_I : forall fx0 : YK11.FPState, @targ_i_spec fx0 rc SK PI B MT.
Hypothesis TREC_SHAPE_OF : forall fx0 : YK11.FPState, @trec_shape_of_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis ASTRSPN : forall fx0 : YK11.FPState, @astrspn_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strspn) 0xa7098 0x6045d8.
Hypothesis ASTRCSPN : forall fx0 : YK11.FPState, @astrcspn_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcspn) 0xa7098 0x6045d8.
Hypothesis VOBJS : cmd_val_objs.
Definition tsup_instance_verb_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (pl ledger : Z) (line : list byte) (R : rstate) (O : list (Z * Z)),
afn_pre SEGS B SUP_INSTANCE_VERB_STK ly S W regs mem md ch ->
(* rounding mode 0 (frm = fcsr bits 5..7): the printf wrappers' frm0_entry; apost_baseF gives it back after a call *)
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
(* the read-only bytes of the image and their addresses: the separators " \t" the strspn and strcspn
   wrappers read (RO_lit_21d60), the verb names and reply shapes rec_shape_of walks (RO_g_shapes and the
   strings it points to), and what answer reads *)
cmd_ro_ok (rdW W mem) ->
getr regs 10 = w64 pl -> 0 <= pl < 2 ^ 64 ->
getr regs 11 = w64 ledger -> -2 ^ 31 <= ledger < 2 ^ 31 ->
(* the line: its one caller, verbs_receive, passes its strndup'd line (0x8de18 `ld s2,24(s1)`, the block of
   verbs.c:219), so it is a string in a live heap block that is none of the recorder's (record() and answer free
   the recorder's own blocks during the call); arg_line takes it in this form. The verb rec_shape_of looks up is
   the first word of the line, past the spaces and tabs strspn counts, and strcspn long (recorder.c:386-387), so
   its bytes are bytes of the line, in the same block *)
in_blockA (ablocks B ly S) pl (Z.of_nat (length line) + 1) -> astr_atR (rdW W mem) pl line ->
Z.of_nat (length line) + 1 <= LMAX + 1 ->
Forall (fun qk => iv_apart pl (Z.of_nat (length line) + 1) (fst qk) (snd qk)) O ->
rec_repA B ly S (rdW W mem) R O ->
(* room for one more side-stack frame: answer takes one of class 7, arg_i one of class 0 *)
Z.of_nat (length (frames S)) <= 8 ->
st_nev S + EV_SUP_INSTANCE_VERB R <= EV_MAX -> blocks_bytes S + LIVE_SUP_INSTANCE_VERB R line ledger <= LIVE_MAX ->
mo_ok MT S (XM_SUP_INSTANCE_VERB R line ledger) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_sup_instance_verb) regs mem md)
(apost_baseF SEGS B SUP_INSTANCE_VERB_STK
 ((A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O)
 regs ly S W mem md (EV_SUP_INSTANCE_VERB R)
(fun ly' S' W' regs' mem' md' => exists (R' : rstate) (t : list byte) (q : Z) (O' : list (Z * Z)),
 (* the model's step: the recorder's new state and the reply text (plain lib/Prog/sup_instance_verb_c.v:28-50) *)
 sup_instance_verb_m R line ledger = (R', t) /\
 getr regs' 10 = w64 q /\ 4096 <= q < 2 ^ 64 /\
 rec_repA B ly' S' (rdW W' mem') R' O' /\
 (* the recorder owns what it owned, less what it freed, plus the blocks it made in this call *)
 (forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
 (* the caller's copy of the reply text: a block of its own, which the recorder does not own and which is none of
    the blocks that were live and none of the recorder's (record()'s spill arm and answer free recorder blocks,
    whose address and size malloc may hand out again) *)
 In (q, Z.of_nat (length t) + 1) (ablocks B ly' S') /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> pn <> (q, Z.of_nat (length t) + 1)) /\ ~ In q (map fst O') /\
 astr_atR (rdW W' mem') q t /\
 (* every block that was live and none of the recorder's is still live, and apart from the copy *)
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O ->
    In pn (ablocks B ly' S') /\ iv_apart (fst pn) (snd pn) q (Z.of_nat (length t) + 1)) /\
 (forall pn, In pn (ablocks B ly' S') ->
    (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O' \/ pn = (q, Z.of_nat (length t) + 1)) /\
 blocks_bytes S' <= blocks_bytes S + LIVE_SUP_INSTANCE_VERB R line ledger /\
 mo_le MT S S' (XM_SUP_INSTANCE_VERB R line ledger))).
End e.
End f.
End d.
