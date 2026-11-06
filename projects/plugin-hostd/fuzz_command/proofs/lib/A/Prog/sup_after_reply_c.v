(* The contract of sup_after_reply on the ASan build of plugin-hostd/fuzz_command.
   The post is FP-existential (apost_baseF, the printf wrappers' shared post); the pre carries rounding mode 0.
   The callees' contracts are taken at every FP state (forall fx0), so a walk can use them at the fx' a call returns.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return, the meter as cgif's trawnew_specX (:88, :92). Functional content:
   fuzz_command's own released plain contract lib/Prog/sup_after_reply_c.v:17-55 and the model
   lib/Prog/RecModel.v:165-166 (`sup_after_reply_m`, which is `rec_record` of the REC id 19 alone: a checkpoint
   of what a preset or patch changed, so it writes the call down and changes no digest).
   sup_after_reply (recorder.c:490-496) records the call with record() (inlined, recorder.c:205-221: a new slot
   of g_rec.calls, or record.spill with its arguments freed when the table already holds 16 calls), adds the
   instance number with arg_i and the verb with arg_s (xstrdup of the string, "(null)" when it is NULL), and
   returns. It calls neither answer nor mix_call.

   Addresses: entry BASE + AF_sup_after_reply = 0x8c658 (M, the pinned image). 100 instructions, 5 (load4:2
   store4:2 store8:1) inline checks, no loop, no side-stack frame of its own (arg_i takes one of class 0). The
   error path of each check (a call of `__asan_report_*`) is not reached: the slot lies in g_rec or record.spill,
   whose shadow CmdRecFacts' cmd_addressable_chk gives as usable. The stack-protector GOT word 0xa7098 and guard
   cell 0x6045d8, which the snprintf wrapper under arg_i reads (RtDefs.v's aguard_ok), come from CmdRecFacts'
   cmd_rec_cells; the tail of the verb that xstrdup's strlen wrapper reads (RtDefs.v's atail_vis), from its heap block
   (cmd_heap_tail_vis). s0 holds the argument verb (0x8c678 `mv s0,a1`) at the calls of rec_calls_free (0x8c6b0)
   and arg_i (0x8c70c) and xstrdup (0x8c734); the slot is in s1. Callees: rec_calls_free, arg_i, xstrdup. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import rec_calls_free_c arg_i_c xstrdup_c.
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
(* the stack this call needs: its own 64-byte frame and the deepest callee *)
Definition SUP_AFTER_REPLY_STK : Z := 64 + Z.max REC_CALLS_FREE_STK (Z.max ARG_I_STK (XSTRDUP_STK)).
(* the allocator events: the frees of record()'s spill arm and the two recorded arguments *)
Definition EV_SUP_AFTER_REPLY (R : rstate) : Z := rec_spill_frees R + EV_ARG_I + EV_XSTRDUP.
(* the live bytes the call adds: the copies of the two arguments *)
Definition LIVE_SUP_AFTER_REPLY (id : Z) (verb : option (list byte)) : Z :=
  LIVE_ARG_I id + LIVE_XSTRDUP (sarg verb).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the meter the call spends: the spill arm's frees and the two copies *)
Definition XM_SUP_AFTER_REPLY (R : rstate) (id : Z) (verb : option (list byte)) : Z :=
  rec_spill_frees R * mo_free MT + XM_ARG_I MT id + XM_XSTRDUP MT (sarg verb).
(* the callees' contracts, and the bridge from the image's object addresses to the listing's atoms *)
Hypothesis TRCF : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT.
Hypothesis TARG_I : forall fx0 : YK11.FPState, @targ_i_spec fx0 rc SK PI B MT.
Hypothesis TXSTRDUP : forall fx0 : YK11.FPState, @txstrdup_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
Definition tsup_after_reply_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (id pv : Z) (verb : option (list byte)) (R : rstate)
 (O : list (Z * Z)),
afn_pre SEGS B SUP_AFTER_REPLY_STK ly S W regs mem md ch ->
(* rounding mode 0 (frm = fcsr bits 5..7): the printf wrappers' frm0_entry; apost_baseF gives it back after a call *)
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
(* the read-only bytes of the image and their addresses: the "%d" format arg_i prints with (RO_lit_21f00) and the
   default "(null)" (RO_lit_22480) on the NULL path, which no caller takes *)
cmd_ro_ok (rdW W mem) ->
getr regs 10 = w64 id -> -2 ^ 31 <= id < 2 ^ 31 ->
getr regs 11 = w64 pv -> 0 <= pv < 2 ^ 64 ->
(* verb: its one caller, verbs_receive, passes a token of its strdup'd copy (0x8db48 `mv a1,s8`, tok[0]): a
   string in a live heap block that is none of the recorder's (record() frees the spill slot's blocks when the
   call table is full) *)
(exists x, verb = Some x /\
 in_blockA (ablocks B ly S) pv (Z.of_nat (length x) + 1) /\ astr_atR (rdW W mem) pv x /\
 Z.of_nat (length x) + 1 <= LMAX + 1 /\
 Forall (fun qk => iv_apart pv (Z.of_nat (length x) + 1) (fst qk) (snd qk)) O) ->
rec_repA B ly S (rdW W mem) R O ->
(* room for one more side-stack frame: arg_i takes one of class 0 *)
Z.of_nat (length (frames S)) <= 8 ->
st_nev S + EV_SUP_AFTER_REPLY R <= EV_MAX -> blocks_bytes S + LIVE_SUP_AFTER_REPLY id verb <= LIVE_MAX ->
mo_ok MT S (XM_SUP_AFTER_REPLY R id verb) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_sup_after_reply) regs mem md)
(apost_baseF SEGS B SUP_AFTER_REPLY_STK
 ((A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O)
 regs ly S W mem md (EV_SUP_AFTER_REPLY R)
(fun ly' S' W' regs' mem' md' => exists O' : list (Z * Z),
 (* the recorder's state after the call: the call recorded, nothing else changed (plain
    lib/Prog/sup_after_reply_c.v:27-41) *)
 rec_repA B ly' S' (rdW W' mem') (sup_after_reply_m R id verb) O' /\
 (* the recorder owns what it owned plus the block it made in this call *)
 (forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly' S')) /\
 (forall pn, In pn (ablocks B ly' S') -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O') /\
 blocks_bytes S' <= blocks_bytes S + LIVE_SUP_AFTER_REPLY id verb /\
 mo_le MT S S' (XM_SUP_AFTER_REPLY R id verb))).
End e.
End f.
End d.
