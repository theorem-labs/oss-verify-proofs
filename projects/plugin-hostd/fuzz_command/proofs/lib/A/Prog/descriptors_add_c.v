(* The contract of descriptors_add on the ASan build of plugin-hostd/fuzz_command.
   The callees' contracts are taken at every FP state (forall fx0), so a walk can use them at the fx' a call returns.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return, the meter as cgif's trawnew_specX (:88, :92). Functional content:
   fuzz_command's own released plain contract lib/Prog/descriptors_add_c.v:27-52 and the model
   lib/Prog/RecModel.v:98 (`descriptors_add_m`, which is `rec_stub_mix` of the REC id 22, RecModel.v:81-82).
   descriptors_add (recorder.c:538-544) records the call with record() (inlined, recorder.c:205-221: a new slot of
   g_rec.calls, or record.spill with its arguments freed when the table already holds 16 calls), adds the
   argument (uri, the default "(null)" (RO_lit_22480) when it is NULL), folds the call into g_rec.state (g_rec +
   944) with
   mix_call and returns no value: a scan of the plugin's files starts, so the call changes the recorder's state
   digest.

   Addresses: entry BASE + AF_descriptors_add = 0x8ce34 (M, the pinned image). 91 instructions, 4 (load4:1 store4:2
   store8:1) inline checks, no loop, no side-stack frame anywhere below it. The error path of each check (a call of
   `__asan_report_*`) is not reached: the slot lies in g_rec or record.spill, whose shadow CmdRecFacts'
   cmd_addressable_chk gives as usable. The tail of the argument that xstrdup's strlen wrapper reads (RtDefs.v's
   atail_vis) comes from its heap block (CmdRecFacts' cmd_heap_tail_vis), as do the tails of the recorded
   arguments mix_call's strlen reads. s0 holds the slot (record.spill or a g_rec slot) at every program call, not
   a value of the caller. Callees: rec_calls_free, xstrdup, mix_call. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import rec_calls_free_c xstrdup_c mix_call_c.
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
Definition DESCRIPTORS_ADD_STK : Z := 64 + Z.max REC_CALLS_FREE_STK (Z.max XSTRDUP_STK (MIX_CALL_STK)).
(* the allocator events: the frees of record()'s spill arm and the copy of the recorded argument *)
Definition EV_DESCRIPTORS_ADD (R : rstate) : Z := rec_spill_frees R + EV_XSTRDUP.
(* the live bytes the call adds: the copy of the argument *)
Definition LIVE_DESCRIPTORS_ADD (uri : option (list byte)) : Z := LIVE_XSTRDUP (sarg uri).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the meter the call spends: the spill arm's frees and the copy *)
Definition XM_DESCRIPTORS_ADD (R : rstate) (uri : option (list byte)) : Z :=
  rec_spill_frees R * mo_free MT + XM_XSTRDUP MT (sarg uri).
(* the callees' contracts, and the bridge from the image's object addresses to the listing's atoms *)
Hypothesis TRCF : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT.
Hypothesis TXSTRDUP : forall fx0 : YK11.FPState, @txstrdup_spec fx0 rc SK PI B MT.
Hypothesis TMIX_CALL : forall fx0 : YK11.FPState, @tmix_call_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
Definition tdescriptors_add_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (pu : Z) (uri : option (list byte)) (R : rstate) (O : list (Z * Z)),
afn_pre SEGS B DESCRIPTORS_ADD_STK ly S W regs mem md ch ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
(* the read-only bytes of the image and their addresses: the default "(null)" (RO_lit_22480) on the NULL path,
   which no caller takes, and the FNV-1a offset basis mix_call reads (RO_lit_10330) *)
cmd_ro_ok (rdW W mem) ->
getr regs 10 = w64 pu -> 0 <= pu < 2 ^ 64 ->
(* uri: its one caller, verbs_receive, passes a token of its strdup'd copy (0x8daa8 `ld a0,8(s6)`, tok[1], after
   sup_add): a string in a live heap block that is none of the recorder's (record() frees the spill slot's blocks
   when the call table is full) *)
(exists x, uri = Some x /\
 in_blockA (ablocks B ly S) pu (Z.of_nat (length x) + 1) /\ astr_atR (rdW W mem) pu x /\
 Z.of_nat (length x) + 1 <= LMAX + 1 /\
 Forall (fun qk => iv_apart pu (Z.of_nat (length x) + 1) (fst qk) (snd qk)) O) ->
rec_repA B ly S (rdW W mem) R O ->
st_nev S + EV_DESCRIPTORS_ADD R <= EV_MAX -> blocks_bytes S + LIVE_DESCRIPTORS_ADD uri <= LIVE_MAX ->
mo_ok MT S (XM_DESCRIPTORS_ADD R uri) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_descriptors_add) regs mem md)
(apost_base SEGS B DESCRIPTORS_ADD_STK
 ((A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O)
 regs ly S W mem md (EV_DESCRIPTORS_ADD R)
(fun ly' S' W' regs' mem' md' => exists O' : list (Z * Z),
 (* the recorder's state after the call: the call recorded and folded into the state digest
    (plain lib/Prog/descriptors_add_c.v:27-52) *)
 rec_repA B ly' S' (rdW W' mem') (descriptors_add_m R uri) O' /\
 (* the recorder owns what it owned plus the block it made in this call *)
 (forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly' S')) /\
 (forall pn, In pn (ablocks B ly' S') -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O') /\
 blocks_bytes S' <= blocks_bytes S + LIVE_DESCRIPTORS_ADD uri /\
 mo_le MT S S' (XM_DESCRIPTORS_ADD R uri))).
End e.
End f.
End d.
