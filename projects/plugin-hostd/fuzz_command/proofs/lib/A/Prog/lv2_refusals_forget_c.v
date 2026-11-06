(* The contract of lv2_refusals_forget on the ASan build of plugin-hostd/fuzz_command.
   The callees' contracts are taken at every FP state (forall fx0), so a walk can use them at the fx' a call returns.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return, the meter as cgif's trawnew_specX (:88, :92). Functional content:
   fuzz_command's own released plain contract lib/Prog/lv2_refusals_forget_c.v:27-48 and the model
   lib/Prog/RecModel.v:95 (`lv2_refusals_forget_m`, which is `rec_stub_mix` of the REC id 25, RecModel.v:81-82).
   lv2_refusals_forget (recorder.c:563-569) records the call with record() (inlined, recorder.c:205-221: a new slot
   of
   g_rec.calls, or record.spill with its arguments freed when the table already holds 16 calls), adds the
   argument (uri, the default "*" (RO_lit_21fa0) when it is NULL), folds the call into g_rec.state (g_rec + 944)
   with
   mix_call and returns no value: the adapter is asked again about what it refused, so the call changes the
   recorder's state digest.

   Addresses: entry BASE + AF_lv2_refusals_forget = 0x8d278 (M, the pinned image). 91 instructions, 4 (load4:1
   store4:2 store8:1) inline checks,
   no loop, no side-stack frame anywhere below it. The error path of each check (a call of `__asan_report_*`)
   is not reached: the slot lies in g_rec or record.spill, whose shadow cmd_addressable_chk
   (lib/A/Prog/CmdRecFacts.v) shows usable. Callees: rec_calls_free, xstrdup, mix_call.
   The argument: both callers (verbs_receive at 0x8dd64, pin_set_words at 0x8e78c) pass NULL (a0 = 0, the return
   value pins_clear / pins_set just gave; lib/Spec/VerbsRun.v:32), so the argument keeps astr_argA's NULL case. *)
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
Definition LV2_REFUSALS_FORGET_STK : Z := 64 + Z.max REC_CALLS_FREE_STK (Z.max XSTRDUP_STK (MIX_CALL_STK)).
(* the allocator events: the frees of record()'s spill arm and the copy of the recorded argument *)
Definition EV_LV2_REFUSALS_FORGET (R : rstate) : Z := rec_spill_frees R + EV_XSTRDUP.
(* the live bytes the call adds: the copy of the argument *)
Definition LIVE_LV2_REFUSALS_FORGET (uri : option (list byte)) : Z := LIVE_XSTRDUP (darg uri (bstr "*"%string)).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the meter the call spends: the spill arm's frees and the copy *)
Definition XM_LV2_REFUSALS_FORGET (R : rstate) (uri : option (list byte)) : Z :=
  rec_spill_frees R * mo_free MT + XM_XSTRDUP MT (darg uri (bstr "*"%string)).
(* the callees' contracts, and the bridge from the image's object addresses to the listing's atoms *)
Hypothesis TRCF : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT.
Hypothesis TXSTRDUP : forall fx0 : YK11.FPState, @txstrdup_spec fx0 rc SK PI B MT.
Hypothesis TMIX_CALL : forall fx0 : YK11.FPState, @tmix_call_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
Definition tlv2_refusals_forget_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (pu : Z) (uri : option (list byte)) (R : rstate) (O : list (Z * Z)),
afn_pre SEGS B LV2_REFUSALS_FORGET_STK ly S W regs mem md ch ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
(* the read-only bytes of the image and their addresses: the default "*" (RO_lit_21fa0) of a NULL argument,
   and the FNV-1a offset basis mix_call reads (RO_lit_10330) *)
cmd_ro_ok (rdW W mem) ->
getr regs 10 = w64 pu -> 0 <= pu < 2 ^ 64 ->
(* the argument: NULL, a string in a live block that is none of the recorder's (record() frees the spill slot's
   blocks when the call table is full), or a read-only byte range of the image (the plain proof's str_arg,
   lib/Prog/RecKindB.v:164-175); for a string, the bytes after its terminator up to the end of that 8-byte word are
   readable (xstrdup's strlen wrapper reads them, RtDefs.v's atail_vis) *)
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O pu uri ->
(forall x, uri = Some x -> atail_vis SEGS W mem (pu + Z.of_nat (length x))) ->
rec_repA B ly S (rdW W mem) R O ->
st_nev S + EV_LV2_REFUSALS_FORGET R <= EV_MAX -> blocks_bytes S + LIVE_LV2_REFUSALS_FORGET uri <= LIVE_MAX ->
mo_ok MT S (XM_LV2_REFUSALS_FORGET R uri) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_lv2_refusals_forget) regs mem md)
(apost_base SEGS B LV2_REFUSALS_FORGET_STK
 ((A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O)
 regs ly S W mem md (EV_LV2_REFUSALS_FORGET R)
(fun ly' S' W' regs' mem' md' => exists O' : list (Z * Z),
 (* the recorder's state after the call: the call recorded and folded into the state digest
    (plain lib/Prog/lv2_refusals_forget_c.v:27-48) *)
 rec_repA B ly' S' (rdW W' mem') (lv2_refusals_forget_m R uri) O' /\
 (* the recorder owns what it owned plus the block it made in this call *)
 (forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly' S')) /\
 (forall pn, In pn (ablocks B ly' S') -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O') /\
 blocks_bytes S' <= blocks_bytes S + LIVE_LV2_REFUSALS_FORGET uri /\
 mo_le MT S S' (XM_LV2_REFUSALS_FORGET R uri))).
End e.
End f.
End d.
