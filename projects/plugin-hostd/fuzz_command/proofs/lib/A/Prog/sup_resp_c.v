(* The contract of sup_resp on the ASan build of plugin-hostd/fuzz_command.
   The post is FP-existential (apost_baseF, the printf wrappers' shared post); the pre carries rounding mode 0.
   The callees' contracts are taken at every FP state (forall fx0), so a walk can use them at the fx' a call returns.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return; the fresh block as cgif's trawnew_specX states it (lib/YC7x.v:93-101), the
   meter as there (:88, :92). Functional content: fuzz_command's own released plain contract
   lib/Prog/sup_resp_c.v:24-46 (a fresh block that holds `resp code` and its terminator, :36-41; the recorder kept,
   `fst (sup_resp_m R code)`, :42) and the model lib/Prog/RecModel.v:87 (`sup_resp_m R code = (R, resp code)`),
   lib/Prog/RecFacts.v:122 (`resp`).
   sup_resp(code) (recorder.c:279-285) prints "resp <code>" with snprintf(buf, 32, "resp %d", code) into buf[32] of
   its own side-stack frame and returns xstrdup(buf). It writes nothing the caller owns (FP = []).

   Addresses: entry BASE + AF_sup_resp = 0x89b84 (M, the pinned image). 122 instructions, no inline check; a
   side-stack frame of class 1 (`__asan_stack_malloc_1`, request 96 bytes, buf at frame + 32, released inline:
   shadow 0xf5 and the flag byte); the real-stack fallback and its one-pass probe loop are not taken (a per-binary
   fact: the use-after-return flag is the record's const cell as_uar_cell = 1, cgif lib/YG0f.v:193
   aso_const_law); callees: the snprintf wrapper, xstrdup. The stack-protector cells the musl body under the
   snprintf wrapper compares are cmd_rec_cells (lib/A/Prog/CmdRecFacts.v).
   Walk plan: the proposed contract in cgif form (its `spZ regs mod 32 = 0` premise is dropped: sup_resp realigns
   with `andi sp,sp,-32` at 0x89bb0, and the 16 bytes of slack are in SUP_RESP_STK). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import xstrdup_c.
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
(* the stack this call needs: its own 96-byte frame, 16 more for the realignment `andi sp,sp,-32` (sp mod 16 = 0 at
   the entry, afn_pre's astk_ok), and the deepest callee: the side-stack entry's window (ESTACK), the snprintf
   wrapper's (3 * ESTACK, the measured 6,672 bytes below the trampoline's entry sp), xstrdup's own need *)
Definition SUP_RESP_STK : Z := 96 + 16 + Z.max ESTACK (Z.max (3 * ESTACK) XSTRDUP_STK).
(* one allocator event: the malloc inside xstrdup; the side-stack frame spends none *)
Definition EV_SUP_RESP : Z := EV_XSTRDUP.
(* the live bytes the call adds: the copy of resp code, at most 17 bytes (RecFacts.v:124 resp_length) *)
Definition LIVE_SUP_RESP (code : Z) : Z := LIVE_XSTRDUP (resp code).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the meter the call spends: xstrdup's copy of resp code *)
Definition XM_SUP_RESP (code : Z) : Z := XM_XSTRDUP MT (resp code).
(* the callee's contract, the runtime entries with this tree's and cgif's names, and the bridge for the "resp %d"
   format's address *)
Hypothesis TXSTRDUP : forall fx0 : YK11.FPState, @txstrdup_spec fx0 rc SK PI B MT.
Hypothesis ASTACK_MALLOC1 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 1.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState, @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa7098 0x6045d8.
Hypothesis VOBJS : cmd_val_objs.
Definition tsup_resp_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (code : Z),
afn_pre SEGS B SUP_RESP_STK ly S W regs mem md ch ->
(* rounding mode 0 (frm = fcsr bits 5..7): the printf wrappers' frm0_entry; apost_baseF gives it back after a call *)
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
(* room for one more side-stack frame of class 1 (count_cid 1 < fs_frames 1) *)
Z.of_nat (length (frames S)) <= 8 ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
(* the read-only bytes of the image; the format "resp %d" is RO_lit_21d00 *)
cmd_ro_ok (rdW W mem) ->
getr regs 10 = w64 code -> -2 ^ 31 <= code < 2 ^ 31 ->
st_nev S + EV_SUP_RESP <= EV_MAX -> blocks_bytes S + LIVE_SUP_RESP code <= LIVE_MAX ->
mo_ok MT S (XM_SUP_RESP code) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_sup_resp) regs mem md)
(apost_baseF SEGS B SUP_RESP_STK [] regs ly S W mem md EV_SUP_RESP
(fun ly' S' W' regs' mem' md' => exists q,
 let n := Z.of_nat (length (resp code)) + 1 in
 getr regs' 10 = w64 q /\ 4096 <= q < 2 ^ 64 /\
 Permutation (ablocks B ly' S') ((q, n) :: ablocks B ly S) /\
 Forall (fun qk => iv_apart q n (fst qk) (snd qk)) (ablocks B ly S) /\
 (* the text resp code (= snd (sup_resp_m R code) for every R, RecModel.v:87) in the block form reply asks, and
    the recorder untouched (plain sup_resp_c.v:41-42) *)
 In (q, n) (ablocks B ly' S') /\ astr_atR (rdW W' mem') q (resp code) /\
 (forall R O, rec_repA B ly S (rdW W mem) R O -> rec_repA B ly' S' (rdW W' mem') (fst (sup_resp_m R code)) O) /\
 blocks_bytes S' <= blocks_bytes S + LIVE_SUP_RESP code /\
 mo_le MT S S' (XM_SUP_RESP code))).
End e.
End f.
End d.
