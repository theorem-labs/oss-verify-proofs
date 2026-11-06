(* The contract of rec_calls_copy on the ASan build of plugin-hostd/fuzz_command.
   The callees' contracts are taken at every FP state (forall fx0), so a walk can use them at the fx' a call returns.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return; the fresh blocks and the meter as cgif's trawnew_specX states them
   (lib/YC7x.v:88, :92-101). Functional content: fuzz_command's own released plain contract
   lib/Prog/rec_calls_copy_c.v:18-65 (rcc_args; the copies dst[i] hold the recorder's calls with fresh argument
   blocks, the recorder kept), over the model lib/Prog/RecModel.v and the representation lib/A/Prog/CmdRep.v
   (rec_repA, acall_at). rec_calls_copy(dst) (H/recorder.c:148-160) copies g_rec.calls[i].fn and .nargs to dst[i]
   and sets dst[i].args[a] = xstrdup(g_rec.calls[i].args[a]), for i < g_rec.ncalls; it returns g_rec.ncalls.
   xstrdup's contract is a Section hypothesis (lib/A/Prog/xstrdup_c.v), not restated.

   Addresses: entry BASE + AF_rec_calls_copy = 0x896bc (M, the pinned image). 146 instructions, 2 loops (0x89730,
   0x897c4), no side-stack frame, 7 inline checks: load4 on g_rec.calls[i].fn and .nargs (0x8974c, 0x89780) and on
   dst[i].nargs (0x897e8), store4 on dst[i].fn and .nargs (0x89764, 0x89794), load8 on g_rec.calls[i].args[a] (0x897c4) and store8
   on dst[i].args[a] (0x897dc), each a read of the shadow byte at (a >> 3) + 0x7fff8000. The error path (a call of
   `__asan_report_*`) is not reached: g_rec is a registered global, whose shadow is usable by
   `cmd_addressable_chk`, and dst is an object of a live side-stack frame (afobj). g_rec's address is an auipc/addi
   pair (0x896f4), so the walk needs cmd_val_objs. Each argument handed to xstrdup is a live block of acall_at
   (xstrdup's astr_argA, block branch with O = []; its tail word by `cmd_heap_tail_vis`). s0 is the loop counter a
   (0x897a8) at the xstrdup calls, below alloc_ceiling, so achain_low gives xstrdup's afn_pre chain. Nothing is
   freed in the call, so the copies' freshness is the exact block equation below. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require rec_calls_copy_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep CmdObj.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import xstrdup_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Module PRcc := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.rec_calls_copy_c.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the stack this call needs: its own 144-byte frame, and xstrdup's *)
Definition REC_CALLS_COPY_STK : Z := 144 + XSTRDUP_STK.
(* the allocator events: one xstrdup for each argument of each recorded call (CmdRep.v ev_args) *)
Definition EV_REC_CALLS_COPY (R : rstate) : Z := EV_XSTRDUP * ev_args R.
(* the live bytes the call adds: one copy for each argument *)
Definition LIVE_REC_CALLS_COPY (R : rstate) : Z :=
fold_right (fun x acc => LIVE_XSTRDUP x + acc) 0 (PRcc.rcc_args (r_calls R)).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the meter the call spends: xstrdup's, once for each argument *)
Definition XM_REC_CALLS_COPY (R : rstate) : Z :=
fold_right (fun x acc => XM_XSTRDUP MT x + acc) 0 (PRcc.rcc_args (r_calls R)).
(* the callee's contract, and the bridge from the image's addresses to the listing's atoms *)
Hypothesis HXSTRDUP : forall fx0 : YK11.FPState, @txstrdup_spec fx0 rc SK PI B MT.
Hypothesis HVAL : cmd_val_objs.
Definition trec_calls_copy_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (dst : Z) (R : rstate) (O : list (Z * Z)),
afn_pre SEGS B REC_CALLS_COPY_STK ly S W regs mem md ch ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
getr regs 10 = w64 dst ->
(* the recorder's state, with at most 2 recorded calls per message (run_args,
   lib/A/Prog/HarnessArgs.v:80-82: after a whole message, run_receive including sup_after_reply, at most 2 calls
   and 5 arguments; the plain step_frame alone gives 3) *)
rec_repA B ly S (rdW W mem) R O ->
(length (r_calls R) <= 2)%nat ->
(* the copy table: an object of a live side-stack frame, room for the recorded calls (plain :40-41) *)
afobj SEGS B ly S W mem dst (CALL_SIZE * Z.of_nat (length (r_calls R))) ->
st_nev S + EV_REC_CALLS_COPY R <= EV_MAX -> blocks_bytes S + LIVE_REC_CALLS_COPY R <= LIVE_MAX ->
mo_ok MT S (XM_REC_CALLS_COPY R) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_rec_calls_copy) regs mem md)
(apost_base SEGS B REC_CALLS_COPY_STK [(dst, dst + CALL_SIZE * Z.of_nat (length (r_calls R)))]
 regs ly S W mem md (EV_REC_CALLS_COPY R)
(fun ly' S' W' regs' mem' md' => exists qs : list (list (Z * Z)),
 (* the number of calls copied (plain :47) *)
 getr regs' 10 = w64 (Z.of_nat (length (r_calls R))) /\
 (* dst[i] holds call i, its arguments in fresh blocks of |s| + 1 bytes (plain :48-52) *)
 length qs = length (r_calls R) /\
 (forall i c P, nth_error (r_calls R) i = Some c -> nth_error qs i = Some P ->
   acall_at (ablocks B ly' S') (rdW W' mem') (dst + CALL_SIZE * Z.of_nat i) c P /\
   forall a s pn, nth_error (snd c) a = Some s -> nth_error P a = Some pn -> snd pn = Z.of_nat (length s) + 1) /\
 (* the new blocks are exactly the copies, distinct and apart from every block that was live (plain :53-55) *)
 Permutation (ablocks B ly' S') (ablocks B ly S ++ concat qs) /\
 NoDup (map fst (concat qs)) /\
 (forall pn q, In pn (concat qs) -> In q (ablocks B ly S) -> iv_apart (fst pn) (snd pn) (fst q) (snd q)) /\
 (* the blocks that were live are kept, and so is the recorder (plain :56, :58) *)
 (forall p n i, In (p, n) (ablocks B ly S) -> 0 <= i < n -> rdW W' mem' (p + i) = rdW W mem (p + i)) /\
 rec_repA B ly' S' (rdW W' mem') R O /\
 blocks_bytes S' <= blocks_bytes S + LIVE_REC_CALLS_COPY R /\
 mo_le MT S S' (XM_REC_CALLS_COPY R))).
End e.
End f.
End d.
