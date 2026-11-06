(* The contract of rec_clear on the ASan build of plugin-hostd/fuzz_command.
   The callees' contracts are taken at every FP state (forall fx0), so a walk can use them at the fx' a call returns.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return. Functional content: fuzz_command's own released plain contract
   lib/Prog/rec_clear_c.v:31-54 (g_rec_rep of `rec_clear R`, the freed blocks D = O minus O', Permutation of the
   blocks) and the model lib/Prog/RecModel.v:57-58 (`rec_clear`: no calls, no answer, no reply, nreplies 0; state,
   host_settings and the spill kept).
   The function frees the arguments of every recorded call (rec_calls_free(g_rec.calls, g_rec.ncalls)), sets
   ncalls to 0, frees the answer and the reply text (either may be NULL) and zeroes answer, nreplies, reply and
   reply_size (the last two with one 16-byte call of the memory-checking runtime's memset entry).
   Its event count is a function of the recorder state (this port's decision for the five contracts whose counts can
   multiply): one free per recorded argument (`ev_args R`, lib/A/Prog/CmdRep.v) and the two frees of the answer
   and the reply.

   Addresses: entry BASE + AF_rec_clear = 0x894d4 (M, the pinned image). 26 instructions, no inline check (every
   g_rec access is at a constant offset of the global, reached by auipc), no loop, no side-stack frame. Calls:
   rec_calls_free (0x8953c), the free wrapper twice (0x58980), the runtime's memset entry (0x57acc). The memset
   entry's write range g_rec + 928 .. + 944 has usable shadow by `cmd_addressable_chk` and is unowned and in the
   image by `cmd_prog_unowned`. s0 is the caller's at rec_calls_free and the first free (afn_pre's achain, carried
   by achain_lower) and g_rec + 928 at the second free (below the stack, empty chain): no achain premise. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep CmdObj.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import rec_calls_free_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG c := (@pa_sigma _ cmd_listing PI c).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the stack this call needs: its own 32-byte frame, and the deeper of rec_calls_free's need and the window the
   free wrapper asks for (cgif's afree04_rule, ASTACK, lib/YG0d.v:17); the memset entry asks for ESTACK only *)
Definition REC_CLEAR_STK : Z := 32 + Z.max REC_CALLS_FREE_STK ASTACK.
(* one free per recorded argument, and free(g_rec.answer), free(g_rec.reply); free(NULL) is an event too
   (cgif's afree_null04_rule, lib/YC5d.v:97-116) *)
Definition EV_REC_CLEAR (R : rstate) : Z := ev_args R + 2.
(* the live bytes the call adds: none, it only frees *)
Definition LIVE_REC_CLEAR : Z := 0.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Definition XM_REC_CLEAR (R : rstate) : Z := (ev_args R + 2) * mo_free MT.
(* the callee and the runtime entries this call reaches *)
Hypothesis TRCF : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT.
Hypothesis AFREE4 : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT.
Hypothesis AFREE_NULL4 : forall fx0 : YK11.FPState, @afree_null04_rule fx0 rc SK SEGS B MT.
Hypothesis AMEMSET : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OSet (SIG CS___asan_memset).
Hypothesis VOBJS : cmd_val_objs.
Definition trec_clear_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (R : rstate) (O : list (Z * Z)),
afn_pre SEGS B REC_CLEAR_STK ly S W regs mem md ch ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
(* the recorder's state, with O the blocks it owns (every argument of every call and of the spill, the answer,
   the reply); the freed ones are among them, so they are in the footprint *)
rec_repA B ly S (rdW W mem) R O ->
(* at most 2 recorded calls per message (run_args, lib/A/Prog/HarnessArgs.v:80-82: after a whole message, run_receive including sup_after_reply, at most 2 calls and 5 arguments; the plain step_frame alone gives 3);
   rec_calls_free's contract asks it of the table it frees (lib/A/Prog/rec_calls_free_c.v:76) *)
(length (r_calls R) <= 2)%nat ->
st_nev S + EV_REC_CLEAR R <= EV_MAX ->
mo_ok MT S (XM_REC_CLEAR R) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_rec_clear) regs mem md)
(apost_base SEGS B REC_CLEAR_STK ((A_G_REC, A_G_REC + REC_SIZE) :: ablocks_fp O) regs ly S W mem md
(EV_REC_CLEAR R)
(fun ly' S' W' regs' mem' md' => exists (O' D : list (Z * Z)),
(* the recorder holds RecModel.rec_clear R; it keeps only the spill's blocks *)
rec_repA B ly' S' (rdW W' mem') (RecModel.rec_clear R) O' /\
(forall pn, In pn O' -> In pn O) /\
(* the freed blocks: those of O it no longer owns, and no other block *)
(forall pn, In pn D <-> In pn O /\ ~ In pn O') /\
Permutation (ablocks B ly S) (ablocks B ly' S' ++ D) /\
blocks_bytes S' <= blocks_bytes S + LIVE_REC_CLEAR /\
mo_le MT S S' (XM_REC_CLEAR R))).
End e.
End f.
End d.
