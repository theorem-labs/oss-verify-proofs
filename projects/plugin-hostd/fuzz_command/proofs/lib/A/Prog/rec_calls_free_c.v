(* The contract of rec_calls_free on the ASan build of plugin-hostd/fuzz_command.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return; the freed blocks in the footprint as cgif's journal asks (lib/YCbq.v:365-366),
   the meter as cgif's trawnew_specX (lib/YC7x.v:88, :92). Functional content: fuzz_command's own released plain
   contract lib/Prog/rec_calls_free_c.v:17-79 (calls_slots, freed, nargs_field: every argument block freed, every
   nargs field set to 0, every other byte of the array kept) and its g_rec form :81-114, over the model
   lib/Prog/RecModel.v (set_calls, set_spill) and the representation lib/A/Prog/CmdRep.v (arep_at, rec_repA).
   rec_calls_free(calls, n) (H/recorder.c:136-146) frees calls[i].args[a] for a < calls[i].nargs through the free
   wrapper, then stores 0 to calls[i].nargs, for i < n. Its three callers hand it g_rec's call table (rec_clear),
   record.spill (record(), inlined in the 26 recording functions) and the copy table first[] in check_round_trip's
   side-stack frame; the post states the recorder's model state after the call for each of the three.

   Addresses: entry BASE + AF_rec_calls_free = 0x8953c (M, the pinned image). 96 instructions, 2 loops (0x8959c,
   0x895e8), no side-stack frame, 4 inline checks: load4 on calls[i].nargs (0x895bc, 0x895f8), load8 on
   calls[i].args[a] (0x895e8) and store4 on calls[i].nargs (0x89624), each a read of the shadow byte at
   (a >> 3) + 0x7fff8000. The error path (a call of `__asan_report_*`) is not reached: the table lies in g_rec or
   record.spill, whose shadow is usable by `cmd_addressable_chk`, or in a side-stack frame object (afobj).
   s0 holds n (at most 2) at the free calls, below the stack, so the free wrapper's chain_pre holds with the empty
   chain; no program call. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require rec_calls_free_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Module PRcf := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.rec_calls_free_c.
(* the bytes the call writes outside its frame: the nargs field of each of the n entries, and the blocks it frees
   (cgif's journal asks every freed byte to be in the footprint, lib/YCbq.v:366). For g_rec's table these are
   ranges inside [A_G_REC, A_G_REC + 960), for the spill inside [A_REC_SPILL, A_REC_SPILL + 56). *)
Definition rcf_fp (c : Z) (ps : list (list (Z * Z))) : list (Z * Z) :=
map (fun i => (c + CALL_SIZE * Z.of_nat i + CALL_OFF_NARGS, c + CALL_SIZE * Z.of_nat i + CALL_OFF_NARGS + 4))
  (seq 0 (length ps)) ++ ablocks_fp (concat ps).
(* the calls of the model after the call: the same functions, no arguments *)
Definition rcf_cleared (cs : list rcall) : list rcall := map (fun c => (fst c, @nil (list byte))) cs.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the stack this call needs: its own 112-byte frame, and the window the free wrapper asks for (ASTACK, cgif
   lib/YG0d.v:17; afree04_rule asks ASTACK - o <= STK, lib/YC5d.v:80) *)
Definition REC_CALLS_FREE_STK : Z := 112 + ASTACK.
(* one allocator event per free: one for each argument slot of the n entries *)
Definition EV_REC_CALLS_FREE (ps : list (list (Z * Z))) : Z := Z.of_nat (length (concat ps)).
(* the live bytes the call adds: none, it only frees *)
Definition LIVE_REC_CALLS_FREE : Z := 0.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the meter the call spends: one free for each argument slot *)
Definition XM_REC_CALLS_FREE (ps : list (list (Z * Z))) : Z := Z.of_nat (length (concat ps)) * mo_free MT.
(* where the table lies: in g_rec's call table, in record.spill (registered globals, shadow usable by
   `cmd_addressable_chk`), or in an object of a live side-stack frame *)
Definition rcf_home (ly : alayout) (S : astate) (W : world SEGS) (mem : word -> option byte) (c n : Z) : Prop :=
(A_G_REC + OFF_CALLS <= c /\ c + n <= A_G_REC + REC_SIZE) \/
(A_REC_SPILL <= c /\ c + n <= A_REC_SPILL + SC_SIZE) \/
afobj SEGS B ly S W mem c n.
(* the runtime entry the call reaches *)
Hypothesis AFREE4 : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT.
Definition trec_calls_free_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (c : Z) (ps : list (list (Z * Z))),
afn_pre SEGS B REC_CALLS_FREE_STK ly S W regs mem md ch ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
getr regs 10 = w64 c -> getr regs 11 = w64 (Z.of_nat (length ps)) ->
(* at most 2 recorded calls per message (run_args, lib/A/Prog/HarnessArgs.v:80-82: after a whole message, run_receive including sup_after_reply, at most 2 calls and 5 arguments; the plain step_frame alone gives 3) *)
(length ps <= 2)%nat ->
rcf_home ly S W mem c (CALL_SIZE * Z.of_nat (length ps)) ->
(* the table pointer is 8-aligned: the B statement's premise (lib/B/Prog/rec_calls_free_c.v:100, the UBSan trap
   0x89afc of the asan-ubsan build, recorder.c:142), carried here so that the A and B statements agree (this port's
   decision). rcf_home's afobj branch has it; its two global branches allow any c in the range. Every caller passes an
   aligned table: rec_clear A_G_REC + OFF_CALLS (0x894f0), the inlined record() of the sup_*, pins_*,
   descriptors_* and lv2_refusals_forget functions A_REC_SPILL, check_round_trip its frame object first[] (afobj) *)
c mod 8 = 0 ->
(* each entry: its nargs field, and each argument pointer the start of a live block (plain calls_slots,
   rec_calls_free_c.v:33-42; the recorder never holds a null argument) *)
(forall i P, nth_error ps i = Some P ->
 (length P <= 6)%nat /\
 aval_mem (rdW W mem) (c + CALL_SIZE * Z.of_nat i + CALL_OFF_NARGS) 4 (Z.of_nat (length P)) /\
 forall a pn, nth_error P a = Some pn ->
   aval_mem (rdW W mem) (c + CALL_SIZE * Z.of_nat i + CALL_OFF_ARGS + 8 * Z.of_nat a) 8 (fst pn) /\
   In pn (ablocks B ly S)) ->
(* no block is freed twice (plain rec_calls_free_c.v:74) *)
NoDup (map fst (concat ps)) ->
st_nev S + EV_REC_CALLS_FREE ps <= EV_MAX ->
mo_ok MT S (XM_REC_CALLS_FREE ps) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_rec_calls_free) regs mem md)
(apost_base SEGS B REC_CALLS_FREE_STK (rcf_fp c ps) regs ly S W mem md (EV_REC_CALLS_FREE ps)
(fun ly' S' W' regs' mem' md' =>
 (* every argument block freed, the others live (plain rec_calls_free_c.v:49) *)
 Permutation (ablocks B ly S) (ablocks B ly' S' ++ concat ps) /\
 (* every nargs field 0, every other byte of the table kept (plain :54-58) *)
 (forall i, (i < length ps)%nat -> aval_mem (rdW W' mem') (c + CALL_SIZE * Z.of_nat i + CALL_OFF_NARGS) 4 0) /\
 (forall j, 0 <= j < CALL_SIZE * Z.of_nat (length ps) -> ~ PRcf.nargs_field c (length ps) (c + j) ->
    rdW W' mem' (c + j) = rdW W mem (c + j)) /\
 (* the blocks still live are kept (plain :50) *)
 (forall p n i, In (p, n) (ablocks B ly' S') -> 0 <= i < n -> rdW W' mem' (p + i) = rdW W mem (p + i)) /\
 (* the recorder after the call, for each of the three tables (plain g_rec form :81-114) *)
 (forall R Q, arep_at (ablocks B ly S) (rdW W mem) A_G_REC A_REC_SPILL R Q ->
    c = A_G_REC + OFF_CALLS -> ps = l_calls Q ->
    rec_repA B ly' S' (rdW W' mem') (set_calls R (rcf_cleared (r_calls R)))
      (l_spill Q ++ oblk (l_answer Q) ++ oblk (l_reply Q))) /\
 (forall R Q, arep_at (ablocks B ly S) (rdW W mem) A_G_REC A_REC_SPILL R Q ->
    c = A_REC_SPILL -> ps = [l_spill Q] ->
    rec_repA B ly' S' (rdW W' mem') (set_spill R (fst (r_spill R), []))
      (concat (l_calls Q) ++ oblk (l_answer Q) ++ oblk (l_reply Q))) /\
 (forall R O, rec_repA B ly S (rdW W mem) R O ->
    iv_apart c (CALL_SIZE * Z.of_nat (length ps)) A_G_REC REC_SIZE ->
    iv_apart c (CALL_SIZE * Z.of_nat (length ps)) A_REC_SPILL SC_SIZE ->
    (forall pn, In pn (concat ps) -> ~ In pn O) ->
    rec_repA B ly' S' (rdW W' mem') R O) /\
 blocks_bytes S' <= blocks_bytes S + LIVE_REC_CALLS_FREE /\
 mo_le MT S S' (XM_REC_CALLS_FREE ps))).
End e.
End f.
End d.
