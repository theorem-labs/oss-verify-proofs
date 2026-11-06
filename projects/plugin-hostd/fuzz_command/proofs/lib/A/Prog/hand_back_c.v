(* The contract of hand_back on the ASan build of plugin-hostd/fuzz_command.
   The callees' contracts are taken at every FP state (forall fx0), so a walk can use them at the fx' a call returns.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return; the fresh blocks as cgif's trawnew_specX states one (lib/YC7x.v:93-101), the
   meter as there (:88, :92). Functional content: fuzz_command's own released plain contract
   lib/Prog/hand_back_c.v:25-75 (hand_back_ret :25-58, the contract :60-75) and the model lib/Prog/RecModel.v:45
   (`hand_back R t = (set_answer R (Some t), t)`).
   hand_back(text) (recorder.c:243-248) frees the answer the recorder kept (g_rec.answer, g_rec + 912; free(NULL)
   when there is none), stores a fresh copy of text there (xstrdup), and returns a second fresh copy (a tail call
   `j xstrdup`). Its callers (answer, sup_add, answer_code) hand it a buffer of their own side-stack frame.

   Addresses: entry BASE + AF_hand_back = 0x8a478 (M, the pinned image). 18 instructions, no inline check, no loop,
   no side-stack frame; callees: the free wrapper (`__interceptor_trampoline_free`), xstrdup (a call and a tail
   call). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdObj.
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
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the stack this call needs: its own 32-byte frame, and the deeper of the free wrapper's window (ASTACK, cgif
   lib/YG0d.v:17, afree04_rule) and xstrdup's own need; the tail call runs xstrdup at the entry sp, which this
   bound covers *)
Definition HAND_BACK_STK : Z := 32 + Z.max ASTACK XSTRDUP_STK.
(* one free and the two mallocs of the two copies *)
Definition EV_HAND_BACK : Z := 1 + EV_XSTRDUP + EV_XSTRDUP.
(* the live bytes the call adds: the two copies of x *)
Definition LIVE_HAND_BACK (x : list byte) : Z := LIVE_XSTRDUP x + LIVE_XSTRDUP x.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the meter the call spends: the free of the old answer (also when it is NULL, afree_null04_rule) and the two
   copies *)
Definition XM_HAND_BACK (x : list byte) : Z := mo_free MT + XM_XSTRDUP MT x + XM_XSTRDUP MT x.
(* the callee's contract, the runtime entries with cgif's names, and the bridge for g_rec's address *)
Hypothesis TXSTRDUP : forall fx0 : YK11.FPState, @txstrdup_spec fx0 rc SK PI B MT.
Hypothesis AFREE4 : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT.
Hypothesis AFREE_NULL4 : forall fx0 : YK11.FPState, @afree_null04_rule fx0 rc SK SEGS B MT.
Hypothesis VOBJS : cmd_val_objs.
Definition thand_back_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (s old : Z) (x : list byte) (R : rstate) (O : list (Z * Z)),
afn_pre SEGS B HAND_BACK_STK ly S W regs mem md ch ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
getr regs 10 = w64 s -> 0 <= s < 2 ^ 64 ->
(* the text: a string of at most LMAX bytes in an object of a live side-stack frame (the caller's buffer), whose
   bytes are marked usable, so the strlen wrapper and __asan_memcpy inside xstrdup pass their checks *)
astr_atR (rdW W mem) s x -> Z.of_nat (length x) <= LMAX ->
afobj SEGS B ly S W mem s (Z.of_nat (length x) + 1) ->
(* the recorder's state; old is the answer it holds (0 or the start of one of its blocks O), an 8-byte field read
   as a 64-bit value *)
rec_repA B ly S (rdW W mem) R O ->
aval_mem (rdW W mem) (A_G_REC + OFF_ANSWER) 8 old -> 0 <= old < 2 ^ 64 ->
st_nev S + EV_HAND_BACK <= EV_MAX -> blocks_bytes S + LIVE_HAND_BACK x <= LIVE_MAX ->
mo_ok MT S (XM_HAND_BACK x) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_hand_back) regs mem md)
(apost_base SEGS B HAND_BACK_STK
 ((A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8) :: ablocks_fp (filter (fun pn => fst pn =? old) O))
 regs ly S W mem md EV_HAND_BACK
(fun ly' S' W' regs' mem' md' => exists p1 p2 O',
 let n := Z.of_nat (length x) + 1 in
 getr regs' 10 = w64 p2 /\ 4096 <= p2 < 2 ^ 64 /\ p1 <> p2 /\
 (* two fresh blocks of |x| + 1 bytes: no block live at the entry other than the freed old answer is one of them
    (plain hand_back_c.v:43; xstrdup's malloc may return old's address after free(old)); the old answer's block is
    gone, every other block stays *)
 (forall pn, In pn (ablocks B ly S) -> fst pn <> old -> pn <> (p1, n) /\ pn <> (p2, n)) /\
 (forall pn, In pn (ablocks B ly' S') <->
   (In pn (ablocks B ly S) /\ fst pn <> old) \/ pn = (p1, n) \/ pn = (p2, n)) /\
 (* the recorder now holds the answer x in p1 (plain hand_back_c.v:46-47) *)
 rec_repA B ly' S' (rdW W' mem') (fst (hand_back R x)) O' /\
 (forall pn, In pn O' <-> (In pn O /\ fst pn <> old) \/ pn = (p1, n)) /\
 (* the caller gets the other copy (plain hand_back_c.v:52) *)
 astr_atR (rdW W' mem') p2 (snd (hand_back R x)) /\
 blocks_bytes S' <= blocks_bytes S + LIVE_HAND_BACK x /\
 mo_le MT S S' (XM_HAND_BACK x))).
End e.
End f.
End d.
