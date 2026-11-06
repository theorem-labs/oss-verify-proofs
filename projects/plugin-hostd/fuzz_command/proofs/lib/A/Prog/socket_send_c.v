(* The contract of socket_send on the ASan build of plugin-hostd/fuzz_command.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return. Functional content: fuzz_command's own released plain contract
   lib/Prog/socket_send_c.v:27-65 (the recorder after the call is `fst (socket_send_m R x)`, a0 = size, the old
   reply freed, a fresh block of `size` bytes owned by the recorder when size > 0) and the model
   lib/Prog/RecModel.v:54-55, :84-85 (`rec_socket_send`, `socket_send_m`).
   The function counts the reply (g_rec.nreplies + 1), frees the previous reply text (NULL or a block the recorder
   owns), zeroes reply and reply_size (one 16-byte call of the memory-checking runtime's memset entry) and, when
   size > 0, allocates `size` bytes through the malloc wrapper, copies the buffer into them (the runtime's memcpy
   entry) and stores the pointer and the size. The abort after a NULL malloc result is not reached: the
   live-bytes premise and size <= LMAX + 2 < MALLOC_MAX make the malloc wrapper return a block (cgif's
   amalloc04_rule, lib/YC5d.v:56-74). The buffer is apart from every recorder block, so the free of the old reply
   does not touch it.

   Addresses: entry BASE + AF_socket_send = 0x8d3e4 (M, the pinned image). 39 instructions, no inline check (g_rec
   at constant offsets, reached by auipc), no loop, no side-stack frame. Calls: the free wrapper (0x58980), the
   memset entry (0x57acc), the malloc wrapper (0x58984), the memcpy entry (0x57630); the error path abort
   (before_abort 0x5f744, abort 0x9504c) is not reached. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep CmdObj.
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
(* the stack this call needs: its own 48-byte frame, and the window the malloc and free wrappers ask for (cgif's
   amalloc04_rule / afree04_rule, ASTACK, lib/YG0d.v:17); the memset and memcpy entries ask for ESTACK only *)
Definition SOCKET_SEND_STK : Z := 48 + ASTACK.
(* free(g_rec.reply) (an event also when the reply is NULL, cgif's afree_null04_rule) and malloc(size) *)
Definition EV_SOCKET_SEND : Z := 2.
(* the reply copy, at most LMAX + 2 bytes (the plain premise, socket_send_c.v:33) *)
Definition LIVE_SOCKET_SEND : Z := LMAX + 2.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Definition XM_SOCKET_SEND (size : Z) : Z := mo_free MT + (if 0 <? size then mo_malloc MT size else 0).
(* the runtime entries this call reaches *)
Hypothesis AMALLOC4 : forall fx0 : YK11.FPState, @amalloc04_rule fx0 rc SK SEGS B MT.
Hypothesis AFREE4 : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT.
Hypothesis AFREE_NULL4 : forall fx0 : YK11.FPState, @afree_null04_rule fx0 rc SK SEGS B MT.
Hypothesis AMEMSET : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OSet (SIG CS___asan_memset).
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIG CS___asan_memcpy).
Hypothesis VOBJS : cmd_val_objs.
Definition tsocket_send_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (buf size : Z) (x : list byte) (R : rstate) (O : list (Z * Z)),
afn_pre SEGS B SOCKET_SEND_STK ly S W regs mem md ch ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
(* a0 (the destination) is not read; a1 = the buffer, a2 = its size as a 32-bit int *)
getr regs 11 = w64 buf -> 0 <= buf < 2 ^ 64 -> getr regs 12 = w64 size -> -2 ^ 31 <= size < 2 ^ 31 ->
rec_repA B ly S (rdW W mem) R O -> r_nreplies R < 2 ^ 31 - 1 ->
(* the bytes the call copies: inside a live block that none of the recorder's blocks overlaps *)
(0 < size ->
 size <= LMAX + 2 /\ Z.of_nat (length x) = size /\ abytes_atR (rdW W mem) buf x /\
 in_blockA (ablocks B ly S) buf size /\ Forall (fun qk => iv_apart buf size (fst qk) (snd qk)) O) ->
(size <= 0 -> x = []) ->
st_nev S + EV_SOCKET_SEND <= EV_MAX -> blocks_bytes S + LIVE_SOCKET_SEND <= LIVE_MAX ->
mo_ok MT S (XM_SOCKET_SEND size) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_socket_send) regs mem md)
(apost_base SEGS B SOCKET_SEND_STK ((A_G_REC, A_G_REC + REC_SIZE) :: ablocks_fp O) regs ly S W mem md
EV_SOCKET_SEND
(fun ly' S' W' regs' mem' md' => exists O' : list (Z * Z),
getr regs' 10 = w64 size /\
rec_repA B ly' S' (rdW W' mem') (fst (socket_send_m R x)) O' /\
(* the recorder's new blocks are fresh; every other block is kept *)
(forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
(forall pn, In pn (ablocks B ly' S') -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O') /\
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly' S')) /\
blocks_bytes S' <= blocks_bytes S + LIVE_SOCKET_SEND /\
mo_le MT S S' (XM_SOCKET_SEND size))).
End e.
End f.
End d.
