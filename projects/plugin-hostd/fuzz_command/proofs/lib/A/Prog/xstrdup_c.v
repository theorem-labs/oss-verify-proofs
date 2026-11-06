(* The contract of xstrdup on the ASan build of plugin-hostd/fuzz_command.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return; the fresh block as cgif's trawnew_specX states it (lib/YC7x.v:93-101), the meter
   as there (:88, :92). Functional content: fuzz_command's own released plain contract lib/Prog/xstrdup_c.v:24-52
   (a fresh block of |x| + 1 bytes that holds x and its terminator; the source string kept).
   The function (H/recorder.c:97-102, xmalloc inlined) asks the strlen wrapper (`___interceptor_strlen`, reached
   through the 4-byte jump `__interceptor_trampoline_strlen`) for |s|, allocates |s| + 1 bytes through the malloc
   wrapper, and copies |s| + 1 bytes with `__asan_memcpy`. The malloc rule returns a block at or above 4096, so the
   abort edge (`__asan_handle_no_return`, then abort) on a null result is not taken. It has no inline check: the
   wrapper and `__asan_memcpy` check the shadow of the ranges they touch, and the source premise below makes those
   bytes usable: a live block (AR's block facts, as PaArt's aread_ok_of_block states them), a read-only byte range
   of the image (astr_argA's read-only branch, which carries range_addressable and shadow_hull_vis; in_img,
   amem_range and 0 < s from `cmd_ro_rd`), or an object of a side-stack frame (afobj). The source is read twice,
   by the strlen wrapper and by `__asan_memcpy`
   after the malloc wrapper ran: a read-only source keeps its bytes across the malloc by the journal's image clause
   (ajournal's kept-bytes clause for image bytes outside as_owned_static and the errno cell, lib/Reusable/YCbq.v:398),
   which astr_argA's narrowed read-only branch states per byte; a caller passing an image literal discharges that
   branch by cmd_img_facts' `cif_ro_unowned`. s is in s0 at the three runtime calls; it lies below the stack (heap,
   image or side stack), so the malloc wrapper's chain_pre holds with the empty chain (no achain premise).

   Addresses: entry BASE + AF_xstrdup = 0x89904 (M, the pinned image). 25 instructions, 0 inline checks, no loop,
   no side-stack frame; callees: the strlen wrapper, the malloc wrapper, __asan_memcpy (0x57630). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
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
(* the stack this call needs: its own 32-byte frame, and the window the malloc wrapper asks for (ASTACK, cgif
   lib/YG0d.v:17; amalloc04_rule asks ASTACK - o <= STK, lib/YC5d.v:60). The strlen wrapper's window and
   __asan_memcpy's (ESTACK each, the runtime contracts' final windows) are smaller. *)
Definition XSTRDUP_STK : Z := 32 + ASTACK.
(* one allocator event: the malloc *)
Definition EV_XSTRDUP : Z := 1.
(* the live bytes the call adds: the copy *)
Definition LIVE_XSTRDUP (x : list byte) : Z := Z.of_nat (length x) + 1.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the meter the call spends: one malloc of |x| + 1 bytes *)
Definition XM_XSTRDUP (x : list byte) : Z := mo_malloc MT (Z.of_nat (length x) + 1).
(* the runtime entries the call reaches, with this tree's and cgif's names *)
Hypothesis AMALLOC4 : forall fx0 : YK11.FPState, @amalloc04_rule fx0 rc SK SEGS B MT.
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIG CS___asan_memcpy).
Hypothesis ASTRLEN : forall fx0 : YK11.FPState, @astrlen_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strlen).
Definition txstrdup_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (s : Z) (x : list byte),
afn_pre SEGS B XSTRDUP_STK ly S W regs mem md ch ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
getr regs 10 = w64 s ->
(* the string the caller hands over, of at most LMAX bytes (plain xstrdup_c.v:45-46): in a live block or in the
   read-only image (astr_argA; the image literals "(null)" and "-" of arg_s and sup_add's defaults keep the
   read-only branch), or in an object of a live side-stack frame (arg_i's, answer's and sup_resp's snprintf
   buffers) *)
(astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) [] s (Some x) \/
 (astr_atR (rdW W mem) s x /\ Z.of_nat (length x) + 1 <= LMAX + 1 /\
  afobj SEGS B ly S W mem s (Z.of_nat (length x) + 1))) ->
(* the bytes after the terminator up to the end of its 8-byte word are readable: the strlen wrapper's musl loop reads
   whole words (the runtime contracts' atail_vis, RtString.v:80; the plain contract's slack, plain xstrdup_c.v:45,47).
   A caller gets it by `cmd_heap_tail_vis` for a heap string, from the frame for a side-stack buffer, and by
   `cmd_tail_vis` for an image literal (`cmd_ro_rd` for a generic read-only string) *)
atail_vis SEGS W mem (s + Z.of_nat (length x)) ->
st_nev S + EV_XSTRDUP <= EV_MAX -> blocks_bytes S + LIVE_XSTRDUP x <= LIVE_MAX ->
mo_ok MT S (XM_XSTRDUP x) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_xstrdup) regs mem md)
(apost_base SEGS B XSTRDUP_STK [] regs ly S W mem md EV_XSTRDUP
(fun ly' S' W' regs' mem' md' => exists p : Z,
 getr regs' 10 = w64 p /\ 4096 <= p < 2 ^ 64 /\
 (* a fresh block, apart from every block that was live (plain xstrdup_c.v:30-31) *)
 Permutation (ablocks B ly' S') ((p, LIVE_XSTRDUP x) :: ablocks B ly S) /\
 Forall (fun qk => iv_apart p (LIVE_XSTRDUP x) (fst qk) (snd qk)) (ablocks B ly S) /\
 (* it holds the copy, in the block form its callers' callees ask (in_blockA + astr_atR), and the source is
    kept (plain xstrdup_c.v:34-35) *)
 in_blockA (ablocks B ly' S') p (LIVE_XSTRDUP x) /\
 astr_atR (rdW W' mem') p x /\ astr_atR (rdW W' mem') s x /\
 blocks_bytes S' <= blocks_bytes S + LIVE_XSTRDUP x /\
 mo_le MT S S' (XM_XSTRDUP x))).
End e.
End f.
End d.
