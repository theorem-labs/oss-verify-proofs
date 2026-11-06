(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk context of proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v (c8557374ad2e) for
   libreac/fuzz_scene's walk of LLVMFuzzerTestOneInput, module paths changed. STATEMENTS ONLY (rule 24): no function is
   proved here, and the donor's two short lemmas are stated as Props for the walk to prove. *)

(*   This file names no image value. Every address, offset and frame class is a Section Variable, so the walk of the
   asan build (lib/A/P_LLVMFuzzerTestOneInput.v, which holds the measured numbers) and the asan-ubsan twin (lib/AU)
   instantiate the same names.

   Taken from the donor, by line:
     - rtcx                                  A/ACf5.v:45-48  (record of the entry state)
     - rt_F, rt_FL                           A/ACf5.v:64-65  (frame and flag address of the entry's fake frame)
     - rt_ch                                 A/ACf5.v:128-129
     - rt_ch_spine      -> rt_ch_spine_stmt  A/ACf5.v:130-131
     - rt_ctx_in        -> rt_ctx_in_stmt    A/ACf5.v:132-136
     - rt_trace_in      -> rt_trace_in_stmt  A/ACf5.v:155-165 (statement; a Theorem Labs lane proves it, in
                                             lib/A/P_LLVMFuzzerTestOneInput_trace.v)
     - call_trace0, call_trace_of_spine      lib/YCbq.v:315, :2800, re-exported (Require Export YCbq)
   Changes from the donor:
     - rtcx is over a segment list `segs` (donor: tfibsegs); c_E0 is the walk's position-abstract (PAImg) entry env.
     - rt_F / rt_FL take the frame class `fcid` (donor: a literal class; the instance file fixes the entry's class).
     - the donor's RT_*_ra literals, its two literal allocator return pcs and Tfib_universe are Section
       Variables: RT_malloc{1,2,3}_ra, RT_free{1,2,3}_ra, PC_MALLOC_RA0, PC_FREE_RA0, U. The donor has one malloc and
       four free sites; scene's entry has three of each.
     - rt_trace_in's site disjunction is grouped by allocator: (malloc pc /\ one of three ras) \/ (free pc /\ one of
       three ras). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
(* the meter (ameter_ops, mo_ok, mo_le) *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Export YCbq.
(* the shape (LIBK), the sink names (sink_path) and arodata_okS; a Theorem Labs lane's glue stages YO09 / YE00 / YE01. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YO09 YE00 YE01.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Namei.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
(* The entry state of the walk. c_fpos: the position of the entry's fake frame; c_sp1: the realigned stack pointer
   the function computes in its prologue; c_E0: the symbolic environment at entry; c_T: the meter budget. *)
Record rtcx := mkRTCX {
c_ly : alayout; c_S : astate; c_W : world segs; c_regs : bvmap 5 word; c_mem : word -> option byte; c_md : Model;
c_p : Z; c_n : Z; c_fpos : Z; c_sp1 : Z; c_E0 : env;
c_T : Z     }.
(* The fake-stack class of the entry's frame. *)
Variable fcid : Z.
Definition rt_F (cx : rtcx) : Z := frame_addr (c_ly cx) fcid (c_fpos cx).
Definition rt_FL (cx : rtcx) : Z := flag_addr (c_ly cx) fcid (c_fpos cx).
(* The caller chain at entry: one record, the entry's own (sp, ra, s0), when the entry frame is below the stack top. *)
Definition rt_ch (cx : rtcx) : list (Z * Z * Z) :=
if spZ (c_regs cx) + 16 <? ly_top (c_ly cx) then [(spZ (c_regs cx), raZ (c_regs cx), s0Z (c_regs cx))] else [].
Definition rt_ch_spine_stmt : Prop :=
forall cx, spine (rt_ch cx) = (if spZ (c_regs cx) + 16 <? ly_top (c_ly cx) then [raZ (c_regs cx)] else []).
(* The return address into the caller of the walked function. *)
Variable RA_LLVMF : Z.
Definition rt_ctx_in_stmt : Prop :=
forall cx (site : Z) (L : list (list Z)),
raZ (c_regs cx) = RA_LLVMF -> In [site] L -> In [site; RA_LLVMF] L -> In (site :: spine (rt_ch cx)) L.
(* The allocator's own return pcs (the first entry of every allocation trace), the walked function's six allocator
   call sites (return addresses) and the trace universe. *)
Variables PC_MALLOC_RA0 PC_FREE_RA0 : Z.
Variables RT_malloc1_ra RT_malloc2_ra RT_malloc3_ra RT_free1_ra RT_free2_ra RT_free3_ra : Z.
Variable U : list (list Z).
Definition rt_trace_in_stmt : Prop :=
forall (pcf ra : Z) (regsT : bvmap 5 word) (cx : rtcx),
raZ (c_regs cx) = RA_LLVMF -> raZ regsT = ra ->
((pcf = PC_MALLOC_RA0 /\ (ra = RT_malloc1_ra \/ ra = RT_malloc2_ra \/ ra = RT_malloc3_ra)) \/
(pcf = PC_FREE_RA0 /\ (ra = RT_free1_ra \/ ra = RT_free2_ra \/ ra = RT_free3_ra))) ->
In (call_trace0 pcf regsT (rt_ch cx)) U.
End c.
Arguments c_ly {segs} _. Arguments c_S {segs} _. Arguments c_W {segs} _. Arguments c_regs {segs} _.
Arguments c_mem {segs} _. Arguments c_md {segs} _. Arguments c_p {segs} _. Arguments c_n {segs} _.
Arguments c_fpos {segs} _. Arguments c_sp1 {segs} _. Arguments c_E0 {segs} _. Arguments c_T {segs} _.
Arguments rt_F {segs} fcid cx. Arguments rt_FL {segs} fcid cx. Arguments rt_ch {segs} cx.

(* =================================================================================================================
   SCENE'S OWN ENTRY CONTRACT.  This is cgif_file_fuzzer A/ACfn.v:33-72 (tfib_lib_pre_x / tfib_lib_post_x /
   tfib_lib_contract_x) with the changes a Theorem Labs lane's review required (ENTRY-REVIEW.md, RC1-RC3, 2026-10-28), and with
   every image value a parameter, so lib/A and lib/AU instantiate the same text.  Differences from the donor, line
   by line, for a Theorem Labs lane (its G_Top.v:374 W_LLVMFuzzerTestOneInput concludes this in place of ACfn's
   tfib_lib_contract_x):
     (1) RC1, the sink.  ACfn.v:42 / :55 `asink_none segs tfib_K (rd W mem) md` is replaced by
         `scene_sink_none segs SINK_OWNED (rd W mem) md`.  cgif's record tfib_K (A/AE2k.v:9-52) names
         '/tmp/out.gif' at 0x20e00 and ak_threaded 0x5f9221; fuzz_scene.asan holds "fuzz/fuzz_scene." at 0x20e00
         and ends at 0x5f9000, so with tfib_K the pre is FALSE in every state of the image and the contract is
         vacuous (ENTRY-REVIEW.md item 7a).  Scene's harness opens no file, so the sink is the CLOSED one of the
         unit's own released plain proof, lib/Reusable/YI14.v:112-114 (closed_stdio_env + ofl_head = 0 +
         fd_names_path = false), with its cells as the parameter SINK_OWNED: a list of (address, width) that the
         clause asks to read 0.  For fuzz_scene.asan that list is __libc + 1 (0x5f6a29, 1), ofl_lock (0x5f6e88, 4)
         and ofl_head (0x5f6e90, 8), all MEASURED in the unstripped twin's .symtab.
     (2) RC1, the meta cells.  ACfn.v:43 / :56 `ameta_inv segs tfib_K ly ... M` is gone from the pre and the post,
         and the parameter M with it; the post's journal footprint is [] where cgif's is [sink_token] (ACfn.v:50).
         Scene HAS meta cells, 0xa3040 / 0xa3048: AD2k.v:27-29 finv_check reads them and closes ameta_ok by
         vm_compute.  The entry contract leaves ameta_inv out because the driver regains it after the return by
         framing (Reusable/YE01.v:155-173 ameta_inv_kept).  There is no I/O on this path.
     (3) RC2, A_EMPTY.  cgif fixes `A_EMPTY := 0x5d8660` (ACfn.v:22); in scene that address is builtin_tls+0x1f90,
         so the n = 0 disjunct could never be met.  A_EMPTY is a parameter, the SIXTH of the entry constants
         (order fixed with a Theorem Labs lane, 2026-10-28 22:33Z: A_LLVMF RA_LLVMF EV_LIB LIVE_LIB LLVMF_STK A_EMPTY).
     (4) RC3, the image globals' shadow, in the form a Theorem Labs lane's R2 requires (a Theorem Labs lane's CUTS.md:605-609, measured).
         A per-state `block_shadow` of a global is NOT carried across a runtime call: a global's shadow byte lies
         in the shadow of `lm_zone` (YG0n.v:227, :241), so it is `aowned`, and `astack_malloc_realizes`
         (YG0d.v:298-299) keeps only bytes that are not aowned, while `acall_kept` (YCbq.v:823-834) keeps only
         addresses >= alloc_ceiling, heap blocks, image bytes and frames.  So the walk would LOSE such a clause at
         its first `__asan_stack_malloc_8` call, and a contract that carried it in the pre and gave it back in the
         post could not be proved.  The shadow of reac_ctrl_build_scene_step.TAIL_TRAILER -- which
         build_scene_step's spec needs at both of its accepting call sites -- is therefore a STATIC fact of B
         (`as_zero_shadow` for its full granule, `as_const` for its partial granule and the redzone cells), named
         in the instance file and read at any state through AR's `am_const` / `al_zshadow`.  Neither the pre nor
         the post mentions it, and the cut predicates do not carry it.  Its BYTES are a different matter and need
         no clause either: `arodata_okS` fixes every byte of a non-writable segment to the image's
         (YE01.v:188-191), and the journal keeps image bytes (YCbq.v:360-361).
   The three entry constants A_LLVMF, RA_LLVMF and A_EMPTY, the window RLO / RHI and SINK_OWNED are bound to
   measured values in the instance files, never here.
   ================================================================================================================= *)
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head} {LS : lib_shape}.
(* RC1: the closed sink.  Every range of SINK_OWNED reads 0, and no file descriptor names the sink path.
   `sink_path` is cgif's literal "/tmp/out.gif" (YI16.v:12-13), which scene's released trunk carries unchanged: it
   is inert for scene, which never opens it (the string does not occur in the image), so the clause is true and
   is kept identical to the released plain form lib/Reusable/YI14.v:112-114 (a Theorem Labs lane 23:43Z).  No conjunct names a
   sink string address (path, mode, rwa, trailer): those are the fields knock's deletion removes
   (at 04aa7c1431f). *)
Definition scene_sink_none (segs : list Segment) (SINK_OWNED : list (Z * Z))
(m : word -> option byte) (md : Model) : Prop :=
Forall (fun r => val_mem segs m (fst r) (Z.to_nat (snd r)) 0) SINK_OWNED /\
Namei.fd_names_path (m_fds md) sink_path = false.
(* The pre: ACfn.v:33-46 with (1), (2), (3), (4). *)
Definition scene_tfib_lib_pre_x (segs : list Segment) (SINK_OWNED : list (Z * Z))
(RA_LLVMF EV_LIB LIVE_LIB LLVMF_STK A_EMPTY : Z) (B : asyms) (MT : ameter_ops) (XM_LIB : Z -> Z) (RLO RHI : Z)
(regs : bvmap 5 word) (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (md : Model)
(p n : Z) (pl : list byte) : Prop :=
afn_pre segs B LLVMF_STK ly S W regs mem md [] /\
raZ regs = RA_LLVMF /\
getr regs 10 = w64 p /\ getr regs 11 = w64 n /\
((n = 0 /\ p = A_EMPTY) \/ (0 < n < 2 ^ 26 /\ In (p, n) (ablocks B ly S))) /\
n = Z.of_nat (length pl) /\ garr8 segs (mrestrict (w_H W) mem) p (map (fun b : byte => bv_unsigned b) pl) /\
frames S = [] /\ st_nev S + EV_LIB <= EV_MAX /\ blocks_bytes S + LIVE_LIB <= LIVE_MAX /\
arodata_okS segs B RLO RHI (aview segs (w_H W) mem) /\
scene_sink_none segs SINK_OWNED (mrestrict (w_H W) mem) md /\
fd_lookup (m_fds md) (alloc_fd (m_fds md)) = None /\
Fs.fs_sorted (m_fs md) = true /\
mo_ok MT S (XM_LIB n).
(* The post: ACfn.v:47-58 with (1) and (2). *)
Definition scene_tfib_lib_post_x (segs : list Segment) (SINK_OWNED : list (Z * Z))
(EV_LIB LLVMF_STK : Z) (B : asyms) (MT : ameter_ops) (XN_LIB : Z -> Z)
(regs : bvmap 5 word) (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (md : Model)
(p n : Z) (l : lleaf) (ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word)
(mem' : word -> option byte) (md' : Model) (k : Z) : Prop :=
ajournal segs B LLVMF_STK (spZ regs) [] ly S W mem md [] ly' S' W' mem' md' k /\ k <= EV_LIB /\
aregs_preserved regs regs' /\ getr regs' 10 = w64 0 /\
Permutation (ablocks B ly' S') (ablocks B ly S) /\
(forall fd, fd_lookup (m_fds md') fd = fd_lookup (m_fds md) fd) /\
m_fs md' = ll_fs l /\ ll_ret l = 0 /\ ll_out l = [] /\ Fs.fs_sorted (ll_fs l) = true /\
scene_sink_none segs SINK_OWNED (mrestrict (w_H W') mem') md' /\
mo_le MT S S' (XN_LIB n) /\
(forall i, 0 <= i < n -> aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i)).
(* The contract: ACfn.v:59-69.  Its arguments are, in order, the two scene parameters (segs and the sink's cells),
   then the entry constants A_LLVMF RA_LLVMF EV_LIB LIVE_LIB LLVMF_STK A_EMPTY, then B MT XM_LIB XN_LIB RLO RHI, as
   fixed with a Theorem Labs lane. *)
Definition scene_tfib_lib_contract_x (segs : list Segment) (SINK_OWNED : list (Z * Z))
(A_LLVMF RA_LLVMF EV_LIB LIVE_LIB LLVMF_STK A_EMPTY : Z)
(B : asyms) (MT : ameter_ops) (XM_LIB XN_LIB : Z -> Z) (RLO RHI : Z) : Prop :=
forall ly S (W : world segs) (regs : bvmap 5 word) mem md p n pl (K : lleaf -> TSet),
AI segs (w_H W) (w_A W) md ->
scene_tfib_lib_pre_x segs SINK_OWNED RA_LLVMF EV_LIB LIVE_LIB LLVMF_STK A_EMPTY
B MT XM_LIB RLO RHI regs ly S W mem md p n pl ->
(forall (l : lleaf) (W' : world segs) (c' : config),
wle W W' -> AI segs (w_H W') (w_A W') (cfg_model c') ->
(exists ly' S' regs' mem' md' k,
c' = cfg_at segs RA_LLVMF regs' mem' md' /\
scene_tfib_lib_post_x segs SINK_OWNED EV_LIB LLVMF_STK B MT XN_LIB
regs ly S W mem md p n l ly' S' W' regs' mem' md' k) ->
srealizes segs c' (K l)) ->
srealizes segs (cfg_at segs A_LLVMF regs mem md) (LIBK pl (m_fs md) K).
End s.
Definition scene_tfib_lib_contract_x_all {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}
(segs : list Segment) (SINK_OWNED : list (Z * Z))
(A_LLVMF RA_LLVMF EV_LIB LIVE_LIB LLVMF_STK A_EMPTY : Z)
(B : asyms) (MT : ameter_ops) (XM_LIB XN_LIB : Z -> Z) (RLO RHI : Z) : Prop :=
forall fx : YK11.FPState,
@scene_tfib_lib_contract_x fx rc SK LS segs SINK_OWNED
A_LLVMF RA_LLVMF EV_LIB LIVE_LIB LLVMF_STK A_EMPTY B MT XM_LIB XN_LIB RLO RHI.
