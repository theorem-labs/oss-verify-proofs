(* crtA_cuts: the cut points of the cgif-form walk of check_round_trip (image A), as Props, so that the walk can
   be proved in four independent pieces that fit together without being re-stated.

   The walk runs backwards, in cgif's own style (origin/ossv/recipes proofs/cgif/cgif_file_fuzzer/lib/A/ACey.v:270
   RFC_I_stmt .. :317 RFC_C1_stmt, composed in ACet.v:36-43): the piece that starts at a cut point takes the next
   cut point's Prop as a hypothesis, and every piece ends in the SAME post, the statement's dec_crt_post.
   crtA_pre carries, besides the contract's premises, the trace facts the cuts cannot name CTX for: the first
   malloc's (dec_crt_uctx's first conjunct), the tail free's (its second), and dec_crt_ufix.
   No cut states the value of ra: x1 is not callee-saved, so no call rule gives it back (YC5d.v:71-75 and
   YGCalloc.v:243-250 give aregs_preserved, whose acallee_saved list (YG0d.v:20) has no x1, plus a0), and no
   code after a cut reads ra before a jal rewrites it (crt_seg4_F passes it through, crt_seg5_F's jal sets it,
   the epilogue reloads it from the frame).  Found by the entry piece's lane, 2026-10-29 03:4xZ.

   The cut points (lib/A/Prog/crtA_iface.v):
     CRT_ENTRY            the entry; the piece to CRT_RET_CALLOC runs the prologue and the three allocator calls
     CRT_RET_CALLOC       after calloc: crtA_at_calloc  (the piece to CRT_LOOP_OUT runs the null checks and the
                          convert loop)
     CRT_LOOP_OUT         after the loop: crtA_at_loopout (the piece to CRT_RET_BCMP runs the encode and bcmp calls)
     CRT_RET_BCMP         after bcmp: crtA_at_bcmp (the piece to the end runs the two frees, the epilogue and the
                          tail free, and lands in dec_crt_post)

   What every piece may assume about the state at its cut point: the walk's three temporaries are
     P = planes  (malloc 4 nch ns),  Q = planar (malloc 8 nch),  R = again (calloc 3 nch ns)
   and the register names are the function's: s0 = P, s1 = audio, s2 = ns, s3 = nch, s4 = 3 nch ns, s5 = Q,
   s6 = pcm, s7 = nch ns (until the calloc returns, then R), s8 = the shadow offset ASAN_K. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG01 YG0f YG0n YG0d YCbq YC5d YGCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YI16.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import Img0 AsanCells DecodeTFIB DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import DecodeSyms DecodeAddr DecodeList.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import crtA_iface check_round_trip_cg.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog Require FloatExact.
Import ListNotations.
Open Scope Z_scope.
Module YKK := OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YK11.
Module DFE := OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog.FloatExact.

(* The pcm sample values the convert loop reads, read at the entry state (pcm lies in a caller block, which the walk
   never writes), and the float each becomes: s24 of three little-endian bytes (`lbu`, `lbu`, `lb`, combined at
   +0x168 .. +0x188), converted (`fcvt.s.w` at +0x18c) and scaled by fa5 = F2M23 = 2^-23 (`fmul.s` at +0x190).
   Same shape as image B's crtB_pb / crtB_s24 / crtB_cv (a working branch 8d59e829a9a,
   lib/B/Prog/crtB_cuts.v). *)
Definition crtA_pb (rd : reader) (pcm i : Z) : Z := match rd (pcm + i) with Some v => v | None => 0 end.
Definition crtA_s24 (b0 b1 b2 : Z) : Z := b0 + 256 * b1 + 65536 * b2 - (if 128 <=? b2 then 16777216 else 0).
Definition crtA_cv (rd : reader) (pcm j : Z) : Z :=
  DFE.f32 (crtA_s24 (crtA_pb rd pcm (3 * j)) (crtA_pb rd pcm (3 * j + 1)) (crtA_pb rd pcm (3 * j + 2))) (-23).

(* What the convert loop leaves in its two blocks: planar[c] = planes + 4 c ns (8 bytes at Q + 8 c, the `sd` at
   +0xf8) for c < nch, and planes[k] = the float of pcm sample k (4 bytes at P + 4 k, the `fsw` at +0x194) for
   k < nch ns.  rd is the reader at the entry state.  Same shape as image B's crtB_conv. *)
Definition crtA_conv (rd : reader) (pcm nch ns P Q : Z) (mem : word -> option byte) : Prop :=
  (forall c, 0 <= c < nch -> bytes_at rsegs mem (Q + 8 * c) (le8 (Z_to_bv 64 (P + 4 * (c * ns))))) /\
  (forall k, 0 <= k < nch * ns -> bytes_at rsegs mem (P + 4 * k) (Z_to_le_bytes 4 (crtA_cv rd pcm k))).

Section CrtCuts.
Context {fx : YKK.FPState} {rc : YM05.RunCeil}.
Local Notation sink := dec_A_sink_head.
Local Notation segs := decodesegs0.
Variable B : asyms.
Variable MT : ameter_ops.

(* The read-only bytes the walk's callees read: the leaf's read-only read set RO_RD, a list of (base, size).
   The frozen statement adds, besides cgif's `rom_view` at the entry (YG0d.v:382), a SCOPED instance fact over
   exactly this set (the porter's ruling, 2026-10-29 03:36Z): those bytes are in no owned static zone and are not
   errno.  It is deliberately not a global "owned statics are off ROM", which is FALSE for decode, because a
   read-only ASan global redzone IS an owned static in .rodata.  The lane carries rom_view RESTRICTED to RO_RD
   (crtA_rom_on) and proves it at each cut from those two premises and the journal's image clause
   (YCbq.v:362). *)
Variable RO_RD : list (Z * Z).
Definition crtA_in_ro_rd (a : Z) : Prop := exists r, In r RO_RD /\ fst r <= a < fst r + snd r.
Definition crtA_rom_on (W : world segs) (mem : word -> option byte) : Prop :=
  forall a, crtA_in_ro_rd a -> in_rom segs a ->
    aview segs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)).
Definition crtA_ro_scoped : Prop :=
  forall a, crtA_in_ro_rd a ->
    ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Local Notation ajournalA := (@ajournal rc sink segs B).

(* The entry data of one call of check_round_trip: what the contract's premises fix. *)
Definition crtA_pre (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model) (k : Z)
    (regs : bvmap 5 word) (audio pcm nch ns bA nA bP nP T : Z) (ch : list (Z * Z * Z)) : Prop :=
  ajournalA STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\
  YK0s.ret_ok (YKK.getr regs 1) /\ 4096 <= raZ regs /\
  YKK.getr regs 3 = w64 (as_gp B) /\ YKK.getr regs 4 = w64 (as_tp B) /\
  YKK.getr regs 10 = w64 audio /\ YKK.getr regs 11 = w64 pcm /\
  YKK.getr regs 12 = w64 nch /\ YKK.getr regs 13 = w64 ns /\
  @achain rc lyc (aview segs (w_H W) memc) (spZ regs) (s0Z regs) ch /\
  spZ regs mod 16 = 0 /\ sp0 - STK <= spZ regs - DEC_CRT_STK /\ spZ regs <= sp0 /\
  Z.even nch = true /\ 2 <= nch <= 127 /\ 1 <= ns <= 12 /\ 3 * nch * ns <= 1440 /\
  In (bA, nA) (ablocks B lyc Sc) /\ bA <= audio /\ audio + 3 * nch * ns <= bA + nA /\
  In (bP, nP) (ablocks B lyc Sc) /\ bP <= pcm /\ pcm + 3 * nch * ns <= bP + nP /\
  dec_crt_braid (aview segs (w_H W) memc) audio pcm nch ns /\
  st_nev S + k + DEC_CRT_EV <= EV_MAX /\ blocks_bytes Sc + DEC_CRT_LIVE <= LIVE_MAX /\
  mo_ok MT Sc T /\ dec_crt_cost MT nch ns <= T /\
  In (dec_utrace (pc_malloc_ra0 (as_code B)) (DEC_CRT_RA_MALLOC1 :: spine ch)) (as_universe B) /\
  In (dec_utrace (pc_free_ra0 (as_code B)) (raZ regs :: spine ch)) (as_universe B) /\
  dec_crt_ufix B /\
  crtA_rom_on W memc /\
  crtA_ro_scoped.

(* The registers the function keeps live from its prologue to its epilogue, at a state whose frame is at
   spZ regs - CRT_FRAME: sp, gp, tp, s0 = P, s1 = audio, s2 = ns, s3 = nch, s4 = 3 nch ns, s5 = Q, s7 = sv7
   (nch ns until the calloc returns, R from +0x90 on), s8 = the shadow offset, s11 untouched.  s6, s9 and s10
   are NOT kept: the convert loop uses them (s6 walks pcm, s9 / s10 are scratch); the frame holds the caller's
   values and the epilogue reloads them.  ra and a0 are stated per cut. *)
Definition crtA_regs (regs regs1 : bvmap 5 word) (P Q sv7 audio nch ns : Z) : Prop :=
  YKK.getr regs1 2 = w64 (spZ regs - CRT_FRAME) /\
  YKK.getr regs1 3 = YKK.getr regs 3 /\ YKK.getr regs1 4 = YKK.getr regs 4 /\
  YKK.getr regs1 8 = w64 P /\ YKK.getr regs1 9 = w64 audio /\
  YKK.getr regs1 18 = w64 ns /\ YKK.getr regs1 19 = w64 nch /\ YKK.getr regs1 20 = w64 (3 * (nch * ns)) /\
  YKK.getr regs1 21 = w64 Q /\ YKK.getr regs1 23 = w64 sv7 /\
  YKK.getr regs1 24 = w64 ASAN_K /\
  YKK.getr regs1 27 = YKK.getr regs 27.

(* Before the convert loop: s6 still holds pcm and s9, s10 still hold the caller's values. *)
Definition crtA_regs_preloop (regs regs1 : bvmap 5 word) (pcm : Z) : Prop :=
  YKK.getr regs1 22 = w64 pcm /\ YKK.getr regs1 25 = YKK.getr regs 25 /\ YKK.getr regs1 26 = YKK.getr regs 26.

(* The frame the prologue wrote: the twelve callee-saved words of the caller, at [sp - 96, sp). *)
Definition crtA_frame (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  rw_cells rsegs mem (spZ regs - CRT_FRAME)
    (crt_fr (YKK.getr regs 26) (YKK.getr regs 25) (YKK.getr regs 24) (YKK.getr regs 23) (YKK.getr regs 22)
            (YKK.getr regs 21) (YKK.getr regs 20) (YKK.getr regs 19) (YKK.getr regs 18) (YKK.getr regs 9)
            (YKK.getr regs 8) (YKK.getr regs 1)).

(* What the state at a cut shares with the entry, in cgif's form: an INNER journal started at the entry state
   (stack window [spZ regs - DEC_CRT_STK, spZ regs), no footprint, no frame of its own; YCbq.v:1827
   ajournal_sub_init starts it, YCbq.v:725 ajournal_sub composes it with the caller's journal at the end, and
   YCbq.v:973 acall_kept_of_journal reads the post's acall_kept off it), `k1` allocator events so far, the frames
   of the caller, the meter charged `acc`, and the frame the prologue wrote. *)
Definition crtA_mid (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model)
    (regs : bvmap 5 word)
    (ly1 : alayout) (S1 : astate) (W1 : world segs) (mem1 : word -> option byte) (md1 : Model)
    (k1 acc : Z) : Prop :=
  ajournalA DEC_CRT_STK (spZ regs) [] lyc Sc W memc mdc [] ly1 S1 W1 mem1 md1 k1 /\
  frames S1 = frames Sc /\
  mo_le MT Sc S1 acc /\
  crtA_frame regs mem1 /\
  crtA_rom_on W1 mem1.

(* The meter charged by the three allocations. *)
Definition crtA_acc3 (nch ns : Z) : Z :=
  mo_malloc MT (4 * (nch * ns)) + mo_malloc MT (8 * nch) + mo_malloc MT (3 * (nch * ns)).

(* The three temporaries are the only blocks the call has added. *)
Definition crtA_blocks3 (lyc : alayout) (Sc : astate) (ly1 : alayout) (S1 : astate) (P Q R nch ns : Z) : Prop :=
  Permutation (ablocks B ly1 S1)
    ((R, 3 * (nch * ns)) :: (Q, 8 * nch) :: (P, 4 * (nch * ns)) :: ablocks B lyc Sc) /\
  0 < P /\ 0 < Q /\ 0 < R.

(* ---- cut 1: after the calloc, at CRT_RET_CALLOC -------------------------------------------------------- *)
(* a0 = R (the calloc's block), s7 still nch * ns, s6 / s9 / s10 not yet touched.  The float state is still the
   entry's: no float instruction runs before +0xc4, and the three allocator rules state their pre and post at the
   same {fx} (YC5d.v:57-75, YGCalloc.v:230-250).  The rounding mode is carried because the convert loop needs it
   (crtA_loop.v crt_loop_stmt_F takes frm0, lib/Lib/FP.v:64, which is frm_zero's body, YK0o.v:13). *)
Definition crtA_at_calloc : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs audio pcm nch ns bA nA bP nP T ch
         ly1 S1 W1 mem1 md1 regs1 P Q R,
    crtA_pre STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs audio pcm nch ns bA nA bP nP T ch ->
    crtA_mid lyc Sc W memc mdc regs ly1 S1 W1 mem1 md1 3 (crtA_acc3 nch ns) ->
    crtA_regs regs regs1 P Q (nch * ns) audio nch ns -> crtA_regs_preloop regs regs1 pcm ->
    YKK.getr regs1 10 = w64 R ->
    frm_zero (@fp_csr fx) ->
    crtA_blocks3 lyc Sc ly1 S1 P Q R nch ns ->
    SRr segs W1 (@cfg_at fx segs CRT_RET_CALLOC regs1 mem1 md1)
      (dec_crt_post B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs nch ns).

(* ---- cut 2: after the convert loop, at CRT_LOOP_OUT ----------------------------------------------------- *)
(* The loop has written the P and Q blocks as crtA_conv says; s7 = R; ra is still CRT_RET_CALLOC; the float state
   has moved (fx1) with the rounding mode still zero. *)
Definition crtA_at_loopout : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs audio pcm nch ns bA nA bP nP T ch
         ly1 S1 W1 mem1 md1 regs1 P Q R (fx1 : YKK.FPState),
    crtA_pre STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs audio pcm nch ns bA nA bP nP T ch ->
    crtA_mid lyc Sc W memc mdc regs ly1 S1 W1 mem1 md1 3 (crtA_acc3 nch ns) ->
    crtA_regs regs regs1 P Q R audio nch ns ->
    crtA_blocks3 lyc Sc ly1 S1 P Q R nch ns ->
    frm_zero (@fp_csr fx1) ->
    crtA_conv (aview segs (w_H W) memc) pcm nch ns P Q mem1 ->
    SRr segs W1 (@cfg_at fx1 segs CRT_LOOP_OUT regs1 mem1 md1)
      (dec_crt_post B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs nch ns).

(* ---- cut 3: after bcmp, at CRT_RET_BCMP ----------------------------------------------------------------- *)
(* bcmp has answered 0 (the braid of the encoded rows is the caller's audio), so the branch to the abort block is
   refuted by the next segment; what is left is free(R), free(Q), the epilogue and the tail jump to free(P). *)
Definition crtA_at_bcmp : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs audio pcm nch ns bA nA bP nP T ch
         ly1 S1 W1 mem1 md1 regs1 P Q R (fx1 : YKK.FPState),
    crtA_pre STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs audio pcm nch ns bA nA bP nP T ch ->
    crtA_mid lyc Sc W memc mdc regs ly1 S1 W1 mem1 md1 3 (crtA_acc3 nch ns) ->
    crtA_regs regs regs1 P Q R audio nch ns ->
    YKK.getr regs1 10 = w64 0 ->
    crtA_blocks3 lyc Sc ly1 S1 P Q R nch ns ->
    frm_zero (@fp_csr fx1) ->
    SRr segs W1 (@cfg_at fx1 segs CRT_RET_BCMP regs1 mem1 md1)
      (dec_crt_post B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs nch ns).
End CrtCuts.
