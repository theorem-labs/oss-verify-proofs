(* crtB_cuts: the cut points of the cgif-form walk of check_round_trip (image B), as Props, so that the walk is
   proved in five independent pieces that fit together without being re-stated.  Twin of lib/A/Prog/crtA_cuts.v
   (a working branch ae1529ccb00): the same names and the same backward-chain form, image
   B's registers, frame and offsets.

   The walk runs backwards, in cgif's own style (origin/ossv/recipes proofs/cgif/cgif_file_fuzzer/lib/A/ACey.v:270
   RFC_I_stmt .. :317 RFC_C1_stmt, composed in ACet.v:36-43): the piece that starts at a cut point takes the next
   cut point's Prop as a hypothesis, and every piece ends in the SAME post, the statement's dec_crt_post.

   The cut points (lib/B/Prog/crtB_iface.v) and the pieces between them (the stage statements at the end):
     CRT_ENTRY        crtB_entry_stmt: the prologue and the three allocator calls, to crtB_at_calloc
     CRT_RET_CALLOC   crtB_at_calloc;   crtB_setup_stmt: the NULL checks and the loop constants, to crtB_at_loopin
     CRT_LOOP_IN      crtB_at_loopin (image B only: the loop lane starts here);
                      crtB_loop_stmt: the outer and inner loops, to crtB_at_loopout
     CRT_LOOP_OUT     crtB_at_loopout;  crtB_encbcmp_stmt: the encode and bcmp calls, to crtB_at_bcmp
     CRT_RET_BCMP     crtB_at_bcmp;     crtB_tail_stmt: the bcmp test, free(R), free(Q), the epilogue and the tail
                      free(P), to dec_crt_post
   dec_check_round_trip_cg_holds_of_cuts composes the five into dec_check_round_trip_cg_holds_stmt.

   What every piece may assume about the state at its cut point: the walk's three temporaries are
     P = planes  (malloc 4 nch ns),  Q = planar (malloc 8 nch),  R = again (calloc 3 nch ns)
   and image B keeps them so: s5 = Q, s2 = ns, s8 = the shadow offset ASAN_K in registers from +0x7c to the end;
   P at 48(sp), nch at 40(sp), 3 nch ns at 16(sp), audio at 24(sp), R at 8(sp) (from +0xa8), ~P at 32(sp) (from
   +0xc4); after the loop s0 = R (`ld s0,8(sp)` at +0x26c).

   Differences from the crtA twin, each needed by image B:
   - crtB_frame carries the six slot words of image B's frame (image A keeps P, Q, R, nch, ns in registers);
     crtB_mid therefore leaves the frame out and every cut states it.  crtB_mid is crtA_mid's inner journal.
   - crtB_pre adds the trace of the tail free (`j wrapper_free` at +0x2e8): the epilogue has restored ra and s0,
     so free's call_trace0 is dec_utrace pc_free_ra0 (raZ :: spine ch) (check_round_trip_cg.v:200-201), which the
     caller's dec_crt_uctx CTX gives for the entry context; the cut after bcmp cannot name CTX, so the entry piece
     passes the fact on.
   - crtB_at_loopout states the loop's output as crtB_conv (planar rows and planes floats): it names P, Q, nch, ns
     and pcm, which the cut binds, so it is not a parameter of the cut. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG01 YG0f YG0n YG0d YCbq YC5d YGCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import DecodeCallocKit.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import DecodeBSyms DecodeBAddr DecodeBList.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require reac_braid_encode_cg.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import crtB_iface check_round_trip_cg.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog Require FloatExact.
Import ListNotations.
Open Scope Z_scope.
Module YKK := OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YK11.
Module LBraidB := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_braid_encode_cg.
Module DFE := OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog.FloatExact.
#[global] Remove Hints OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The pcm sample values the convert loop reads, read at the entry state (pcm lies in a caller block, which the walk
   never writes), and the float each becomes: s24 of three little-endian bytes (`lbu`, `lbu`, `lb`, combined at
   +0x1dc .. +0x1fc), converted (`fcvt.s.w` at +0x200) and scaled by fa5 = F2M23 = 2^-23 (`fmul.s` at +0x204). *)
Definition crtB_pb (rd : reader) (pcm i : Z) : Z := match rd (pcm + i) with Some v => v | None => 0 end.
Definition crtB_s24 (b0 b1 b2 : Z) : Z := b0 + 256 * b1 + 65536 * b2 - (if 128 <=? b2 then 16777216 else 0).
Definition crtB_cv (rd : reader) (pcm j : Z) : Z :=
  DFE.f32 (crtB_s24 (crtB_pb rd pcm (3 * j)) (crtB_pb rd pcm (3 * j + 1)) (crtB_pb rd pcm (3 * j + 2))) (-23).

(* What the convert loop leaves in its two blocks: planar[c] = planes + 4 c ns (8 bytes at Q + 8 c, the `sd` at
   +0x154) for c < nch, and planes[k] = the float of pcm sample k (4 bytes at P + 4 k, the `fsw` at +0x208) for
   k < nch ns.  rd is the reader at the entry state. *)
Definition crtB_conv (rd : reader) (pcm nch ns P Q : Z) (mem : word -> option byte) : Prop :=
  (forall c, 0 <= c < nch -> bytes_at rsegs mem (Q + 8 * c) (le8 (Z_to_bv 64 (P + 4 * (c * ns))))) /\
  (forall k, 0 <= k < nch * ns -> bytes_at rsegs mem (P + 4 * k) (Z_to_le_bytes 4 (crtB_cv rd pcm k))).

Section CrtCuts.
Context {fx : YKK.FPState} {rc : YM05.RunCeil}.
Local Notation sink := dec_B_sink_head.
Local Notation segs := decodesegsB0.
Variable B : asyms.
Variable MT : ameter_ops.

(* The read-only bytes the walk's callees read: the leaf's read-only read set RO_RD, a list of (base, size).
   The frozen statement adds, besides cgif's `rom_view` at the entry (YG0d.v:382), a SCOPED instance fact over
   exactly this set (the porter's ruling, 2026-10-29 03:36Z): those bytes are in no owned static zone and are not
   errno.  It is deliberately not a global "owned statics are off ROM", which is FALSE for decode, because a
   read-only ASan global redzone IS an owned static in .rodata.  The lane carries rom_view RESTRICTED to RO_RD
   (crtB_rom_on) and proves it at each cut from those two premises and the journal's image clause (YCbq.v:362). *)
Variable RO_RD : list (Z * Z).
Definition crtB_in_ro_rd (a : Z) : Prop := exists r, In r RO_RD /\ fst r <= a < fst r + snd r.
Definition crtB_rom_on (W : world segs) (mem : word -> option byte) : Prop :=
  forall a, crtB_in_ro_rd a -> in_rom segs a ->
    aview segs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)).
Definition crtB_ro_scoped : Prop :=
  forall a, crtB_in_ro_rd a ->
    ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
(* RO_RD reads only bytes of the statement's read set DEC_RO_RD (check_round_trip_cg.v dec_in_ro_rd): the entry
   piece turns the statement's read-only image premise at DEC_RO_RD into crtB_rom_on RO_RD with it; the close
   discharges it at RO_RD := DEC_RO_RD (crtB_ro_sub_dec). *)
Definition crtB_ro_sub : Prop := forall a, crtB_in_ro_rd a -> dec_in_ro_rd a.
Local Notation ajournalB := (@ajournal rc sink segs B).

(* The entry data of one call of check_round_trip: what the contract's premises fix (check_round_trip_cg.v:153-166,
   but the float state, which each cut states for its own state), and the trace of the tail free. *)
Definition crtB_pre (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model) (k : Z)
    (regs : bvmap 5 word) (audio pcm nch ns bA nA bP nP T : Z) (ch : list (Z * Z * Z)) : Prop :=
  ajournalB STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\
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
  In (dec_utrace (pc_free_ra0 (as_code B)) (raZ regs :: spine ch)) (as_universe B) /\
  crtB_rom_on W memc /\
  crtB_ro_scoped.

(* The registers image B keeps live from +0x7c to the end, at a state whose frame is at spZ regs - CRT_FRAME:
   sp, gp, tp, s2 = ns, s5 = Q, s8 = ASAN_K. *)
Definition crtB_regs (regs regs1 : bvmap 5 word) (Q ns : Z) : Prop :=
  YKK.getr regs1 2 = w64 (spZ regs - CRT_FRAME) /\
  YKK.getr regs1 3 = YKK.getr regs 3 /\ YKK.getr regs1 4 = YKK.getr regs 4 /\
  YKK.getr regs1 18 = w64 ns /\ YKK.getr regs1 21 = w64 Q /\ YKK.getr regs1 24 = w64 ASAN_K.

(* The frame the prologue wrote, at [sp - 160, sp): the six slot words, audio at 24(sp), and the caller's s11 ..
   s0, ra (the prologue's saves at +0x04 .. +0x34; `sd a0,24(sp)` at +0x44). *)
Definition crtB_frame (regs : bvmap 5 word) (mem : word -> option byte) (audio : Z) (v0 v8 v16 v32 v40 v48 : word)
    : Prop :=
  rw_cells rsegs mem (spZ regs - CRT_FRAME)
    (crt_fr v0 v8 v16 (w64 audio) v32 v40 v48
       (YKK.getr regs 27) (YKK.getr regs 26) (YKK.getr regs 25) (YKK.getr regs 24) (YKK.getr regs 23)
       (YKK.getr regs 22) (YKK.getr regs 21) (YKK.getr regs 20) (YKK.getr regs 19) (YKK.getr regs 18)
       (YKK.getr regs 9) (YKK.getr regs 8) (YKK.getr regs 1)).

(* What the state at a cut shares with the entry, in cgif's form: an INNER journal started at the entry state
   (stack window [spZ regs - DEC_CRT_STK, spZ regs), no footprint, no frame of its own; YCbq.v:1827
   ajournal_sub_init starts it, YCbq.v:725 ajournal_sub composes it with the caller's journal at the end, and
   YCbq.v:973 acall_kept_of_journal reads the post's acall_kept off it), `k1` allocator events so far, the frames
   of the caller, the meter charged `acc`.  (crtA_mid also carries the frame; image B's frame holds six slot words
   that change from cut to cut, so each cut states crtB_frame itself.) *)
Definition crtB_mid (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model)
    (regs : bvmap 5 word)
    (ly1 : alayout) (S1 : astate) (W1 : world segs) (mem1 : word -> option byte) (md1 : Model)
    (k1 acc : Z) : Prop :=
  ajournalB DEC_CRT_STK (spZ regs) [] lyc Sc W memc mdc [] ly1 S1 W1 mem1 md1 k1 /\
  frames S1 = frames Sc /\
  mo_le MT Sc S1 acc /\
  crtB_rom_on W1 mem1.

(* The meter charged by the three allocations. *)
Definition crtB_acc3 (nch ns : Z) : Z :=
  mo_malloc MT (4 * (nch * ns)) + mo_malloc MT (8 * nch) + mo_malloc MT (3 * (nch * ns)).

(* The three temporaries are the only blocks the call has added. *)
Definition crtB_blocks3 (lyc : alayout) (Sc : astate) (ly1 : alayout) (S1 : astate) (P Q R nch ns : Z) : Prop :=
  Permutation (ablocks B ly1 S1)
    ((R, 3 * (nch * ns)) :: (Q, 8 * nch) :: (P, 4 * (nch * ns)) :: ablocks B lyc Sc) /\
  0 < P /\ 0 < Q /\ 0 < R.

(* ---- cut 1: after the calloc, at CRT_RET_CALLOC -------------------------------------------------------- *)
(* a0 = R (the calloc's block), s4 = pcm; the float state is the entry's.  No cut states ra: x1 is not in
   acallee_saved (YG0d.v:20), so no call rule gives it back, and no code after a cut reads it before a jal
   rewrites it (the epilogue reloads it from the frame). *)
Definition crtB_at_calloc : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs audio pcm nch ns bA nA bP nP T ch
         ly1 S1 W1 mem1 md1 regs1 P Q R (v0 v8 v32 : word),
    crtB_pre STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs audio pcm nch ns bA nA bP nP T ch ->
    crtB_mid lyc Sc W memc mdc regs ly1 S1 W1 mem1 md1 3 (crtB_acc3 nch ns) ->
    crtB_regs regs regs1 Q ns ->
    YKK.getr regs1 10 = w64 R -> YKK.getr regs1 20 = w64 pcm ->
    crtB_frame regs mem1 audio v0 v8 (w64 (3 * (nch * ns))) v32 (w64 nch) (w64 P) ->
    crtB_blocks3 lyc Sc ly1 S1 P Q R nch ns ->
    frm_zero (@fp_csr fx) ->
    SRr segs W1 (@cfg_at fx segs CRT_RET_CALLOC regs1 mem1 md1)
      (@dec_crt_post rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs nch ns).

(* ---- cut 1b (image B only): the outer loop's head at channel 0, at CRT_LOOP_IN ------------------------- *)
(* The loop constants (+0xb4 .. +0x108): t0 = Q & 7 = 0, t1 = 4 ns, t2 = 1, a6 = ~pcm, a7 = P & 3 = 0, t3 = CRT_T3,
   t4 = t6 = 3 ns, t5 = CRT_T5; the channel registers at channel 0: a3 = 0, a4 = 0, s0 = s11 = P, s4 = s9 = pcm;
   fa5 = F2M23 (`fmv.w.x fa5,a1` at +0x100); 8(sp) = R, 32(sp) = ~P. *)
Definition crtB_at_loopin : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs audio pcm nch ns bA nA bP nP T ch
         ly1 S1 W1 mem1 md1 regs1 P Q R (fx1 : YKK.FPState) (v0 : word),
    crtB_pre STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs audio pcm nch ns bA nA bP nP T ch ->
    crtB_mid lyc Sc W memc mdc regs ly1 S1 W1 mem1 md1 3 (crtB_acc3 nch ns) ->
    crtB_regs regs regs1 Q ns ->
    YKK.getr regs1 5 = w64 0 -> YKK.getr regs1 6 = w64 (4 * ns) -> YKK.getr regs1 7 = w64 1 ->
    YKK.getr regs1 16 = w64 (2 ^ 64 - 1 - pcm) -> YKK.getr regs1 17 = w64 0 ->
    YKK.getr regs1 28 = w64 CRT_T3 -> YKK.getr regs1 29 = w64 (3 * ns) -> YKK.getr regs1 30 = w64 CRT_T5 ->
    YKK.getr regs1 31 = w64 (3 * ns) ->
    YKK.getr regs1 13 = w64 0 -> YKK.getr regs1 14 = w64 0 -> YKK.getr regs1 8 = w64 P ->
    YKK.getr regs1 27 = w64 P -> YKK.getr regs1 20 = w64 pcm -> YKK.getr regs1 25 = w64 pcm ->
    frm_zero (@fp_csr fx1) -> unbox_s (reg_get (@fp_regs fx1) (Z_to_bv 5 15)) = Z_to_bv 32 DFE.F2M23 ->
    crtB_frame regs mem1 audio v0 (w64 R) (w64 (3 * (nch * ns))) (w64 (2 ^ 64 - 1 - P)) (w64 nch) (w64 P) ->
    crtB_blocks3 lyc Sc ly1 S1 P Q R nch ns ->
    SRr segs W1 (@cfg_at fx1 segs CRT_LOOP_IN regs1 mem1 md1)
      (@dec_crt_post rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs nch ns).

(* ---- cut 2: after the convert loop, at CRT_LOOP_OUT ----------------------------------------------------- *)
(* The loop has written the P and Q blocks (crtB_conv, against the entry reader); the float state has moved (fx1),
   with the rounding mode still zero.  (ra is not stated: image B's loop uses it, `slli ra,a0,2` at +0x110.) *)
Definition crtB_at_loopout : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs audio pcm nch ns bA nA bP nP T ch
         ly1 S1 W1 mem1 md1 regs1 P Q R (fx1 : YKK.FPState) (v0 v32 : word),
    crtB_pre STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs audio pcm nch ns bA nA bP nP T ch ->
    crtB_mid lyc Sc W memc mdc regs ly1 S1 W1 mem1 md1 3 (crtB_acc3 nch ns) ->
    crtB_regs regs regs1 Q ns ->
    crtB_frame regs mem1 audio v0 (w64 R) (w64 (3 * (nch * ns))) v32 (w64 nch) (w64 P) ->
    crtB_blocks3 lyc Sc ly1 S1 P Q R nch ns ->
    frm_zero (@fp_csr fx1) ->
    crtB_conv (aview segs (w_H W) memc) pcm nch ns P Q mem1 ->
    SRr segs W1 (@cfg_at fx1 segs CRT_LOOP_OUT regs1 mem1 md1)
      (@dec_crt_post rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs nch ns).

(* ---- cut 3: after bcmp, at CRT_RET_BCMP ----------------------------------------------------------------- *)
(* bcmp has answered 0 (the braid of the encoded rows is the caller's audio), so the branch to the abort block is
   refuted by the next segment; s0 = R; what is left is free(R), free(Q), the epilogue and the tail jump to
   free(P). *)
Definition crtB_at_bcmp : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs audio pcm nch ns bA nA bP nP T ch
         ly1 S1 W1 mem1 md1 regs1 P Q R (fx1 : YKK.FPState) (v0 v8 v16 v32 v40 : word),
    crtB_pre STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs audio pcm nch ns bA nA bP nP T ch ->
    crtB_mid lyc Sc W memc mdc regs ly1 S1 W1 mem1 md1 3 (crtB_acc3 nch ns) ->
    crtB_regs regs regs1 Q ns ->
    YKK.getr regs1 10 = w64 0 -> YKK.getr regs1 8 = w64 R ->
    crtB_frame regs mem1 audio v0 v8 v16 v32 v40 (w64 P) ->
    crtB_blocks3 lyc Sc ly1 S1 P Q R nch ns ->
    frm_zero (@fp_csr fx1) ->
    SRr segs W1 (@cfg_at fx1 segs CRT_RET_BCMP regs1 mem1 md1)
      (@dec_crt_post rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs nch ns).

(* ---- the premises of dec_check_round_trip_cg_holds_stmt that every piece may use --------------------------- *)
(* check_round_trip_cg.v:225-235 but dec_crt_uctx CTX (the entry piece turns it into crtB_pre's trace fact). *)
Definition crtB_rules : Prop :=
  pc_wrap_malloc (as_code B) = decodeb_sigma DB___interceptor_trampoline_malloc /\
  pc_wrap_free (as_code B) = decodeb_sigma DB___interceptor_trampoline_free /\
  dec_crt_cells B /\
  AR_laws segs B /\ ameter_laws MT /\ dec_crt_ufix B /\
  (forall fx' : YKK.FPState, @amalloc04_rule fx' rc sink segs B MT) /\
  (forall fx' : YKK.FPState, @afree04_rule fx' rc sink segs B MT) /\
  (forall fx' : YKK.FPState, @acalloc04_rule fx' segs B (as_universe B) ajournalB (@acall_kept rc segs B)
     (mo_ok MT) (mo_le MT) (mo_malloc MT) (decodeb_sigma DB___interceptor_trampoline_calloc) DEC_B_calloc_ra0
     DEC_CALLOC_MAX DEC_CALLOC_DEPTH) /\
  (forall fx' : YKK.FPState, @abcmp_realizes fx' rc segs B (decodeb_sigma DB___interceptor_trampoline_bcmp)) /\
  (forall fx' : YKK.FPState, @dec_leaf_wr_at rc B (@LBraidB.dec_reac_braid_encode_cg) fx').

(* ---- the five pieces ---- *)
(* PROLOGUE + ALLOCATOR CALLS (a Theorem Labs lane): CRT_ENTRY .. CRT_RET_CALLOC.  It concludes the frozen statement's own
   contract dec_check_round_trip_cg (a working branch 7bdd511d726), and takes the
   scoped read-only fact over the cuts' RO_RD that crtB_pre carries; the close discharges it at RO_RD := DEC_RO_RD
   by the statement's dec_ro_rd_scoped. *)
Definition crtB_entry_stmt : Prop :=
  crtB_rules -> crtB_at_calloc ->
  forall CTX, dec_crt_uctx B CTX -> crtB_ro_scoped -> crtB_ro_sub ->
    @dec_check_round_trip_cg fx rc B MT (decodeb_sigma DB_check_round_trip) CTX.
(* NULL CHECKS + LOOP CONSTANTS (a Theorem Labs lane): CRT_RET_CALLOC .. CRT_LOOP_IN. *)
Definition crtB_setup_stmt : Prop := crtB_rules -> crtB_at_loopin -> crtB_at_calloc.
(* THE TWO LOOPS (a Theorem Labs lane, crtB_loop.v): CRT_LOOP_IN through CRT_ILOOP and CRT_LOOP_TAIL to CRT_LOOP_OUT. *)
Definition crtB_loop_stmt : Prop := crtB_rules -> crtB_at_loopout -> crtB_at_loopin.
(* ENCODE + BCMP (a Theorem Labs lane, crtB_encbcmp.v): CRT_LOOP_OUT through CRT_RET_ENCODE to CRT_RET_BCMP with
   a0 = 0 (the bcmp equality is the braid relation; the abort branch is refuted there).  crtB_at_loopout's
   rom_view (the premise EncBcmp asked for) is the last conjunct of crtB_mid, which that cut takes. *)
Definition crtB_encbcmp_stmt : Prop := crtB_rules -> crtB_at_bcmp -> crtB_at_loopout.
(* THE BCMP TEST, THE FREES AND THE EPILOGUE (a Theorem Labs lane): CRT_RET_BCMP .. dec_crt_post. *)
Definition crtB_tail_stmt : Prop := crtB_rules -> crtB_at_bcmp.

(* ---- the composition ---- *)
(* The statement's conclusion from the five pieces, the scoped read-only fact over RO_RD, and the statement's premises
   but its two instance facts (dec_rom_owned_in_slot / dec_rom_no_errno), which give the scoped fact at DEC_RO_RD. *)
Theorem crtB_holds_of_cuts :
  crtB_entry_stmt -> crtB_setup_stmt -> crtB_loop_stmt -> crtB_encbcmp_stmt -> crtB_tail_stmt ->
  forall CTX : list (list Z),
    crtB_ro_scoped -> crtB_ro_sub ->
    pc_wrap_malloc (as_code B) = decodeb_sigma DB___interceptor_trampoline_malloc ->
    pc_wrap_free (as_code B) = decodeb_sigma DB___interceptor_trampoline_free ->
    dec_crt_cells B ->
    AR_laws segs B -> ameter_laws MT ->
    dec_crt_uctx B CTX -> dec_crt_ufix B ->
    (forall fx' : YKK.FPState, @amalloc04_rule fx' rc sink segs B MT) ->
    (forall fx' : YKK.FPState, @afree04_rule fx' rc sink segs B MT) ->
    (forall fx' : YKK.FPState, @acalloc04_rule fx' segs B (as_universe B) ajournalB (@acall_kept rc segs B)
       (mo_ok MT) (mo_le MT) (mo_malloc MT) (decodeb_sigma DB___interceptor_trampoline_calloc) DEC_B_calloc_ra0
       DEC_CALLOC_MAX DEC_CALLOC_DEPTH) ->
    (forall fx' : YKK.FPState, @abcmp_realizes fx' rc segs B (decodeb_sigma DB___interceptor_trampoline_bcmp)) ->
    (forall fx' : YKK.FPState, @dec_leaf_wr_at rc B (@LBraidB.dec_reac_braid_encode_cg) fx') ->
    @dec_check_round_trip_cg fx rc B MT (decodeb_sigma DB_check_round_trip) CTX.
Proof.
  intros HE HS HL HB HT CTX HSC HSUB HM HF HC HAR HML HU HUF RM RF RC RB RE.
  assert (R : crtB_rules)
    by exact (conj HM (conj HF (conj HC (conj HAR (conj HML (conj HUF (conj RM (conj RF (conj RC (conj RB RE)))))))))).
  exact (HE R (HS R (HL R (HB R (HT R)))) CTX HU HSC HSUB).
Qed.
End CrtCuts.
