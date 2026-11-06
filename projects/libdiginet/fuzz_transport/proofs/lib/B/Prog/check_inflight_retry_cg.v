(* check_inflight_retry_cg: the ASan walk contract of check_inflight_retry (fuzz/fuzz_transport.c:450-474; model
   lib/TModel/TCb.v check_inflight_retry_m) on fuzz_transport.asan-ubsan (41113a03c82f) at 0x844fc =
   transportb_sigma TB_check_inflight_retry, size 300, as STATEMENTS only (no proof). It stores into no harness global
   and calls the bcmp wrapper, so it takes decode's caller-journal form (lib/B/Prog/DgnTransportBCg.v decode_cg_post
   over the caller's donor journal ajournal); a G-form caller lifts it with lib/A/Prog/TransportGCg.v gx_call_cg
   (stated over any segments, record and G, so image B's walks use it too). Image B's twin of
   lib/A/Prog/check_inflight_retry_cg.v: the same statement at image B's world table, cells and listing; the
   differences image B's code forces are listed at the end of this comment.

   The contract. a0 = fa, the len bytes frame (a1 = len = length frame); a2 = fp, the struct spec_frame of 80 bytes
   that holds the parse TCb.rf frame of the bytes at fa (check_sent_frame_cg.v trans_sframe_at). The bytes at fa may
   lie in a harness global (g_s.inflight_frame), a caller's frame or a heap block, the struct in the caller's machine
   frame: trans_src_ok of both ranges, both outside this call's stack window (decode_off_win). The memory relates to
   the world Bw by image B's world relation (lib/A/Prog/TWorldG.v tw_at at lib/B/Prog/TWorldB.v TMAP_B, read through
   aview), check_inflight_retry_m Bw frame = Some (Bw', tt), and M.fly.len <= 1514 (SPEC_MAX_FRAME, the size of
   M.fly.frame). The function returns to ra with the callee-saved registers kept, no allocator event, no meter charge,
   every byte outside its stack window kept (it stores nothing outside its own frame: E is empty), and Bw' = Bw. This
   is what the plain contract (lib/Prog/T/check_inflight_retry_c.v) says: void; B' = B and wmem rsegs m' B; munch of
   the frame only. Its bytes_at / off_window / sframe_at / wmem premises become garr8 + trans_src_ok + decode_off_win /
   trans_sframe_at / tw_at; mem_inv is dropped, and so is fa + 28 < 2 ^ 64, the premise of the
   ubsan build's pointer-overflow check: image B has that check (0x84564 - 0x84578), and the walk rules it out from
   0 < fa, len >= 28 (the code's test at 0x84534, before it) and the bound fa + len <= 2 ^ 63 it takes from
   trans_src_ok, the bound abcmp_realizes asks of the second bcmp's range [fa + 28, fa + len) as well.
   The one premise the plain contract does not have: M.fly.len <= 1514. The second bcmp reads len - 28 bytes from
   M + 148, and the model bounds len only by the plain world (W_LEN <? A_M_fly_frame + len); on image B, M's payload
   ends at M + 1648, after which come the bytes the runtime marks unusable, so with len > 1528 the wrapper's check
   fails (the error path). The plain side's run invariant has it: lib/TSim/Agree.v agree_fly's b8_frames gives, when
   M.fly.on = 1, M.fly.len = frame_len of a body of at most 1484 bytes, so at most 1514 (io_send stores
   min (len, 1514), TCb.v io_send_m :888); the caller supplies it from that invariant.

   The code, measured on the symbol-bearing twin (e217cb0a84f1; its loaded bytes equal the pin's but the ELF header's
   section-table fields and the build-id note, and the 300 code bytes of this function are equal in both files),
   75 words:
     0x844fc          sp = sp - 48; ra, s0 .. s4 at sp + 40 .. sp + 0 (0x84500 - 0x84514), loaded back at 0x845ec -
                      0x84600; no side-stack frame, no frame pointer. s1 = len (0x84518), s3 = M = 0x5dede0
                      (0x8451c - 0x84520), s2 = fa (0x8452c), s0 = fp (0x84540).
     0x84524 - 0x8453c  the 4-byte load of M.fly.on (M + 96, no instrumented check): 0 goes to the trap; len < 28
                      (unsigned) goes to the trap; len <> M.fly.len (the 8-byte load at M + 1640) goes to the trap.
     0x84544 - 0x8454c  s4 = the 8-byte load at the GOT word 0xa3cf0 (GOT_CELL_K), then at the cell 0xac678 (CELL_K)
                      it holds: the shadow base 0x7fff8000 (transport_cells rows 1-2).
     0x84550 - 0x84560  bcmp (0x42d34 = transportb_sigma TB___interceptor_trampoline_bcmp) at 0x8455c with (fa, M + 120
                      = 0x5dee58 (M.fly.frame), 26); a result not 0 goes to the trap.
     0x84564 - 0x84578  the ubsan build's checks of frame + 28: fa = 0 (0x84564), fa > 2 ^ 64 - 27 (unsigned, 0x8456c:
                      fa + 26 wraps) or fa + 26 >= 2 ^ 64 - 2 (unsigned, 0x84578: fa + 28 wraps) goes to the unimp
                      word at 0x84614.
     0x8457c - 0x8458c  bcmp at 0x84588 with (fa + 28, M + 148 = 0x5dee74, len - 28); a result not 0 goes to the
                      trap. The two bytes at fa + 26 (the retry field) are not compared.
     0x84590 - 0x84594  fp & 7 <> 0 goes to the unimp word (the ubsan build's alignment check).
     0x84598 - 0x845b0  the instrumented check of the 2-byte load at fp + 30 (the shadow byte k at
                      ((fp + 30) >> 3) + 0x7fff8000; k = 0 goes on; else ((fp + 30) & 7) + 1 < k (signed) goes on; else
                      the error path), then M.fly.retries (the 4-byte load at M + 108) and f->retry (fp + 30).
     0x845b4 - 0x845c8  M.fly.retries + 1 (32-bit) <> f->retry goes to the trap; g_cfg.max_retries (the 4-byte load at
                      g_cfg + 32 = 0x5ded20, no instrumented check) < f->retry (unsigned) goes to the trap.
     0x845cc - 0x845e8  g_now (0x5ded80) - M.fly.sent (M + 112) < g_cfg.ack_timeout_ms (g_cfg + 28, zero-extended)
                      * 1000 (unsigned) goes to the trap; else the return at 0x84608 (a0 not stated: void).
   The trap: 0x8460c call of __asan_handle_no_return (0x5a500, TB___asan_handle_no_return), 0x84610 call of abort
   (0x93390, TB_abort), then 0x84614 the word 0xc0001073 (unimp: a write of the read-only CSR cycle, an illegal
   instruction that traps); every branch to 0x8460c is ruled out by check_inflight_retry_m Bw frame = Some _: its
   tests are the code's tests, read through tw_at (M.fly.*, g_cfg.max_retries, g_cfg.ack_timeout_ms, g_now),
   trans_sframe_at (f->retry is sf_retry (rf frame)) and the bcmp results (0 exactly when the bytes agree,
   abcmp_realizes; the model's sub Bw A_M_fly_frame .. are the bytes at M + 120 .. by tw_at).
   The unimp word at 0x84614 (the ubsan build's checks) and the facts that rule out each branch to it: 0x84564:
   0 < fa; 0x8456c and 0x84578: fa + 28 <= fa + len <= 2 ^ 63 (len >= 28 from the test at 0x84534; the bound from
   trans_src_ok of [fa, fa + len)); 0x84594: trans_sframe_at's fp mod 8 = 0.
   Error path (1 call) and the fact that rules it out: __asan_report_load2 (0x595a4) at 0x84624 (fp + 30): the 80
   bytes at fp are marked usable (trans_src_ok: a heap block's bytes by AR_laws' block shadow, else decode_rd_ok's
   range_addressable), and bcmp keeps every byte outside its stack window [sp - 48 - 2 * ESTACK, sp - 48), which
   decode_off_win puts fp's 80 bytes outside.
   Callee texts assumed: the bcmp wrapper as abcmp_realizes (YG0d.v) at transportb_sigma
   TB___interceptor_trampoline_bcmp. Its ranges: [fa, fa + 26) and [fa + 28, fa + len) (trans_src_ok), and
   [M + 120, M + 146) and [M + 148, M + 120 + len) in M, whose shadow is 0: len = M.fly.len <= 1514 (the model and
   the premise), so M + 120 + len <= M + 1634 < M + 1648. Besides the range's own shadow bytes, abcmp_realizes asks
   every shadow byte of the aligned group of 8 around them to be visible (YG0d.v shadow_hull_vis: the shadow of 64
   bytes). For len = 1513 or 1514 (frames of 1483- and 1484-byte bodies) the second range ends at 0x5df440 /
   0x5df441, whose shadow byte 0x800b3e88 lies in the group [0x800b3e88, 0x800b3e90), past M's zero shadow (which
   ends at 0x800b3e8a): trans_cir_cells gives the six bytes 0x800b3e8a .. 0x800b3e8f (M's guard granules, 0xf9).
   Each is a row of the record (lib/B/YF0m.v Tfib_zero_shadow, Tfib_const_shadow). No program function is called.
   Stack: 48 bytes of its own and the 2 * ESTACK the bcmp wrapper uses below sp - 48 (abcmp_realizes): CIR_STK.

   The caller is io_send (the call at 0x830e0, return address 0x830e4): a0 = s1 (its argument frame), a1 = s0 (len),
   a2 = sp + 8 (its struct spec_frame, in its 160-byte machine frame, in the machine stack), as for
   check_sent_frame.

   Against image A's statement (lib/A/Prog/check_inflight_retry_cg.v): the same premises, post and holds statement,
   at image B's names (TMAP_B, TB_M, transportb_sigma, lib/B/Prog/DgnTransportBCg.v); the same six guard rows, at image
   B's addresses. What image B's code forces: the branches to the unimp word (the ubsan build's pointer-overflow check
   of frame + 28 and alignment check of fp; image A has neither), ruled out by premises the statement already has
   (0 < fa, trans_src_ok, trans_sframe_at), so no premise is added and the plain contract's fa + 28 < 2 ^ 64 stays
   dropped; the error path is a direct call of the runtime's report entry (image A's file names it errpath_load2). *)
From Stdlib Require Import ZArith List Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBAddr DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_sent_frame_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module BCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* check_inflight_retry's frame (`sp = sp - 48` at its entry; no realignment) and the 2 * ESTACK its bcmp calls use
   below sp - 48 (abcmp_realizes, YG0d.v). *)
Definition CIR_FRAME : Z := 48.
Definition CIR_STK : Z := CIR_FRAME + 2 * ESTACK.
(* No allocator event: it calls neither malloc nor free and takes no side-stack frame. *)
Definition CIR_EV : Z := 0.

(* The shadow facts of the record (lib/B/YF0m.v Tfib_zero_shadow and Tfib_const_shadow rows) that the bcmp calls need:
   M's payload (1648 bytes, 206 whole granules) has shadow 0, and the six guard granules after it that share the
   aligned group of 8 shadow bytes of M's last payload bytes. Both bcmp calls read M.fly.frame. *)
Definition trans_cir_cells (B : asyms) : Prop :=
  decode_zshadow_at B TB_M (TB_M + TW.SZ_M) /\
  forall ly,
    In (z1 (ANum (BCells.shadow_addr (TB_M + TW.SZ_M))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TB_M + TW.SZ_M + 8))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TB_M + TW.SZ_M + 16))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TB_M + TW.SZ_M + 24))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TB_M + TW.SZ_M + 32))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TB_M + TW.SZ_M + 40))) 0xf9) (as_const B ly).
Lemma trans_cir_cells_rows :
  map (fun j => BCells.shadow_addr (TB_M + TW.SZ_M + 8 * j)) [0; 1; 2; 3; 4; 5] =
  [0x800b3e8a; 0x800b3e8b; 0x800b3e8c; 0x800b3e8d; 0x800b3e8e; 0x800b3e8f].
Proof. reflexivity. Qed.

Section cir. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal := (@ajournal rc tfib_sink_head segs B).

(* What a call leaves: DgnTransportBCg.v decode_cg_post with no event, no written range, no meter charge, and X: the
   model's world is the world it was given. *)
Definition transport_cir_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (Bw Bw' : list byte) : world segs -> config -> Prop :=
  @decode_cg_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs CIR_STK CIR_EV 0
    (fun _ => False) (fun _ _ _ => Bw' = Bw).

(* The contract at entry address a, in the caller-journal form. *)
Definition transport_check_inflight_retry_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (fa fp : Z) (frame : list byte) (Bw Bw' : list byte),
    ajournal STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 fa -> YK11.getr regs 11 = w64 (Z.of_nat (length frame)) -> YK11.getr regs 12 = w64 fp ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - CIR_STK -> spZ regs <= sp0 ->
    0 < fa ->
    garr8 segs (mrestrict (w_H W) memc) fa (map DSpec.bz frame) ->
    trans_src_ok B lyc Sc W memc fa (Z.of_nat (length frame)) ->
    decode_off_win regs CIR_STK fa (Z.of_nat (length frame)) ->
    trans_sframe_at W memc fp fa (TC.rf frame) ->
    trans_src_ok B lyc Sc W memc fp SF_SIZE ->
    decode_off_win regs CIR_STK fp SF_SIZE ->
    tw_at TMAP_B (aview segs (w_H W) memc) Bw ->
    TC.check_inflight_retry_m Bw frame = Some (Bw', tt) ->
    TW.M_fly_len Bw <= TC.SPEC_MAX_FRAME ->
    st_nev S + k + CIR_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (transport_cir_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw').

(* The statement the walk will prove: the runtime cells (the shadow base through its GOT word), M's shadow and the
   guard granules after it (trans_cir_cells), the allocator and meter laws, and the bcmp contract at the listing's
   trampoline give the contract at TB_check_inflight_retry. *)
Definition transport_check_inflight_retry_cg_holds_stmt : Prop :=
  transport_cells B -> trans_cir_cells B ->
  AR_laws segs B -> ameter_laws MT ->
  (forall fx' : YK11.FPState, @abcmp_realizes fx' rc segs B (transportb_sigma TB___interceptor_trampoline_bcmp)) ->
  transport_check_inflight_retry_cg (transportb_sigma TB_check_inflight_retry).
End cir.
