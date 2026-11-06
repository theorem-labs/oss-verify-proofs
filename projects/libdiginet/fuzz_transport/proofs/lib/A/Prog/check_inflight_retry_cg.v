(* check_inflight_retry_cg: the ASan walk contract of check_inflight_retry (fuzz/fuzz_transport.c:450-474; model
   lib/TModel/TCb.v check_inflight_retry_m) on fuzz_transport.asan (e89be137db17) at 0x84268 =
   transport_sigma TS_check_inflight_retry, size 264, as STATEMENTS only (no proof). It stores into no harness global
   and calls the bcmp wrapper, so it takes decode's caller-journal form (lib/A/Prog/DgnTransportCg.v decode_cg_post
   over the caller's donor journal ajournal); a G-form caller lifts it with lib/A/Prog/TransportGCg.v gx_call_cg.

   The contract. a0 = fa, the len bytes frame (a1 = len = length frame); a2 = fp, the struct spec_frame of 80 bytes
   that holds the parse TCb.rf frame of the bytes at fa (check_sent_frame_cg.v trans_sframe_at). The bytes at fa may
   lie in a harness global (g_s.inflight_frame), a caller's frame or a heap block, the struct in the caller's machine
   frame: trans_src_ok of both ranges, both outside this call's stack window (decode_off_win). The memory relates to
   the world Bw by image A's world relation (TWorldG.v tw_at at TWorldA.v TMAP_A, read through aview),
   check_inflight_retry_m Bw frame = Some (Bw', tt), and M.fly.len <= 1514 (SPEC_MAX_FRAME, the size of M.fly.frame).
   The function returns to ra with the callee-saved registers kept, no allocator event, no meter charge, every byte
   outside its stack window kept (it stores nothing outside its own frame: E is empty), and Bw' = Bw. This is what the
   plain contract (lib/Prog/T/check_inflight_retry_c.v) says: void; B' = B and wmem rsegs m' B; munch of the frame
   only. Its bytes_at / off_window / sframe_at / wmem premises become garr8 + trans_src_ok + decode_off_win /
   trans_sframe_at / tw_at; mem_inv is dropped, and so is fa + 28 < 2 ^ 64, the premise of the
   ubsan build's pointer-overflow check: image A has no such check, and the bound the walk needs on [fa, fa + len)
   comes from trans_src_ok.
   The one premise the plain contract does not have: M.fly.len <= 1514. The second bcmp reads len - 28 bytes from
   M + 148, and the model bounds len only by the plain world (W_LEN <? A_M_fly_frame + len); on image A, M's payload
   ends at M + 1648, after which come the bytes the runtime marks unusable, so with len > 1528 the wrapper's check
   fails (the error path). The plain side's run invariant has it: lib/TSim/Agree.v agree_fly's b8_frames gives, when
   M.fly.on = 1, M.fly.len = frame_len of a body of at most 1484 bytes, so at most 1514 (io_send stores
   min (len, 1514), TCb.v io_send_m :888); the caller supplies it from that invariant.

   The code, measured on the symbol-bearing twin (86efc3a80314; its loaded bytes equal the pin's), 66 words:
     0x84268          sp = sp - 48; ra, s0 .. s4 at sp + 40 .. sp + 0 (0x8426c - 0x84280), loaded back at 0x84338 -
                      0x8434c; no side-stack frame, no frame pointer. s1 = len (0x84284), s3 = M = 0x5df160
                      (0x84288 - 0x8428c), s2 = fa (0x84298), s0 = fp (0x842ac).
     0x84290 - 0x842a8  the 4-byte load of M.fly.on (M + 96, no instrumented check): 0 goes to the trap; len < 28
                      (unsigned) goes to the trap; len <> M.fly.len (the 8-byte load at M + 1640) goes to the trap.
     0x842b0 - 0x842b8  s4 = the 8-byte load at the GOT word 0xa4090, then at the cell 0xac9f8 it holds: the shadow
                      base 0x7fff8000 (transport_cells rows 1-2).
     0x842bc - 0x842cc  bcmp (0x42cf8 = transport_sigma TS___interceptor_trampoline_bcmp) at 0x842c8 with (fa, M + 120
                      = 0x5df1d8 (M.fly.frame), 26); a result not 0 goes to the trap.
     0x842d0 - 0x842e0  bcmp at 0x842dc with (fa + 28, M + 148 = 0x5df1f4, len - 28); a result not 0 goes to the
                      trap. The two bytes at fa + 26 (the retry field) are not compared.
     0x842e4 - 0x842fc  the instrumented check of the 2-byte load at fp + 30 (the shadow byte k at
                      ((fp + 30) >> 3) + 0x7fff8000; k = 0 goes on; else ((fp + 30) & 7) + 1 < k (signed) goes on; else
                      the error path), then f->retry (fp + 30) and M.fly.retries (the 4-byte load at M + 108).
     0x84300 - 0x84314  M.fly.retries + 1 (32-bit) <> f->retry goes to the trap; g_cfg.max_retries (the 4-byte load at
                      g_cfg + 32 = 0x5df0a0, no instrumented check) < f->retry (unsigned) goes to the trap.
     0x84318 - 0x84334  g_now (0x5df100) - M.fly.sent (M + 112) < g_cfg.ack_timeout_ms (g_cfg + 28, zero-extended)
                      * 1000 (unsigned) goes to the trap; else the return at 0x84354 (a0 not stated: void).
   The trap: 0x84358 call of before_abort (0x5a4c4), 0x8435c call of abort (0x93734); every branch to it is ruled out
   by check_inflight_retry_m Bw frame = Some _: its tests are the code's tests, read through tw_at (M.fly.*,
   g_cfg.max_retries, g_cfg.ack_timeout_ms, g_now), trans_sframe_at (f->retry is sf_retry (rf frame)) and the bcmp
   results (0 exactly when the bytes agree, abcmp_realizes; the model's sub Bw A_M_fly_frame .. are the bytes at
   M + 120 .. by tw_at).
   Error path (1 call) and the fact that rules it out: errpath_load2 0x8436c (fp + 30): the 80 bytes at fp are marked
   usable (trans_src_ok: a heap block's bytes by AR_laws' block shadow, else decode_rd_ok's range_addressable), and
   bcmp keeps every byte outside its stack window [sp - 48 - 2 * ESTACK, sp - 48), which decode_off_win puts fp's 80
   bytes outside.
   Callee texts assumed: the bcmp wrapper as abcmp_realizes (YG0d.v) at transport_sigma
   TS___interceptor_trampoline_bcmp. Its ranges: [fa, fa + 26) and [fa + 28, fa + len) (trans_src_ok), and
   [M + 120, M + 146) and [M + 148, M + 120 + len) in M, whose shadow is 0: len = M.fly.len <= 1514 (the model and
   the premise), so M + 120 + len <= M + 1634 < M + 1648. Besides the range's own shadow bytes, abcmp_realizes asks
   every shadow byte of the aligned group of 8 around them to be visible (YG0d.v shadow_hull_vis: the shadow of 64
   bytes). For len = 1513 or 1514 (frames of 1483- and 1484-byte bodies) the second range ends at 0x5df7c0 /
   0x5df7c1, whose shadow byte 0x800b3ef8 lies in the group [0x800b3ef8, 0x800b3f00), past M's zero shadow (which
   ends at 0x800b3efa): trans_cir_cells gives the six bytes 0x800b3efa .. 0x800b3eff (M's guard granules, 0xf9).
   Each is a row of the record (lib/A/AF0m.v Tfib_zero_shadow, Tfib_const_shadow). No program function is called.
   Stack: 48 bytes of its own and the 2 * ESTACK the bcmp wrapper uses below sp - 48 (abcmp_realizes): CIR_STK.

   The caller is io_send (the call at 0x830fc, return address 0x83100): a0 = s1 (its argument frame), a1 = s0 (len),
   a2 = sp + 8 (its struct spec_frame, in its 160-byte machine frame, in the machine stack), as for
   check_sent_frame. *)
From Stdlib Require Import ZArith List Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportSyms DgnTransportAddr DgnTransportCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_sent_frame_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module ACells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
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

(* The shadow facts of the record (lib/A/AF0m.v Tfib_zero_shadow and Tfib_const_shadow rows) that the bcmp calls need:
   M's payload (1648 bytes, 206 whole granules) has shadow 0, and the six guard granules after it that share the
   aligned group of 8 shadow bytes of M's last payload bytes. Both bcmp calls read M.fly.frame. *)
Definition trans_cir_cells (B : asyms) : Prop :=
  decode_zshadow_at B TA_M (TA_M + TW.SZ_M) /\
  forall ly,
    In (z1 (ANum (ACells.shadow_addr (TA_M + TW.SZ_M))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TA_M + TW.SZ_M + 8))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TA_M + TW.SZ_M + 16))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TA_M + TW.SZ_M + 24))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TA_M + TW.SZ_M + 32))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TA_M + TW.SZ_M + 40))) 0xf9) (as_const B ly).
Lemma trans_cir_cells_rows :
  map (fun j => ACells.shadow_addr (TA_M + TW.SZ_M + 8 * j)) [0; 1; 2; 3; 4; 5] =
  [0x800b3efa; 0x800b3efb; 0x800b3efc; 0x800b3efd; 0x800b3efe; 0x800b3eff].
Proof. reflexivity. Qed.

Section cir. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal := (@ajournal rc tfib_sink_head segs B).

(* What a call leaves: DgnTransportCg.v decode_cg_post with no event, no written range, no meter charge, and X: the
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
    tw_at TMAP_A (aview segs (w_H W) memc) Bw ->
    TC.check_inflight_retry_m Bw frame = Some (Bw', tt) ->
    TW.M_fly_len Bw <= TC.SPEC_MAX_FRAME ->
    st_nev S + k + CIR_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (transport_cir_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw').

(* The statement the walk will prove: the runtime cells (the shadow base through its GOT word), M's shadow and the
   guard granules after it (trans_cir_cells), the allocator and meter laws, and the bcmp contract at the listing's
   trampoline give the contract at TS_check_inflight_retry. *)
Definition transport_check_inflight_retry_cg_holds_stmt : Prop :=
  transport_cells B -> trans_cir_cells B ->
  AR_laws segs B -> ameter_laws MT ->
  (forall fx' : YK11.FPState, @abcmp_realizes fx' rc segs B (transport_sigma TS___interceptor_trampoline_bcmp)) ->
  transport_check_inflight_retry_cg (transport_sigma TS_check_inflight_retry).
End cir.
