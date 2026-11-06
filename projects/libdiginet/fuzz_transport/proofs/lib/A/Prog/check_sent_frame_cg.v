(* check_sent_frame_cg: the ASan walk contract of check_sent_frame (fuzz/fuzz_transport.c:398-420; model
   lib/TModel/TCb.v check_sent_frame_m) on fuzz_transport.asan (e89be137db17) at 0x83e68 =
   transport_sigma TS_check_sent_frame, size 756, as STATEMENTS only (no proof). It stores into no harness global and
   calls the bcmp wrapper, so it takes decode's caller-journal form (lib/A/Prog/DgnTransportCg.v decode_cg_post over
   the caller's donor journal ajournal); a G-form caller lifts it with lib/A/Prog/TransportGCg.v gx_call_cg.

   The contract. a0 = fa, the len bytes frame (a1 = len = length frame); a2 = fp, the struct spec_frame of 80 bytes
   that holds the parse TCb.rf frame of the bytes at fa, field by field (trans_sframe_at: TContract.sframe_at read
   through the walk's image view). The bytes at fa may lie in a harness global (g_s.inflight_frame), a caller's frame
   or a heap block, and the struct in the caller's machine frame: trans_src_ok of both ranges, both outside this
   call's stack window (decode_off_win). The memory relates to the world Bw by image A's world relation (TWorldG.v
   tw_at at TWorldA.v TMAP_A, read through aview), check_sent_frame_m Bw frame = Some (Bw', tt), and the read-only
   bytes it compares (HOST) read as the image's (trans_rom_view_rd). The function returns to ra with the callee-saved
   registers kept, no allocator event, no meter charge, every byte outside its stack window kept (it stores nothing
   outside its own frame: E is empty), and Bw' = Bw. This is what the plain contract
   (lib/Prog/T/check_sent_frame_c.v) says: void; B' = B and wmem rsegs m' B; munch of the frame only. Its
   bytes_at / off_window / sframe_at / wmem / mem_inv premises become garr8 + trans_src_ok + decode_off_win /
   trans_sframe_at / tw_at, and mem_inv is dropped.

   The code, measured on the symbol-bearing twin (86efc3a80314; its loaded bytes equal the pin's), 189 words:
     0x83e68          sp = sp - 48; ra, s0 .. s3 at sp + 40 .. sp + 8 (0x83e6c - 0x83e7c), loaded back at 0x840f8 -
                      0x8410c; no side-stack frame, no frame pointer. s0 = fp, s1 = len, s2 = fa.
     0x83e88 - 0x83e90  s3 = the 8-byte load at the GOT word 0xa4090, then at the cell 0xac9f8 it holds: the shadow
                      base 0x7fff8000 (transport_cells rows 1-2).
     each instrumented check below: the shadow byte k at (a >> 3) + 0x7fff8000; k = 0 goes on; for an n-byte load
                      (n < 8), ((a & 7) + n - 1) < k (signed) goes on; else the error path. An 8-byte load goes on only
                      at k = 0.
     0x83e94 - 0x83eac  the check of the 4-byte load at fp, then f->code (fp + 0); not 0 goes to the trap.
     0x83eb0 - 0x83ed8  the check of the 8-byte load at fp + 16 and f->src; bcmp (0x42cf8 = transport_sigma
                      TS___interceptor_trampoline_bcmp) at 0x83ed4 with (f->src, HOST = 0x21040 = TRANS_HOST, 6); a
                      result not 0 goes to the trap.
     0x83edc - 0x83ee8  the 4-byte load of M.desk_known at M = 0x5df160 (no instrumented check); 0 goes to the trap.
     0x83eec - 0x83f10  the check of the 8-byte load at fp + 8 and f->dst; bcmp at 0x83f0c with (f->dst, M + 4 =
                      0x5df164 (M.desk), 6); a result not 0 goes to the trap.
     0x83f14 - 0x83f40  the checks of the 8-byte loads at fp + 48 and fp + 56: a3 = f->body, a2 = f->body_len.
     0x83f44 - 0x83ff4  spec_system_at, inlined: when body_len >= 4, for i = 0 .. body_len - 4 the checked 1-byte
                      loads of body[i], body[i + 1], body[i + 3]; the pattern 0xf0, 0x13, _, 0x70 at some i goes to the
                      trap (bgez at 0x83ff4).
     0x83ff8 - 0x84008  n = body_len + 30; a1 = n when n > 60, else 60.
     0x8400c - 0x84070  when n < len, the checked 1-byte loads of frame[n .. len) (at fa + n + j), all 0 or not.
     0x84074 / 0x84078  len <> a1 goes to the trap; a byte of frame[n .. len) not 0 goes to the trap.
     0x8407c - 0x84090  the check of the 2-byte load at fp + 28 and f->sum.
     0x84094 - 0x840f0  want = 0 when body_len = 0 or g_cfg.sum_mode (the 4-byte load at g_cfg + 20 = 0x5df094, no
                      instrumented check) is 1; else the low 16 bits of the sum of the checked 1-byte loads of
                      body[0 .. body_len).
     0x840f4          f->sum <> want goes to the trap; else the return at 0x84110 (a0 not stated: void).
   The trap: 0x84114 call of before_abort (0x5a4c4), 0x84118 call of abort (0x93734); every branch to it is ruled out
   by check_sent_frame_m Bw frame = Some _: its tests are the code's tests, read through tw_at (M.desk_known, M.desk,
   g_cfg.sum_mode), trans_sframe_at (the struct's fields are those of rf frame) and the bcmp results (0 exactly when
   the bytes agree, abcmp_realizes).
   Error paths (11 calls) and the facts that rule them out: errpath_load4 0x8412c (fp), errpath_load8 0x84140,
   0x84144, 0x84148, 0x8414c (fp + 16, fp + 8, fp + 48, fp + 56), errpath_load2 0x8413c (fp + 28): the 80 bytes at fp
   are marked usable (trans_src_ok: a heap block's bytes by AR_laws' block shadow, else decode_rd_ok's
   range_addressable) and fp mod 8 = 0, so each 8-byte load reads one whole granule, whose shadow byte is 0;
   errpath_load1 0x83ff0, 0x84150, 0x84158 (body bytes), 0x84064 (frame[n .. len)), 0x840e8 (body bytes): every
   such byte lies in [fa, fa + len) (the body is frame[30 .. 30 + body_len) when f->code is 0, the model's rf), which
   trans_src_ok marks usable. No call keeps a byte it reads from changing: bcmp keeps every byte outside its stack
   window [sp - 48 - 2 * ESTACK, sp - 48), and decode_off_win puts both ranges outside it.
   Callee texts assumed: the bcmp wrapper as abcmp_realizes (YG0d.v) at transport_sigma
   TS___interceptor_trampoline_bcmp. Its ranges: [f->src, f->src + 6) and [f->dst, f->dst + 6) inside [fa, fa + len)
   (rf), HOST = [0x21040, 0x21046) in TRANS_RO_RD, and [M + 4, M + 10) in M. Besides the range's own shadow bytes,
   abcmp_realizes asks every shadow byte of the aligned group of 8 around them to be visible (YG0d.v shadow_hull_vis:
   the shadow of 64 bytes). HOST's group [0x7fffc208, 0x7fffc210): transport_cells gives 0x7fffc208 (6) and
   0x7fffc20c (DESK's, 6); trans_csf_cells gives the other six (HOST's and DESK's guard bytes, 0xf9). M + 4's group
   [0x800b3e28, 0x800b3e30): trans_csf_cells gives M's zero shadow (0x800b3e2c ..) and the four bytes before it
   (g_last_counter's last granule, 4, and its guard bytes, 0xf9). Each is a row of the record (lib/A/AF0m.v
   Tfib_zero_shadow, Tfib_const_shadow). No program function is called.
   Stack: 48 bytes of its own and the 2 * ESTACK the bcmp wrapper uses below sp - 48 (abcmp_realizes): CSF_STK.

   The caller is io_send (the call at 0x83084, return address 0x83088): a0 = s1 (its argument frame: g_s's
   inflight_frame or send_control's buffer), a1 = s0 (len), a2 = sp + 8 (its struct spec_frame, in its 160-byte
   machine frame, in the machine stack). It supplies the journal, the world relation and the model call from
   its own walk, the struct's fields from its inlined spec_read_frame, and trans_src_ok / decode_off_win of both
   ranges.

   Also defined here (io_send and check_inflight_retry use it): trans_sframe_at, the ASan form of
   lib/Prog/T/TContract.v sframe_at. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require TContract.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module ACells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module TCt := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.TContract.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* check_sent_frame's frame (`sp = sp - 48` at its entry; no realignment) and the 2 * ESTACK its bcmp calls use
   below sp - 48 (abcmp_realizes, YG0d.v). *)
Definition CSF_FRAME : Z := 48.
Definition CSF_STK : Z := CSF_FRAME + 2 * ESTACK.
(* No allocator event: it calls neither malloc nor free and takes no side-stack frame. *)
Definition CSF_EV : Z := 0.
(* struct spec_frame (fuzz/spec.h:188-197): 80 bytes in every build (lib/Prog/T/TContract.v). *)
Definition SF_SIZE : Z := 80.

(* The shadow facts of the record (lib/A/AF0m.v Tfib_zero_shadow and Tfib_const_shadow rows) that the bcmp calls need:
   M's payload (1648 bytes, 206 whole granules) has shadow 0, and the rest of the two aligned groups of 8 shadow bytes
   its ranges touch: HOST's (0x21040, payload 6) and DESK's (0x21060) guard granules, and g_last_counter's
   (0x5df140, payload 4) last granule and guard granules, which share M + 4's group. *)
Definition trans_csf_cells (B : asyms) : Prop :=
  decode_zshadow_at B TA_M (TA_M + TW.SZ_M) /\
  forall ly,
    In (z1 (ANum (ACells.shadow_addr (TRANS_HOST + 8))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TRANS_HOST + 16))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TRANS_HOST + 24))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TRANS_DESK + 8))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TRANS_DESK + 16))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TRANS_DESK + 24))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr TA_g_last_counter)) 4) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TA_g_last_counter + 8))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TA_g_last_counter + 16))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TA_g_last_counter + 24))) 0xf9) (as_const B ly).
Lemma trans_csf_cells_rows :
  map ACells.shadow_addr [TRANS_HOST + 8; TRANS_HOST + 16; TRANS_HOST + 24; TRANS_DESK + 8; TRANS_DESK + 16;
                          TRANS_DESK + 24; TA_g_last_counter; TA_g_last_counter + 8; TA_g_last_counter + 16;
                          TA_g_last_counter + 24; TA_M] =
  [0x7fffc209; 0x7fffc20a; 0x7fffc20b; 0x7fffc20d; 0x7fffc20e; 0x7fffc20f; 0x800b3e28; 0x800b3e29; 0x800b3e2a;
   0x800b3e2b; 0x800b3e2c].
Proof. reflexivity. Qed.

Section csf. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal := (@ajournal rc tfib_sink_head segs B).

(* A struct spec_frame at p holding the parse f of the frame bytes at fa, field by field, read through the walk's
   image view: lib/Prog/T/TContract.v sframe_at with bytes_at rsegs m replaced by garr8 of the view (the padding is
   left free, as there). p is not 0 and 8-aligned. *)
Definition trans_sframe_at (W : world segs) (memc : word -> option byte) (p fa : Z) (f : DSpec.spec_frame) : Prop :=
  0 < p /\ p mod 8 = 0 /\
  exists SB : list byte, garr8 segs (mrestrict (w_H W) memc) p (map DSpec.bz SB) /\ length SB = 80%nat /\
    TW.s32_at SB 0 = DSpec.sf_code f /\
    TW.u_at SB 8 8 = TCt.sf_ptr fa f (DSpec.sf_dst f) /\ TW.u_at SB 16 8 = TCt.sf_ptr fa f (DSpec.sf_src f) /\
    TW.u_at SB 24 2 = DSpec.sf_ethertype f /\ TW.u_at SB 26 2 = DSpec.sf_numbytes f /\
    TW.u_at SB 28 2 = DSpec.sf_sum f /\ TW.u_at SB 30 2 = DSpec.sf_retry f /\
    TW.u_at SB 32 4 = DSpec.sf_send f /\ TW.u_at SB 36 4 = DSpec.sf_ack f /\
    TW.u_at SB 40 1 = DSpec.sf_cmd f /\ TW.u_at SB 41 1 = DSpec.sf_ncmds f /\
    TW.u_at SB 48 8 = TCt.sf_ptr fa f (DSpec.sf_body f) /\ TW.u_at SB 56 8 = DSpec.sf_body_len f /\
    TW.u_at SB 64 8 = DSpec.sf_pad_len f /\ TW.u_at SB 72 2 = DSpec.sf_body_sum f.

(* What a call leaves: DgnTransportCg.v decode_cg_post with no event, no written range, no meter charge, and X: the
   model's world is the world it was given. *)
Definition transport_csf_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (Bw Bw' : list byte) : world segs -> config -> Prop :=
  @decode_cg_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs CSF_STK CSF_EV 0
    (fun _ => False) (fun _ _ _ => Bw' = Bw).

(* The contract at entry address a, in the caller-journal form. *)
Definition transport_check_sent_frame_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (fa fp : Z) (frame : list byte) (Bw Bw' : list byte),
    ajournal STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 fa -> YK11.getr regs 11 = w64 (Z.of_nat (length frame)) -> YK11.getr regs 12 = w64 fp ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - CSF_STK -> spZ regs <= sp0 ->
    0 < fa ->
    garr8 segs (mrestrict (w_H W) memc) fa (map DSpec.bz frame) ->
    trans_src_ok B lyc Sc W memc fa (Z.of_nat (length frame)) ->
    decode_off_win regs CSF_STK fa (Z.of_nat (length frame)) ->
    trans_sframe_at W memc fp fa (TC.rf frame) ->
    trans_src_ok B lyc Sc W memc fp SF_SIZE ->
    decode_off_win regs CSF_STK fp SF_SIZE ->
    trans_rom_view_rd W memc ->
    tw_at TMAP_A (aview segs (w_H W) memc) Bw ->
    TC.check_sent_frame_m Bw frame = Some (Bw', tt) ->
    st_nev S + k + CSF_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (transport_csf_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw').

(* The statement the walk will prove: the runtime cells (the shadow base through its GOT word, HOST's shadow), M's
   shadow and the rest of the bcmp ranges' shadow groups (trans_csf_cells), the two read-only facts of the record
   (they keep HOST's bytes visible through the journal), the allocator and meter laws, and the bcmp contract at the
   listing's trampoline give the contract at TS_check_sent_frame. *)
Definition transport_check_sent_frame_cg_holds_stmt : Prop :=
  transport_cells B -> trans_csf_cells B ->
  trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  AR_laws segs B -> ameter_laws MT ->
  (forall fx' : YK11.FPState, @abcmp_realizes fx' rc segs B (transport_sigma TS___interceptor_trampoline_bcmp)) ->
  transport_check_sent_frame_cg (transport_sigma TS_check_sent_frame).
End csf.
