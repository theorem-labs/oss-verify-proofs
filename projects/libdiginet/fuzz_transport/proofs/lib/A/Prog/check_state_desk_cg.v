(* check_state_desk_cg: the ASan walk contract of check_state_desk (fuzz/fuzz_transport.c:527-557; model
   lib/TModel/TCb.v check_state_desk_m) on fuzz_transport.asan (e89be137db17) at 0x8538c =
   transport_sigma TS_check_state_desk, size 684, as STATEMENTS only (no proof). It stores into no harness global and
   calls the bcmp wrapper, so it takes decode's caller-journal form (lib/A/Prog/DgnTransportCg.v decode_cg_post over
   the caller's donor journal ajournal); a G-form caller lifts it with lib/A/Prog/TransportGCg.v gx_call_cg.

   The contract. a0 = p, a struct diginet_notice n of 72 bytes (check_state_data_cg.v trans_ntc_at); Fr the current
   heap frame (check_state_data_cg.v trans_tframe_at). The memory relates to the world Bw by image A's world relation
   (TWorldG.v tw_at at TWorldA.v TMAP_A, read through aview), check_state_desk_m timg_A Fr Bw n = Some (Bw', tt)
   (lib/A/Prog/TImgA.v timg_A: SPEC_C24 0xa3da0, SPEC_PC 0xa3dc0, personalities 0xa3ea0), and the read-only bytes it
   reads (personalities[], SPEC_C24, SPEC_PC) read as the image's (trans_rom_view_rd). The function returns to ra with
   the callee-saved registers kept, no allocator event, no meter charge, every byte outside its stack window kept (it
   stores nothing outside its own frame: E is empty), and Bw' = Bw. This is what the plain contract
   (lib/Prog/T/check_state_desk_c.v) says: void; B' = B and wmem rsegs m' B; munch of the frame only. Its ntc_at /
   tframe_at / relro_img / wmem premises become trans_ntc_at / trans_tframe_at / trans_rom_view_rd / tw_at, timg_plain
   becomes timg_A, and mem_inv is dropped.

   The code, measured on the symbol-bearing twin (86efc3a80314; its loaded bytes equal the pin's), 171 words:
     0x8538c          sp = sp - 48; ra, s0 .. s4 at sp + 40 .. sp + 0 (0x85390 - 0x853a4), loaded back at 0x85598 -
                      0x855ac; no side-stack frame, no frame pointer. a0 = p throughout until 0x85480.
     0x853a8 - 0x853bc  GOT.desk (the 4-byte load at GOT + 208 = 0x5e53b0) and, a3 = OW (0x5f3060), OW.desk (OW + 208),
                      no instrumented check; OW.desk < GOT.desk (signed) goes to the trap.
     0x853c0 - 0x853c8  s4 = the 8-byte load at the GOT word 0xa4090, then at the cell 0xac9f8 it holds: the shadow
                      base 0x7fff8000 (transport_cells rows 1-2).
     each instrumented check below: the shadow byte k at (a >> 3) + 0x7fff8000; k = 0 goes on; for an n-byte load
                      (n < 8), ((a & 7) + n - 1) < k (signed) goes on; else the error path. An 8-byte load goes on only
                      at k = 0.
     0x853cc - 0x853e8  the check of the 4-byte load at p + 40 (n->mac_offset); it differs from OW.desk_off (the 4-byte
                      load at OW + 232): the trap.
     0x853ec - 0x85410  the check of the 8-byte load at p + 32 (pn = n->personality); pd = OW.desk_p (the 8-byte load at
                      OW + 240); exactly one of pn, pd is 0: the trap.
     0x85414 - 0x8547c  when pn <> 0: the checks of the 1-byte loads at pn + 16 and pd + 8 (device), then pn + 17 and
                      pd + 9 (strips); a pair that differs goes to the trap.
     0x85480 - 0x85498  the check of the 8-byte load at p + 24 (s0 = n->announce); 0 goes to the trap.
     0x8549c - 0x854e8  db = OW.desk_body (the 8-byte load at OW + 248); vn = spec_strz_len (db + 15): the checked
                      1-byte loads of db + 15 + i, i = 0 .. 8, up to the first 0 (vn = its index, or 9).
     0x854ec - 0x85538  nn = spec_strz_len (db + 24) in the same way (s1 = db + 24, s3 = nn).
     0x85540 - 0x85560  bcmp (0x42cf8 = transport_sigma TS___interceptor_trampoline_bcmp) at 0x85540 with (announce,
                      db + 15, vn); a result not 0 goes to the trap; the check of the 1-byte load at announce + vn; not
                      0 goes to the trap.
     0x85564 - 0x85594  bcmp at 0x85574 with (announce + 10, db + 24, nn); a result not 0 goes to the trap; the check of
                      the 1-byte load at announce + 10 + nn; not 0 goes to the trap; else the return at 0x855b4 (a0 not
                      stated: void).
   The trap: 0x855b8 call of before_abort (0x5a4c4), 0x855bc call of abort (0x93734); every branch to it is ruled out
   by check_state_desk_m timg_A Fr Bw n = Some _: its tests are the code's tests, read through tw_at (GOT_desk,
   OW_desk, OW_desk_off, OW_desk_p, OW_desk_body), trans_ntc_at (n's fields and the announce's bytes),
   trans_tframe_at with frame_strz_len / frame_read (the bytes at db + 15 and db + 24), trans_rom_view_rd (the image's
   bytes at personality_ptr timg_A pn + 16, + 17 and at spec_desk_at timg_A pd + 8, + 9 are the model's dp_device /
   dp_strips and d_dev / d_strips), and bcmp's result is 0 exactly when the bytes agree (abcmp_realizes).
   Error paths (11 calls) and the facts that rule them out: errpath_load4 0x855d0 (p + 40), errpath_load8 0x85630
   (p + 32), 0x85634 (p + 24): the 72 bytes at p are marked usable (trans_ntc_at's trans_src_ok) and p mod 8 = 0;
   errpath_load1 0x855f8, 0x85618 (pn + 16, + 17): pn is personalities + 24 k, k < 2 (personality_ptr timg_A pn =
   Some _), whose 48 bytes have shadow 0 (transport_cells: decode_zshadow_at TRANS_PERS); 0x85608, 0x85628 (pd + 8,
   + 9): pd is SPEC_C24 or SPEC_PC (spec_desk_at timg_A pd = Some _), 16 bytes each with shadow 0 (transport_cells);
   0x854e4, 0x85530 (db + 15 + i, db + 24 + i): inside Fr (frame_strz_len reads them from tf_bytes), which
   trans_tframe_at's trans_src_ok marks usable; 0x855dc, 0x855e8 (announce + vn, announce + 10 + nn, vn, nn <= 9):
   inside the announce's 20 bytes, which trans_ntc_at's trans_src_ok marks usable. bcmp keeps every byte outside its
   stack window [sp - 48 - 2 * ESTACK, sp - 48), which decode_off_win puts these ranges outside.
   Callee texts assumed: the bcmp wrapper as abcmp_realizes (YG0d.v) at transport_sigma
   TS___interceptor_trampoline_bcmp. Its ranges: [announce, + vn), [announce + 10, + nn) (trans_ntc_at) and
   [db + 15, + vn), [db + 24, + nn) (inside Fr). No program function is called.
   Stack: 48 bytes of its own and the 2 * ESTACK the bcmp wrapper uses below sp - 48 (abcmp_realizes): CSDESK_STK.

   The caller is notice, by the tail jump at 0x835e4 (after GOT.desk++ at 0x835c8 - 0x835d4 and its own frame given
   back: ra and sp are notice's entry values, so check_state_desk returns to notice's caller): a0 = its argument n. It
   supplies the journal, the world relation, the model call and the notice and frame facts from its own walk. *)
From Stdlib Require Import ZArith List Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportSyms DgnTransportAddr DgnTransportCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_state_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TCb TImg.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* check_state_desk's frame (`sp = sp - 48` at its entry; no realignment) and the 2 * ESTACK its bcmp calls use below
   sp - 48 (abcmp_realizes, YG0d.v). *)
Definition CSDESK_FRAME : Z := 48.
Definition CSDESK_STK : Z := CSDESK_FRAME + 2 * ESTACK.
(* No allocator event: it calls neither malloc nor free and takes no side-stack frame. *)
Definition CSDESK_EV : Z := 0.

Section csdesk. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal := (@ajournal rc tfib_sink_head segs B).

(* What a call leaves: DgnTransportCg.v decode_cg_post with no event, no written range, no meter charge, and X: the
   model's world is the world it was given. *)
Definition transport_csdesk_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (Bw Bw' : list byte) : world segs -> config -> Prop :=
  @decode_cg_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs CSDESK_STK CSDESK_EV 0
    (fun _ => False) (fun _ _ _ => Bw' = Bw).

(* The contract at entry address a, in the caller-journal form. *)
Definition transport_check_state_desk_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (p : Z) (n : TI.ntc) (Fr : option TI.tframe) (Bw Bw' : list byte),
    ajournal STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 p ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - CSDESK_STK -> spZ regs <= sp0 ->
    trans_ntc_at B lyc Sc W memc regs CSDESK_STK p n ->
    trans_tframe_at B lyc Sc W memc regs CSDESK_STK Fr ->
    trans_rom_view_rd W memc ->
    tw_at TMAP_A (aview segs (w_H W) memc) Bw ->
    TC.check_state_desk_m timg_A Fr Bw n = Some (Bw', tt) ->
    st_nev S + k + CSDESK_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (transport_csdesk_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw').

(* The statement the walk will prove: the runtime cells (the shadow base through its GOT word, the shadow of
   personalities, SPEC_C24 and SPEC_PC), the two read-only facts of the record (they keep those bytes visible through
   the journal), the allocator and meter laws, and the bcmp contract at the listing's trampoline give the contract at
   TS_check_state_desk. *)
Definition transport_check_state_desk_cg_holds_stmt : Prop :=
  transport_cells B ->
  trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  AR_laws segs B -> ameter_laws MT ->
  (forall fx' : YK11.FPState, @abcmp_realizes fx' rc segs B (transport_sigma TS___interceptor_trampoline_bcmp)) ->
  transport_check_state_desk_cg (transport_sigma TS_check_state_desk).
End csdesk.
