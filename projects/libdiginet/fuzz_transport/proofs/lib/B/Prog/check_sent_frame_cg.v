(* check_sent_frame_cg: the ASan walk contract of check_sent_frame (fuzz/fuzz_transport.c:398-420; model
   lib/TModel/TCb.v check_sent_frame_m) on fuzz_transport.asan-ubsan (41113a03c82f) at 0x84080 =
   transportb_sigma TB_check_sent_frame, size 852, as STATEMENTS only (no proof). It stores into no harness global and
   calls the bcmp wrapper, so it takes decode's caller-journal form (lib/B/Prog/DgnTransportBCg.v decode_cg_post over
   the caller's donor journal ajournal); a G-form caller lifts it with lib/A/Prog/TransportGCg.v gx_call_cg (stated
   over any segments, record and G, so image B's walks use it too). Image B's twin of
   lib/A/Prog/check_sent_frame_cg.v: the same statement at image B's world table, cells and listing; the differences
   image B's code forces are listed at the end of this comment.

   The contract. a0 = fa, the len bytes frame (a1 = len = length frame); a2 = fp, the struct spec_frame of 80 bytes
   that holds the parse TCb.rf frame of the bytes at fa, field by field (trans_sframe_at: TContract.sframe_at read
   through the walk's image view). The bytes at fa may lie in a harness global (g_s.inflight_frame), a caller's frame
   or a heap block, and the struct in the caller's machine frame: trans_src_ok of both ranges, both outside this
   call's stack window (decode_off_win). The memory relates to the world Bw by image B's world relation
   (lib/A/Prog/TWorldG.v tw_at at lib/B/Prog/TWorldB.v TMAP_B, read through aview), check_sent_frame_m Bw frame =
   Some (Bw', tt), and the read-only bytes it compares (HOST) read as the image's (trans_rom_view_rd). The function
   returns to ra with the callee-saved registers kept, no allocator event, no meter charge, every byte outside its
   stack window kept (it stores nothing outside its own frame: E is empty), and Bw' = Bw. This is what the plain
   contract (lib/Prog/T/check_sent_frame_c.v) says: void; B' = B and wmem rsegs m' B; munch of the frame only. Its
   bytes_at / off_window / sframe_at / wmem / mem_inv premises become garr8 + trans_src_ok + decode_off_win /
   trans_sframe_at / tw_at, and mem_inv is dropped.

   The code, measured on the symbol-bearing twin (e217cb0a84f1; its loaded bytes equal the pin's but the ELF header's
   section-table fields and the build-id note, and the 852 code bytes of this function are equal in both files),
   213 words:
     0x84080          sp = sp - 48; ra, s0 .. s3 at sp + 40 .. sp + 8 (0x84084 - 0x84094), loaded back at 0x84368 -
                      0x84378; no side-stack frame, no frame pointer. s1 = len (0x84098), s0 = fp, s2 = fa
                      (0x840a4 - 0x840a8).
     0x8409c - 0x840a0  fp & 7 <> 0 goes to the unimp word at 0x84384 (the ubsan build's alignment check).
     0x840ac - 0x840b4  s3 = the 8-byte load at the GOT word 0xa3cf0 (GOT_CELL_K), then at the cell 0xac678 (CELL_K)
                      it holds: the shadow base 0x7fff8000 (transport_cells rows 1-2).
     each instrumented check below: the shadow byte k at (a >> 3) + 0x7fff8000; k = 0 goes on; for an n-byte load
                      (n < 8), ((a & 7) + n - 1) < k (signed) goes on; else the error path. An 8-byte load goes on only
                      at k = 0.
     0x840b8 - 0x840cc  the check of the 4-byte load at fp, then f->code (fp + 0); not 0 goes to the trap.
     0x840d0 - 0x840f8  the check of the 8-byte load at fp + 16 and f->src; bcmp (0x42d34 = transportb_sigma
                      TB___interceptor_trampoline_bcmp) at 0x840f4 with (f->src, HOST = 0x20fe0 = TRANS_HOST, 6); a
                      result not 0 goes to the trap.
     0x840fc - 0x84108  the 4-byte load of M.desk_known at M = 0x5dede0 (no instrumented check); 0 goes to the trap.
     0x8410c - 0x84130  the check of the 8-byte load at fp + 8 and f->dst; bcmp at 0x8412c with (f->dst, M + 4 =
                      0x5dede4 (M.desk), 6); a result not 0 goes to the trap.
     0x84134 - 0x84160  the checks of the 8-byte loads at fp + 48 and fp + 56: a2 = f->body_len, a3 = f->body.
     0x84164 - 0x84230  spec_system_at, inlined: when body_len >= 4, for i = 0 .. body_len - 4 the checked 1-byte
                      loads of body[i], body[i + 1], body[i + 3]; the pattern 0xf0, 0x13, _, 0x70 at some i goes to the
                      trap (bgez at 0x84230). Before them, the ubsan build's pointer checks go to the unimp word at
                      0x84384: body + i < body (unsigned, 0x84190: the sum wraps), (body <> 0) = (body + i = 0)
                      (0x8419c), body = 0 (0x841a0), i >= 2 ^ 64 - 1 - body (unsigned, 0x841c4: body + i + 1 wraps),
                      2 ^ 64 - 1 - body < i + 3 (unsigned, 0x841e4: body + i + 3 wraps).
     0x84234 - 0x84244  n = body_len + 30; a1 = n when n > 60, else 60.
     0x84248 - 0x842c4  when n < len, the checked 1-byte loads of frame[n .. len) (at fa + n + j), all 0 or not; before
                      each, fa + n + j < fa (unsigned, 0x84268), (fa <> 0) = (fa + n + j = 0) (0x84274) or fa = 0
                      (0x84278) goes to the unimp word.
     0x842c8 / 0x842cc  len <> a1 goes to the trap; a byte of frame[n .. len) not 0 goes to the trap.
     0x842d0 - 0x842e4  the check of the 2-byte load at fp + 28 and f->sum.
     0x842e8 - 0x84360  want = 0 when body_len = 0 or g_cfg.sum_mode (the 4-byte load at g_cfg + 20 = 0x5ded14, no
                      instrumented check) is 1; else the low 16 bits of the sum of the checked 1-byte loads of
                      body[0 .. body_len); before each, body + i < body (unsigned, 0x84310), (body <> 0) =
                      (body + i = 0) (0x8431c) or body = 0 (0x84320) goes to the unimp word.
     0x84364          f->sum <> want goes to the trap; else the return at 0x84380 (a0 not stated: void).
   The trap: 0x84388 call of __asan_handle_no_return (0x5a500, TB___asan_handle_no_return), 0x8438c call of abort
   (0x93390, TB_abort), then 0x84390 the word 0xc0001073 (unimp: a write of the read-only CSR cycle, an illegal
   instruction that traps); every branch to it is ruled out by check_sent_frame_m Bw frame = Some _: its tests are the
   code's tests, read through tw_at (M.desk_known, M.desk, g_cfg.sum_mode), trans_sframe_at (the struct's fields are
   those of rf frame) and the bcmp results (0 exactly when the bytes agree, abcmp_realizes).
   The unimp word at 0x84384 (the ubsan build's checks) and the facts that rule out each branch to it: 0x840a0:
   trans_sframe_at's fp mod 8 = 0; the body pointer checks (0x84190 - 0x841e4, 0x84310 - 0x84320): f->body is
   sf_ptr fa (rf frame) (sf_body (rf frame)) = fa + sf_body (rf frame) once f->code is 0 (trans_sframe_at, the test at
   0x840cc), with 0 < fa, and every body byte the loops address lies in [fa, fa + len) (the body is
   frame[30 .. 30 + body_len), the model's rf), with fa + len <= 2 ^ 63 (trans_src_ok); the frame pointer checks
   (0x84268 - 0x84278): 0 < fa and fa + n + j < fa + len <= 2 ^ 63.
   Error paths (11 calls) and the facts that rule them out: __asan_report_load4 (0x59644) at 0x843a0 (fp),
   __asan_report_load8 (0x596e4) at 0x843b4, 0x843b8, 0x843bc, 0x843c0 (fp + 16, fp + 8, fp + 48, fp + 56),
   __asan_report_load2 (0x595a4) at 0x843b0 (fp + 28): the 80 bytes at fp are marked usable (trans_src_ok: a heap
   block's bytes by AR_laws' block shadow, else decode_rd_ok's range_addressable) and fp mod 8 = 0, so each 8-byte load
   reads one whole granule, whose shadow byte is 0; __asan_report_load1 (0x59504) at 0x843c8, 0x843d0, 0x8422c (body
   bytes), 0x842b8 (frame[n .. len)), 0x84358 (body bytes): every such byte lies in [fa, fa + len) (the body is
   frame[30 .. 30 + body_len) when f->code is 0, the model's rf), which trans_src_ok marks usable. No call keeps a byte
   it reads from changing: bcmp keeps every byte outside its stack window [sp - 48 - 2 * ESTACK, sp - 48), and
   decode_off_win puts both ranges outside it.
   Callee texts assumed: the bcmp wrapper as abcmp_realizes (YG0d.v) at transportb_sigma
   TB___interceptor_trampoline_bcmp. Its ranges: [f->src, f->src + 6) and [f->dst, f->dst + 6) inside [fa, fa + len)
   (rf), HOST = [0x20fe0, 0x20fe6) in TRANS_RO_RD, and [M + 4, M + 10) in M. Besides the range's own shadow bytes,
   abcmp_realizes asks every shadow byte of the aligned group of 8 around them to be visible (YG0d.v shadow_hull_vis:
   the shadow of 64 bytes). HOST's group [0x7fffc1f8, 0x7fffc200): transport_cells gives 0x7fffc1fc (HOST's, 6);
   trans_csf_cells gives the other seven (the guard bytes of SCALE (0x20fa0, payload 32) and of HOST, 0xf9). M + 4's
   group [0x800b3db8, 0x800b3dc0): trans_csf_cells gives M's zero shadow (0x800b3dbc ..) and the four bytes before it
   (g_last_counter's last granule, 4, and its guard bytes, 0xf9). Each is a row of the record (lib/B/YF0m.v
   Tfib_zero_shadow, Tfib_const_shadow). No program function is called.
   Stack: 48 bytes of its own and the 2 * ESTACK the bcmp wrapper uses below sp - 48 (abcmp_realizes): CSF_STK.

   The caller is io_send (the call at 0x83060, return address 0x83064): a0 = s1 (its argument frame: g_s's
   inflight_frame or send_control's buffer), a1 = s0 (len), a2 = sp + 8 (its struct spec_frame, in its 160-byte
   machine frame, in the machine stack). It supplies the journal, the world relation and the model call from
   its own walk, the struct's fields from its call of spec_read_frame (0x839c0, the call at 0x83050; image A inlines
   spec_read_frame into io_send), and trans_src_ok / decode_off_win of both ranges.

   Also defined here (io_send and check_inflight_retry use it): trans_sframe_at, the ASan form of
   lib/Prog/T/TContract.v sframe_at.

   Against image A's statement (lib/A/Prog/check_sent_frame_cg.v): the same premises, post and holds statement, at
   image B's names (TMAP_B, TB_M, TB_g_last_counter, transportb_sigma, lib/B/Prog/DgnTransportBCg.v). What image B's
   code forces: the branches to the unimp word (the ubsan build's checks; image A has none), ruled out by premises the
   statement already has (trans_sframe_at, 0 < fa, trans_src_ok), so no premise is added; trans_csf_cells names the
   rows of HOST's shadow group that image B's layout puts there: HOST (0x20fe0) sits in the middle of its group, after
   SCALE's guard bytes, where image A's HOST (0x21040) starts its group and DESK's shadow fills the rest; the error
   paths are direct calls of the runtime's report entries (image A's file names them errpath_load1 .. errpath_load8).
   *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require TContract.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module BCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
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

(* The shadow facts of the record (lib/B/YF0m.v Tfib_zero_shadow and Tfib_const_shadow rows) that the bcmp calls need:
   M's payload (1648 bytes, 206 whole granules) has shadow 0, and the rest of the two aligned groups of 8 shadow bytes
   its ranges touch: SCALE's (0x20fa0, payload 32) guard granules before HOST (0x20fe0, payload 6) and HOST's guard
   granules, which share HOST's group, and g_last_counter's (0x5dedc0, payload 4) last granule and guard granules,
   which share M + 4's group. *)
Definition trans_csf_cells (B : asyms) : Prop :=
  decode_zshadow_at B TB_M (TB_M + TW.SZ_M) /\
  forall ly,
    In (z1 (ANum (BCells.shadow_addr (TRANS_SCALE + 32))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TRANS_SCALE + 40))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TRANS_SCALE + 48))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TRANS_SCALE + 56))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TRANS_HOST + 8))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TRANS_HOST + 16))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TRANS_HOST + 24))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr TB_g_last_counter)) 4) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TB_g_last_counter + 8))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TB_g_last_counter + 16))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TB_g_last_counter + 24))) 0xf9) (as_const B ly).
Lemma trans_csf_cells_rows :
  map BCells.shadow_addr [TRANS_SCALE + 32; TRANS_SCALE + 40; TRANS_SCALE + 48; TRANS_SCALE + 56; TRANS_HOST + 8;
                          TRANS_HOST + 16; TRANS_HOST + 24; TB_g_last_counter; TB_g_last_counter + 8;
                          TB_g_last_counter + 16; TB_g_last_counter + 24; TB_M] =
  [0x7fffc1f8; 0x7fffc1f9; 0x7fffc1fa; 0x7fffc1fb; 0x7fffc1fd; 0x7fffc1fe; 0x7fffc1ff; 0x800b3db8; 0x800b3db9;
   0x800b3dba; 0x800b3dbb; 0x800b3dbc].
Proof. reflexivity. Qed.

Section csf. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
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

(* What a call leaves: DgnTransportBCg.v decode_cg_post with no event, no written range, no meter charge, and X: the
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
    tw_at TMAP_B (aview segs (w_H W) memc) Bw ->
    TC.check_sent_frame_m Bw frame = Some (Bw', tt) ->
    st_nev S + k + CSF_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (transport_csf_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw').

(* The statement the walk will prove: the runtime cells (the shadow base through its GOT word, HOST's shadow), M's
   shadow and the rest of the bcmp ranges' shadow groups (trans_csf_cells), the two read-only facts of the record
   (they keep HOST's bytes visible through the journal), the allocator and meter laws, and the bcmp contract at the
   listing's trampoline give the contract at TB_check_sent_frame. *)
Definition transport_check_sent_frame_cg_holds_stmt : Prop :=
  transport_cells B -> trans_csf_cells B ->
  trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  AR_laws segs B -> ameter_laws MT ->
  (forall fx' : YK11.FPState, @abcmp_realizes fx' rc segs B (transportb_sigma TB___interceptor_trampoline_bcmp)) ->
  transport_check_sent_frame_cg (transportb_sigma TB_check_sent_frame).
End csf.
