(* spec_read_frame_cg: the ASan walk contract of spec_read_frame (fuzz/spec.h:199-223, with spec_be16 / spec_be32 /
   spec_sum inlined; model lib/Spec/DgnSpec.v spec_read_frame, the struct's 80 bytes lib/Prog/T/TContract.v sf_bytes)
   on fuzz_transport.asan-ubsan (41113a03c82f) at 0x839c0 = transportb_sigma TB_spec_read_frame, size 1728, as
   STATEMENTS only (no proof). Image B only: image A's and the plain image's io_send, m_rx and receive inline it, so no
   plain contract or image-A statement of this function exists. It stores into no harness global, calls __asan_memset
   and writes the struct spec_frame its caller passes by address in the CALLER's own machine frame (each of its three
   callers takes no side-stack frame). So it takes the G-form caller-journal form with one out cell: the caller's
   journal is lib/A/W_journalG.v ajournal_gx over G = lib/B/TransportGB.v G_HARNESS_B with no out cell (XO = 0,
   OUT = []), and the post is lib/A/Prog/TransportGCg.v transport_cg_post_out with outs = [(fp, 80)] (acall_kept_g read
   at the memory with the 80 bytes at fp put back as they were at the call; X says what they hold), the form this unit
   fixed for image B. Form: the nearest image-A sibling of that form, lib/A/Prog/check_latest_sent_cg.v (a G-form
   walk that writes one cell of its caller's machine frame: the write right transport_twr_ok_g, decode_rd_ok,
   decode_off_win and ~ inG of the cell; the read range apart from every byte the call stores; the post's out cell),
   with the frame premises of lib/A/Prog/check_sent_frame_cg.v (the frame bytes at fa read through garr8 +
   trans_src_ok + decode_off_win) and the struct of its trans_sframe_at, here all 80 bytes (sf_bytes: the memset
   zeroes the padding).

   The contract. a0 = b, the frame bytes frame at b (not 0); a1 = len, 0 <= len <= length frame (io_send passes the
   whole frame, receive its whole heap copy or its first 1514 bytes, m_rx the n it was given); a2 = fp, 8-aligned, the
   caller's struct spec_frame of 80 bytes (SRF_SIZE). The frame's first len bytes are placed by trans_src_ok (a heap
   block, a caller's side-stack or machine frame, or a harness global: io_send's frame may be g_s.inflight_frame) and
   outside this call's stack window (decode_off_win), and lie apart from the struct; the struct carries the write right
   transport_twr_ok_g, decode_rd_ok (its shadow bytes are read by the instrumented stores and by __asan_memset), lies
   outside this call's stack window and outside G. The function returns to ra with a0 = sf_code f (f = DgnSpec
   spec_read_frame (zs frame) len, srf_f: SPEC_OK 0, SPEC_E_SHORT -2, SPEC_E_ETHERTYPE -3 or SPEC_E_LENGTH -4,
   sign-extended), the callee-saved registers kept, no allocator event, no meter charge, the caller's side-stack frames
   and blocks exactly, the 80 bytes at fp holding TContract.sf_bytes b f (the fields of f, the pointers b + 0, b + 6,
   b + 30 when the code is SPEC_OK and 0 else, every padding byte 0), every byte of G as it was (gx_kept: it writes no
   harness global), and every other byte acall_kept_g keeps outside the struct (srf_wr fp). At len = length frame, f is
   TCb.rf frame (srf_f_rf).

   The code, measured on the symbol-bearing twin (e217cb0a84f1; its loaded bytes equal the pin's but the ELF header's
   section-table fields and the build-id note, and the 1728 code bytes of this function are equal in both files),
   432 words:
     0x839c0 - 0x839d4  sp = sp - 48; ra, s0 .. s3 at sp + 40 .. sp + 8, loaded back at 0x83e88 - 0x83e98 (sp = sp + 48
                      at 0x83e9c, return at 0x83ea0); sp + 0 .. sp + 7 unused. No side-stack frame, no frame pointer.
                      s0 = fp, s1 = len, s2 = b.
     0x839e0 - 0x839e8  s3 = the 8-byte load at the GOT word 0xa3cf0, then at the cell 0xac678 it holds: the shadow base
                      0x7fff8000 (transport_cells rows 1-2).
     0x839ec - 0x839fc  __asan_memset (0x52888 = transportb_sigma TB___asan_memset) at 0x839fc with (fp, 0, 80), return
                      address 0x83a00 (spec.h:201).
     each instrumented check below: the shadow byte k at (a >> 3) + 0x7fff8000; k = 0 goes on; for an n-byte access
                      (n < 8), ((a & 7) + n - 1) < k (signed) goes on; else the error path. An 8-byte store goes on only
                      at k = 0.
     0x83a00 - 0x83a14  len < 30 (len <= 29, unsigned): fp & 7 <> 0 goes to the trap word; a0 = -2 (SPEC_E_SHORT) and
                      the code store at 0x83e74.
     0x83a18 - 0x83a34  the UBSan checks before b[12]: b = 0, b >= 2^64 - 12, b + 12 = 2^64 - 1 (b + 13 wraps), and
                      fp & 7 <> 0 go to the trap word.
     0x83a38 - 0x83a8c  the checks of the 1-byte loads at b + 12 and b + 13 and of the 2-byte store at fp + 24; the two
                      bytes; ethertype = b[12] << 8 | b[13], stored at fp + 24 (0x83a88); ethertype <> 0x885f
                      (SPEC_ETHERTYPE) goes to 0x83e70: a0 = -3 (SPEC_E_ETHERTYPE) and the code store.
     0x83a90 - 0x83af0  the UBSan checks (b + 14, b + 15 wrap: the trap word); the checks of the loads at b + 14, b + 15
                      and of the 2-byte store at fp + 26; numbytes = b[14] << 8 | b[15], stored at fp + 26 (0x83af0).
     0x83af4 - 0x83b00  a0 = -4 (SPEC_E_LENGTH); numbytes < 16, or len - 14 < numbytes (unsigned), goes to the code
                      store.
     0x83b04 - 0x83b40  the checks of the 8-byte stores at fp + 8 and fp + 16; dst = b stored at fp + 8 (0x83b20); b + 6
                      below 7 (b + 6 wraps) goes to the trap word; src = b + 6 stored at fp + 16 (0x83b40).
     0x83b44 - 0x83ba0  (b + 16, b + 17 wrap: the trap word) sum = b[16] << 8 | b[17], stored at fp + 28 (0x83ba0).
     0x83ba4 - 0x83c4c  (b + 18 .. b + 21 wrap: the trap word) send = b[18] << 24 | b[19] << 16 | b[20] << 8 | b[21],
                      stored at fp + 32 (0x83c4c, 4 bytes).
     0x83c50 - 0x83cf8  (b + 22 .. b + 25 wrap: the trap word) ack = the same of b[22 .. 25], stored at fp + 36 (0x83cf8).
     0x83cfc - 0x83d58  (b + 26, b + 27 wrap: the trap word) retry = b[26] << 8 | b[27], stored at fp + 30 (0x83d58).
     0x83d5c - 0x83d90  (b + 28 wraps: the trap word) cmd = b[28], stored at fp + 40 (0x83d90, 1 byte).
     0x83d94 - 0x83dc8  (b + 29 wraps: the trap word) ncmds = b[29], stored at fp + 41 (0x83dc8, 1 byte).
     0x83dcc - 0x83e24  (b + 30 wraps: the trap word) the checks of the 8-byte stores at fp + 48, fp + 56, fp + 64;
                      body = b + 30 (s2) stored at fp + 48 (0x83dec); body_len = numbytes - 16 at fp + 56 (0x83e08);
                      pad_len = len - numbytes - 14 at fp + 64 (0x83e24).
     0x83e28 - 0x83e60  body_sum: body_len = 0 gives 0 (0x83ea4); else for i = 0 .. body_len - 1: the bitwise not of
                      b + 30 below i (b + 30 + i wraps) goes to the trap word; the check of the 1-byte load at
                      b + 30 + i; the byte added to a2 (64 bits).
     0x83ea8 - 0x83ec4  the check of the 2-byte store at fp + 72; the low 16 bits of a2 stored at fp + 72 (0x83ec0)
                      (spec_sum's sum mod 2^16, step by step); a0 = 0 (SPEC_OK).
     0x83e74 - 0x83e84  the code store, on every path: the check of the 4-byte store at fp, the low 32 bits of a0 stored
                      at fp (0x83e84); then the return with a0 = the code (sign-extended).
     0x83ec8          the word 0xc0001073 (unimp: a write of the read-only CSR cycle, an illegal instruction that traps):
                      the trap path, reached by the 22 UBSan branches at 0x83a0c, 0x83a18, 0x83a20, 0x83a2c, 0x83a34,
                      0x83a94, 0x83aa0, 0x83b24, 0x83b44, 0x83b50, 0x83ba4, 0x83bc0, 0x83be4, 0x83c50, 0x83c6c, 0x83c90,
                      0x83cfc, 0x83d08, 0x83d5c, 0x83d94, 0x83dcc, 0x83e38.
   The stores of the struct's fields are in spec.h's order (ethertype and numbytes before their tests); every field
   the code does not store keeps the memset's 0, so the 80 bytes are sf_bytes b f on each of the four returns: the
   model's zero record of each error code (ethertype stored on SPEC_E_ETHERTYPE and SPEC_E_LENGTH, numbytes on
   SPEC_E_LENGTH) and its SPEC_OK record.
   Trap path and the facts that rule it out: fp & 7 <> 0 by fp mod 8 = 0 (the UBSan alignment check of the struct's
   members); b = 0 by 0 < b; every wrap test of b + j (j <= 30) and b + 30 + i (i < body_len) is reached only at
   len >= 30, with b + j <= b + len (j <= 15 before the length test; past it, 30 + body_len = numbytes + 14 <= len) and
   b + 30 + i < b + len, and trans_src_ok places [b, b + len) below 2^64 (decode_rd_ok: b + len <= 2^63; a heap block:
   below the allocator's ceiling). fp mod 8 = 0 and 0 < b are the two premises the UBSan checks ask for.
   Error paths (34 calls) and the facts that rule them out:
     __asan_report_load1 (0x59504 = TB___asan_report_load1) at 0x83ee8, 0x83ef8, 0x83f14, 0x83f24, 0x83f40, 0x83f50,
       0x83f6c, 0x83f7c, 0x83f88, 0x83f98, 0x83fb4, 0x83fc4, 0x83fd0, 0x83fe0, 0x83ffc, 0x8400c, 0x84028, 0x84044
       (b + 12 .. b + 29) and 0x83e6c (b + 30 + i): each byte lies in [b, b + len), which trans_src_ok marks usable (a
       heap block: AR's block shadow; else decode_rd_ok's range_addressable);
     __asan_report_store1 (0x59824) at 0x84038, 0x84054 (fp + 40, fp + 41), __asan_report_store2 (0x598c4) at 0x83f08,
       0x83f34, 0x83f60, 0x8401c, 0x84068 (fp + 24, + 26, + 28, + 30, + 72), __asan_report_store4 (0x59964) at 0x83fa8,
       0x83ff0, 0x83edc (fp + 32, + 36, fp), __asan_report_store8 (0x59a04) at 0x8406c, 0x84070, 0x84074, 0x84078,
       0x8407c (fp + 8, + 16, + 48, + 56, + 64): the 80 bytes at fp are marked usable (decode_rd_ok's
       range_addressable) and fp mod 8 = 0, so each access lies in one granule whose shadow byte is 0 or above its last
       byte's offset.
   __asan_memset keeps every byte outside [fp, fp + 80) and its stack window [sp - 48 - ESTACK, sp - 48) (YG0d.v
   aintrin_realizes), and the frame bytes lie apart from both (the disjointness premise, decode_off_win); the field
   stores touch only [fp, fp + 80). So each frame byte the code reads is the one at entry (garr8 of frame), and the
   loaded values are the model's (DgnSpec spec_be16 / spec_be32 / byte_at of zs frame; spec_sum_at's sum mod 2^16).
   Callee texts assumed: __asan_memset as aintrin_realizes ... OSet (transportb_sigma TB___asan_memset), which the
   walk applies from its G journal through TransportGCg.v gx_intrin_at (destination [fp, fp + 80): each byte a present
   awr_byte of the caller's window, transport_twr_ok_g). No program function is called.
   Stack: 48 bytes of its own and the ESTACK __asan_memset uses below sp - 48 (YG0d.v aintrin_realizes' ecall_pre):
   SRF_STK.

   The callers, each passing a struct in its own machine frame (none of them takes a side-stack frame):
     io_send, the call at 0x83050 (return address 0x83054; DgnTransportBList.v PCall TB_spec_read_frame): a0 = s1 (its
       argument frame: g_s.inflight_frame or a sender's buffer), a1 = s0 (its length), a2 = io_send's sp + 8;
     receive, the calls at 0x8374c (return address 0x83750; a1 = n) and 0x83778 (return address 0x8377c; a1 = the
       lesser of n and 1514): a0 = s0 (the heap copy of its n input bytes), a2 = receive's sp + 0;
     m_rx, the call at 0x84c40 (return address 0x84c44): a0, a1 = m_rx's own a0, a1 (the received frame and its n),
       a2 = m_rx's sp + 0.
   Each supplies the G journal of its own walk, the frame's placement and bytes, and the struct's write right. *)
From Stdlib Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBAddr DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require TContract.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module TCt := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.TContract.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* spec_read_frame's frame (`sp = sp - 48` at its entry; no realignment) and the ESTACK its only callee,
   __asan_memset, uses below sp - 48. *)
Definition SRF_FRAME : Z := 48.
Definition SRF_STK : Z := SRF_FRAME + ESTACK.
(* No allocator event: it calls neither malloc nor free and takes no side-stack frame. *)
Definition SRF_EV : Z := 0.
(* struct spec_frame (fuzz/spec.h:188-197): 80 bytes in every build (lib/Prog/T/TContract.v). *)
Definition SRF_SIZE : Z := 80.
Lemma srf_size_bytes : forall fa f, Z.of_nat (length (TCt.sf_bytes fa f)) = SRF_SIZE.
Proof. intros fa f. reflexivity. Qed.
(* The record the code fills: the model's parse of the first len bytes of frame; at len = length frame it is
   TCb.rf frame. *)
Definition srf_f (frame : list byte) (len : Z) : DSpec.spec_frame := DSpec.spec_read_frame (TW.zs frame) len.
Lemma srf_f_rf : forall frame, srf_f frame (Z.of_nat (length frame)) = TC.rf frame.
Proof. intros frame. reflexivity. Qed.
(* The bytes the code stores: the struct's 80 bytes (the memset, then the field stores). *)
Definition srf_wr (fp a : Z) : Prop := fp <= a < fp + SRF_SIZE.

Section srf. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* What a call leaves: TransportGCg.v transport_cg_post_out over G_HARNESS_B with the one out cell [(fp, SRF_SIZE)],
   no event, the written range srf_wr fp, no meter charge, and X: a0 = the code, the 80 bytes at fp holding
   sf_bytes b f, and every byte of G as it was. *)
Definition transport_srf_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (b fp : Z) (f : DSpec.spec_frame) : world segs -> config -> Prop :=
  @transport_cg_post_out fx rc tfib_sink_head segs B MT TG.G_HARNESS_B [(fp, SRF_SIZE)]
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs SRF_STK SRF_EV 0 (srf_wr fp)
    (fun regs2 W2 mem2 =>
       YK11.getr regs2 10 = w64 (DSpec.sf_code f) /\
       garr8 segs (mrestrict (w_H W2) mem2) fp (TW.zs (TCt.sf_bytes b f)) /\
       gx_kept segs TG.G_HARNESS_B W memc W2 mem2).

(* The contract at entry address a, in the G-form caller-journal form. *)
Definition transport_spec_read_frame_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (b len fp : Z) (frame : list byte),
    ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 b -> YK11.getr regs 11 = w64 len -> YK11.getr regs 12 = w64 fp ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - SRF_STK -> spZ regs <= sp0 ->
    0 < b -> 0 <= len <= Z.of_nat (length frame) ->
    garr8 segs (mrestrict (w_H W) memc) b (TW.zs frame) ->
    trans_src_ok B lyc Sc W memc b len ->
    decode_off_win regs SRF_STK b len ->
    (forall x, b <= x < b + len -> ~ srf_wr fp x) ->
    fp mod 8 = 0 ->
    transport_twr_ok_g segs B TG.G_HARNESS_B STK sp0 FP ly S lyc Sc own W memc (spZ regs) fp SRF_SIZE ->
    decode_rd_ok W memc fp SRF_SIZE ->
    decode_off_win regs SRF_STK fp SRF_SIZE ->
    (forall x, fp <= x < fp + SRF_SIZE -> ~ inG TG.G_HARNESS_B x) ->
    st_nev S + k + SRF_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (transport_srf_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b fp (srf_f frame len)).

(* The statement the walk will prove: the runtime cells (the shadow base through its GOT word), the allocator and
   meter laws, G inside the image and outside the allocator's statics, and the contract of __asan_memset give the
   contract at TB_spec_read_frame. *)
Definition transport_spec_read_frame_cg_holds_stmt : Prop :=
  transport_cells B ->
  AR_laws segs B -> ameter_laws MT ->
  gx_ok segs B TG.G_HARNESS_B ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OSet (transportb_sigma TB___asan_memset)) ->
  transport_spec_read_frame_cg (transportb_sigma TB_spec_read_frame).
End srf.
