(* The machine contract of build_and_receive (fuzz/fuzz_transport.c:1027-1033; spec_build_frame of fuzz/spec.h
   inlined) in the plain image: an SR contract, since its callee receive allocates. *)
(* build_and_receive at 0x15be4, 412 bytes (EQUAL-mod-pcrel to the pin's, at the same address).
   addi sp,sp,-1616 at 0x15be4 (ra, s0-s8 saved; frame[SPEC_MAX_FRAME] at sp + 20). Callees: memset (0x15c8c, the
   frame from byte 12 on), memcpy (0x15c9c: src, 6 bytes; 0x15d38: the body, only when len != 0), receive (0x15d4c:
   receive(frame, n, 0, 0), Prog/T/receive_c.v). dst is read byte by byte (0x15c3c-0x15c58).
   FRAME 9856 = 1616 + receive_FRAME 8240 (memset / memcpy 0). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Contract Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TWorldMem TNeed TCb TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import TImgP WMem TContract receive_c.
Import ListNotations.
Local Open Scope Z_scope.

Definition build_and_receive_ENTRY : Z := 0x15be4.
Definition build_and_receive_FRAME : Z := 1616 + receive_FRAME.

(* The length of the frame spec_build_frame writes (TNeed.v), the n receive gets and mallocs. *)
Definition bar_len (dst src : list byte) (send ack retry cmd : Z) (body : list byte) : Z :=
  Z.of_nat (length (fst (spec_build_frame dst src send ack retry cmd 1 body 0))).

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

(* 6 bytes of a MAC table in .rodata (op_frame's DST / SRC entries and op_announce's SPEC_BCAST / DESK point
   there): read-only, so mem_inv makes every load read the image. *)
Definition h_mac_at (mem : word -> option byte) (p : Z) (mac : list byte) : Prop :=
  length mac = 6%nat /\ blk_data B mem p mac /\
  forall i, 0 <= i < 6 -> Mem.ro_addr rsegs (Z_to_bv 64 (p + i)) = true.

(* The premises of build_and_receive (dst, src, send, ack, retry, cmd, body, len) besides the budget: a0 = dst,
   a1 = src (6-byte MACs), a2 = send and a3 = ack (uint32_t: their low 32 bits), a4 = retry (uint16_t), a5 = cmd
   (uint8_t), a6 = body, a7 = len = length body (size_t), and the model premise for every heap frame a. The binary
   stores constant zeros where send's upper 16 bits and retry's upper byte go (the compiler propagated the callers'
   ranges), so send < 2^16 and retry < 2^8. The callers: op_frame (send a fuzz_u16, retry r land 3, body a take of
   the input, len <= SPEC_MAX_BODY) and op_announce (send 0, retry 0, body its 34-byte stack array), both inlined
   into LLVMFuzzerTestOneInput. *)
Definition bar_args (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte)
    (Bw : list byte) (dstp srcp bodyp : Z) (dst src body : list byte) (send ack retry cmd : Z) : Prop :=
  getr regs 10 = Z_to_bv 64 dstp /\ h_mac_at mem dstp dst /\
  getr regs 11 = Z_to_bv 64 srcp /\ h_mac_at mem srcp src /\
  bv_unsigned (getr regs 12) mod 2 ^ 32 = send /\ 0 <= send < 2 ^ 16 /\
  bv_unsigned (getr regs 13) mod 2 ^ 32 = ack /\ 0 <= ack < 2 ^ 32 /\
  getr regs 14 = Z_to_bv 64 retry /\ 0 <= retry < 2 ^ 8 /\
  getr regs 15 = Z_to_bv 64 cmd /\ 0 <= cmd < 2 ^ 8 /\
  getr regs 16 = Z_to_bv 64 bodyp /\
  getr regs 17 = Z_to_bv 64 (Z.of_nat (length body)) /\
  blk_data B mem bodyp body /\
  h_src L A (spZ regs) bodyp (Z.of_nat (length body)) /\
  (forall a, h_addr_ok a -> build_and_receive_m timg_plain Bw a dst src send ack retry cmd body <> None).

(* What build_and_receive returns in: receive's heap frame a (below alloc_ceiling, off the image), the world the
   model gives at it. *)
Definition bar_ret (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (b : sbound) (Bw : list byte) (dst src body : list byte) (send ack retry cmd : Z) (c' : config) : Prop :=
  exists (a : Z) (Bw' : list byte),
    h_addr_ok a /\ a + Z.max 1 (bar_len dst src send ack retry cmd body) <= alloc_ceiling /\
    (forall i, 0 <= i < Z.max 1 (bar_len dst src send ack retry cmd body) -> ~ in_img B (a + i)) /\
    build_and_receive_m timg_plain Bw a dst src send ack retry cmd body = Some (Bw', tt) /\
    h_post B API build_and_receive_FRAME
      (fun x => h_world x \/ a <= x < a + Z.max 1 (bar_len dst src send ack retry cmd body) \/
                ms_ctx B <= x < ms_ctx B + CTX_SIZE)
      L A regs mem md b Bw' c'.

Definition build_and_receive_contract : Prop :=
  h_binds B API ->
  forall L A regs mem md b (Bw : list byte) (dstp srcp bodyp : Z) (dst src body : list byte)
         (send ack retry cmd : Z),
    h_pre B API build_and_receive_FRAME L A regs mem md b Bw ->
    frm_zero fp_csr ->
    bar_args L A regs mem Bw dstp srcp bodyp dst src body send ack retry cmd ->
    room_slots b (Z.max 1 (bar_len dst src send ack retry cmd body)) ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 build_and_receive_ENTRY) mem (seg_rom segs)) md)
      (bar_ret L A regs mem md b Bw dst src body send ack retry cmd).

End K.
