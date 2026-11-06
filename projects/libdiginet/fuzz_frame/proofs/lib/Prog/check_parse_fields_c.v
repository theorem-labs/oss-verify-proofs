(* Contract of check_parse_fields in fuzz_frame.plain, and the struct spec_frame that
   LLVMFuzzerTestOneInput gives to the check functions.
   Source: fuzz/fuzz_frame.c:65-112 at 835f336c.
   Address 0x12eec, size 364 bytes. Stack frame: 48 bytes (addi sp, sp, -0x30 at 0x12eec). The
   function calls bcmp (0x1b828) three times, diginet_mac_is_digidesign (0x13690) and
   diginet_frame_is_keepalive (0x136c0). None of them uses stack: their contracts write no
   byte below sp. It calls abort (0x14414) at 0x13054. CPF_STACK is 48.
   Arguments: a0 is the address buf of the frame, a1 the address f of a struct diginet_frame
   (64 bytes), a2 the address w of a struct spec_frame (80 bytes). The caller is
   LLVMFuzzerTestOneInput, at 0x12e4c, only for a frame b with fr_code b = 0. It gives its copy
   of the input (a heap block of exactly the input size), its local frame struct at sp + 0x50
   and its local spec_frame at sp.
   Preconditions:
   - fr_code b = 0, for the bytes b at buf; f is not 0;
   - the bytes b at buf are readable (bytes_at);
   - the 64 bytes at f are parse_cells buf b fj (diginet_frame_parse_c.v), the struct that
     diginet_frame_parse writes (ro_cells);
   - the 80 bytes at w are spec_cells buf b (below), the struct that the inlined
     spec_read_frame writes (ro_cells);
   - the bytes at buf, f and w are not in the 48 bytes below sp;
   - the stack from lo to sp is writable (stk), and lo + 48 <= sp;
   - mem_inv holds.
   Result: the function returns to ra. It does not call abort: each test compares a value in f
   with the same value in w, and the libdiginet model (DgnSpec, DgnLib) reads both from b:
   - the header fields numbytes, sum, send, ack, retry, cmd and ncmds (0x12f0c..0x12f60);
   - bcmp of the 6 bytes at f and at w->dst = buf, and at f + 6 and at w->src = buf + 6
     (0x12f64..0x12f8c), then the EtherType;
   - diginet_mac_is_digidesign (f + 6) answers oui_of (fr_src b), and bcmp compares the 3
     bytes at w->src with SPEC_OUI, the bytes 00 a0 7e at 0x1038f in .rodata
     (DgnSpec.oui_of_firstn);
   - body = buf + 30, body_len, pad_len, body_sum, and sum_matches = (w->sum == body_sum);
   - diginet_frame_is_keepalive (f) answers fr_keepalive b (keepalive_of), the harness's own
     test. The binary tests f->body_len == 1 first, then w->cmd == 0, then reads w->body[0];
     body_len is 1 there, so the byte buf + 30 is in b.
   The function writes only the 48 bytes below sp. It can change t0..t6 and a0..a7. It keeps
   ra, sp, gp, tp, s0..s11, the floating-point registers and fcsr, and all other memory; the
   stack from lo to sp stays writable.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Prog Require Import diginet_frame_parse_c.
Import ListNotations.
Open Scope Z_scope.

Definition CHECK_PARSE_FIELDS : Z := 0x12eec.
(* addi sp, sp, -0x30 at 0x12eec; bcmp, diginet_mac_is_digidesign and
   diginet_frame_is_keepalive use no stack. *)
Definition CPF_STACK : Z := 48.

(* The struct spec_frame (fuzz/spec.h:188-197) that the inlined spec_read_frame of
   LLVMFuzzerTestOneInput (0x12cf4..0x12e30) leaves at w for the frame bytes b at buf when
   fr_code b = 0: memset to zero, then the fields that it reads from b. code is SPEC_OK, 0 (the
   binary does not write it again after the memset). *)
Definition spec_cells (buf : Z) (b : list byte) : list cell :=
  [ C4 (Z_to_bv 64 0);                                        (*  0 code *)
    CB 4 (repeat (b8 0) 4);                                   (*  4 padding *)
    C8 (Z_to_bv 64 buf);                                      (*  8 dst *)
    C8 (Z_to_bv 64 (buf + 6));                                (* 16 src *)
    C2 (Z_to_bv 64 (fr_ethertype b));                         (* 24 ethertype *)
    C2 (Z_to_bv 64 (fr_numbytes b));                          (* 26 numbytes *)
    C2 (Z_to_bv 64 (fr_sum b));                               (* 28 sum *)
    C2 (Z_to_bv 64 (fr_retry b));                             (* 30 retry *)
    C4 (Z_to_bv 64 (fr_send b));                              (* 32 send *)
    C4 (Z_to_bv 64 (fr_ack b));                               (* 36 ack *)
    C1 (b8 (fr_cmd b));                                       (* 40 cmd *)
    C1 (b8 (fr_ncmds b));                                     (* 41 ncmds *)
    CB 6 (repeat (b8 0) 6);                                   (* 42 padding *)
    C8 (Z_to_bv 64 (buf + 30));                               (* 48 body *)
    C8 (Z_to_bv 64 (fr_body_len b));                          (* 56 body_len *)
    C8 (Z_to_bv 64 (fr_pad_len b));                           (* 64 pad_len *)
    C2 (Z_to_bv 64 (fr_body_sum b));                          (* 72 body_sum *)
    CB 6 (repeat (b8 0) 6) ].                                 (* 74 padding *)

(* The 80 bytes of spec_cells, for check_round_trip_c.v. *)
Definition spec_bytes (buf : Z) (b : list byte) : list byte := cells_bytes (spec_cells buf b).

Definition check_parse_fields_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (buf f w lo : Z) (b fj : list byte),
    fr_code b = 0 -> f <> 0 ->
    bytes_at rsegs m buf b ->
    ro_cells rsegs m f (parse_cells buf b fj) ->
    ro_cells rsegs m w (spec_cells buf b) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + CPF_STACK <= bv_unsigned sp ->
    buf + Z.of_nat (length b) <= bv_unsigned sp - CPF_STACK \/ bv_unsigned sp <= buf ->
    f + 64 <= bv_unsigned sp - CPF_STACK \/ bv_unsigned sp <= f ->
    w + 80 <= bv_unsigned sp - CPF_STACK \/ bv_unsigned sp <= w ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CPF_STACK, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 buf) (Z_to_bv 64 f) (Z_to_bv 64 w)
               a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_PARSE_FIELDS) fc None m (seg_rom rsegs)).
