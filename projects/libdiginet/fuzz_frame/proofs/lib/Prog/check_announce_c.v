(* Contract of check_announce in fuzz_frame.plain.
   Source: fuzz/fuzz_frame.c:212-263 at 835f336c. The binary inlines field_len
   (fuzz/fuzz_frame.c:204-210) and spec_strz_len (fuzz/spec.h:251-257) two times each.
   Address 0x13518, size 376 bytes. Stack frame: 80 bytes (addi sp, sp, -0x50 at 0x13518); the
   struct diginet_announce a (40 bytes) is at sp + 8 in it. The function calls memset
   (0x1bc60), diginet_announce_parse (0x13ab0) and bcmp (0x1b828) two times. None of them uses
   stack: their contracts write no byte below sp. It calls abort (0x14414) at 0x1368c.
   CA_STACK is 80.
   Arguments: a0 is the address f of a struct diginet_frame (64 bytes), a1 the address w of a
   struct spec_frame (80 bytes). The caller is LLVMFuzzerTestOneInput, at 0x12e60, only for a
   frame b with fr_code b = 0. It gives its local frame struct at sp + 0x50 and its local
   spec_frame at sp.
   Preconditions:
   - fr_code b = 0, for the bytes b at buf (the caller's copy of the input); f is not 0;
   - the bytes b at buf are readable (bytes_at);
   - the 64 bytes at f are parse_cells buf b fj (diginet_frame_parse_c.v), the struct that
     diginet_frame_parse writes (ro_cells). f->body is buf + 30;
   - the 80 bytes at w are spec_cells buf b (check_parse_fields_c.v), the struct that the
     inlined spec_read_frame writes (ro_cells). w->body is buf + 30;
   - the bytes at buf, f and w are not in the 80 bytes below sp;
   - the stack from lo to sp is writable (stk), and lo + 80 <= sp;
   - mem_inv holds.
   Result: the function returns to ra. It does not call abort:
   - memset fills a with 0xa5. diginet_announce_parse (f, a) answers
     r = ann_code (fr_cmd b) (fr_body_len b), and is_ann is ann_cmd (fr_cmd b): the binary
     tests (cmd & 0xfe) == 0xe0 (DgnSpec.ann_cmd_land). So the three tests of r
     (0x13554..0x13590) hold. On r other than 0 the function returns;
   - on r = 0: a.unknown is buf + 30 = w->body and a.unknown_len is 15 (ann_cells). a.version
     is ann_version of the body, so field_len 10 of it is strz_len of the body bytes from 15
     (DgnSpec.field_len_copy_strz), and its first strz_len bytes are those body bytes
     (DgnSpec.copy_strz_prefix; bcmp at 0x13630). The same holds for a.name and the body
     bytes from 24 (bcmp at 0x1366c). fr_body_len b >= 33 there, so spec_strz_len reads only
     bytes of the body.
   The function writes only the 80 bytes below sp. It can change t0..t6 and a0..a7. It keeps
   ra, sp, gp, tp, s0..s11, the floating-point registers and fcsr, and all other memory; the
   stack from lo to sp stays writable.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Prog Require Import diginet_frame_parse_c check_parse_fields_c.
Import ListNotations.
Open Scope Z_scope.

Definition CHECK_ANNOUNCE : Z := 0x13518.
(* addi sp, sp, -0x50 at 0x13518; memset, diginet_announce_parse and bcmp use no stack. *)
Definition CA_STACK : Z := 80.

Definition check_announce_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (buf f w lo : Z) (b fj : list byte),
    fr_code b = 0 -> f <> 0 ->
    bytes_at rsegs m buf b ->
    ro_cells rsegs m f (parse_cells buf b fj) ->
    ro_cells rsegs m w (spec_cells buf b) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + CA_STACK <= bv_unsigned sp ->
    buf + Z.of_nat (length b) <= bv_unsigned sp - CA_STACK \/ bv_unsigned sp <= buf ->
    f + 64 <= bv_unsigned sp - CA_STACK \/ bv_unsigned sp <= f ->
    w + 80 <= bv_unsigned sp - CA_STACK \/ bv_unsigned sp <= w ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CA_STACK, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) (Z_to_bv 64 w)
               a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_ANNOUNCE) fc None m (seg_rom rsegs)).
