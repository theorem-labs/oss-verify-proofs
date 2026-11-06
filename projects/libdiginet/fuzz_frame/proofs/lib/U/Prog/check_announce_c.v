(* Contract of check_announce in fuzz_frame.ubsan, the twin of
   Prog/check_announce_c.v (fuzz_frame.plain).
   Source: fuzz/fuzz_frame.c:212-263 at 835f336c. The binary inlines field_len
   (fuzz/fuzz_frame.c:204-210) and spec_strz_len (fuzz/spec.h:251-257) two times each.
   Address 0x13500, size 424 bytes. Stack frame: 80 bytes (addi sp, sp, -0x50 at 0x13500); the
   struct diginet_announce a (40 bytes) is at sp + 8 in it. The function calls memset
   (0x1c1a0), diginet_announce_parse (0x13f04) and bcmp (0x1bd68) two times. memset and bcmp
   use no stack; diginet_announce_parse uses 32 bytes below its sp. Its walk takes their
   contracts (U/Prog/memset_c.v, diginet_announce_parse_c.v, bcmp_c.v) as hypotheses. It calls
   abort (0x14954) at 0x136a0. U_CA_STACK (U/Prog/CheckStackU.v) is 80 + 32.
   Arguments: a0 is the address f of a struct diginet_frame (64 bytes), a1 the address w of a
   struct spec_frame (80 bytes). The caller is LLVMFuzzerTestOneInput, at 0x12fd0, only for a
   frame b with fr_code b = 0. It gives its local frame struct at sp + 0x50 and its local
   spec_frame at sp.
   Preconditions:
   - fr_code b = 0, for the bytes b at buf (the caller's copy of the input);
     buf + length b < 2^64; f is not 0; f and w are 8-aligned;
   - the bytes b at buf are readable (bytes_at);
   - the 64 bytes at f are parse_cells buf b fj (U/Prog/diginet_frame_parse_c.v), the struct
     that diginet_frame_parse writes (ro_cells). f->body is buf + 30;
   - the 80 bytes at w are spec_cells buf b (U/Prog/check_parse_fields_c.v), the struct that
     the inlined spec_read_frame writes (ro_cells). w->body is buf + 30;
   - the bytes at buf, f and w are not in the 112 bytes below sp;
   - sp is 8-aligned; the stack from lo to sp is writable (stk), and lo + 112 <= sp;
   - mem_inv holds.
   Result: the function returns to ra. It does not call abort:
   - memset fills a with 0xa5. diginet_announce_parse (f, a) answers
     r = ann_code (fr_cmd b) (fr_body_len b), and is_ann is ann_cmd (fr_cmd b): the binary
     tests (cmd & 0xfe) == 0xe0 (DgnSpec.ann_cmd_land). So the three tests of r
     (0x1354c..0x1357c) hold. On r other than 0 the function returns;
   - on r = 0: a.unknown is buf + 30 = w->body and a.unknown_len is 15 (ann_cells). a.version
     is ann_version of the body, so field_len 10 of it is strz_len of the body bytes from 15
     (DgnSpec.field_len_copy_strz), and its first strz_len bytes are those body bytes
     (DgnSpec.copy_strz_prefix; bcmp at 0x13640). The same holds for a.name and the body
     bytes from 24 (bcmp at 0x1367c). fr_body_len b >= 33 there, so spec_strz_len reads only
     bytes of the body.
   The function writes only the 112 bytes below sp. It can change t0..t6 and a0..a7. It keeps
   ra, sp, gp, tp, s0..s11, the floating-point registers and fcsr, and all other memory; the
   stack from lo to sp stays writable.
   UBSan checks: branches to the trap at 0x1369c (unimp):
   - 0x1351c: w & 7 is not 0 (the alignment of struct spec_frame). The premise w mod 8 = 0
     keeps it from firing;
   - on r = 0 only: 0x1359c: a.unknown = buf + 30 is 0; 0x135a4: buf + 30 + 15 wraps;
     0x135b4: buf + 30 + 15 + i wraps (i <= 8); 0x135dc: buf + 30 + 24 wraps; 0x135f0:
     buf + 30 + 24 + i wraps (i <= 8). There fr_body_len b >= 33, so buf + 63 <= buf + length b
     < 2^64, and buf + 30 is not 0; none of them is taken.
   diginet_announce_parse's own premises need f and a 8-aligned (a is at sp - 72: the premise
   sp mod 8 = 0 gives it) and its body, buf + 30, in 1 .. 2^64 - 1 (the premise
   buf + length b < 2^64 gives it).
   Differences from the plain statement: the premises buf + length b < 2^64, f mod 8 = 0,
   w mod 8 = 0 and sp mod 8 = 0, and the stack constant is U_CA_STACK (112, with the 32 bytes
   of diginet_announce_parse) in place of 80. The caller gives a heap block far below 2^64 for
   buf and its local structs at its 16-aligned sp for f and w.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Prog Require Import diginet_frame_parse_c check_parse_fields_c
  CheckStackU.
Import ListNotations.
Open Scope Z_scope.

Definition CHECK_ANNOUNCE : Z := 0x13500.

Definition check_announce_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (buf f w lo : Z) (b fj : list byte),
    fr_code b = 0 -> buf + Z.of_nat (length b) < 2^64 -> f <> 0 -> f mod 8 = 0 -> w mod 8 = 0 ->
    bytes_at rsegs m buf b ->
    ro_cells rsegs m f (parse_cells buf b fj) ->
    ro_cells rsegs m w (spec_cells buf b) ->
    bv_unsigned sp mod 8 = 0 ->
    stk rsegs m lo (bv_unsigned sp) -> lo + U_CA_STACK <= bv_unsigned sp ->
    buf + Z.of_nat (length b) <= bv_unsigned sp - U_CA_STACK \/ bv_unsigned sp <= buf ->
    f + 64 <= bv_unsigned sp - U_CA_STACK \/ bv_unsigned sp <= f ->
    w + 80 <= bv_unsigned sp - U_CA_STACK \/ bv_unsigned sp <= w ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - U_CA_STACK, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) (Z_to_bv 64 w)
               a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_ANNOUNCE) fc None m (seg_rom rsegs)).
