(* Stack constants of the four harness checks LLVMFuzzerTestOneInput calls in fuzz_frame.ubsan, read from the
   disassembly of the pinned image (sha256 259858a8e23b), with function addresses from the .symtab of its
   unstripped twin. Each is the frame of the function's own addi sp, plus the deepest stack of its callees.
   The UBSan contracts of the four checks import this file. Written by Theorem Labs.
     check_parse_refusal  0x13010  addi sp, sp, -0x10 at 0x1304c (only on its path to abort, its one callee)
     check_parse_fields   0x1305c  addi sp, sp, -0x30 at 0x1305c; its callees bcmp, diginet_frame_is_keepalive
                                   (0x139d8) and diginet_mac_is_digidesign (0x13994) use no stack
     check_round_trip     0x131e4  addi sp, sp, -0x50 at 0x131e4; its callees: malloc and free (ALLOC_STACK of
                                   U/Reusable/YO0d.v, the stack of call_pre), diginet_frame_build (0x13c44: addi
                                   sp, sp, -0x60, and its callee diginet_body_check, 0x14028: addi sp, sp, -0x90;
                                   96 + 144 = 240), spec_build_frame (0x136a8: addi sp, sp, -0x60, callees memcpy
                                   and memset; 96); memcpy, memset and bcmp use no stack. ALLOC_STACK is the deepest.
     check_announce       0x13500  addi sp, sp, -0x50 at 0x13500; its callee diginet_announce_parse (0x13f04:
                                   addi sp, sp, -0x20; its callee copy_strz, 0x13fc4, uses no stack) takes 32;
                                   memset and bcmp use no stack. *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Reusable Require Import YO0d.
Local Open Scope Z_scope.

Definition U_CPR_STACK : Z := 16.
Definition U_CPF_STACK : Z := 48.
Definition U_CRT_FRAME : Z := 80.
Definition U_CRT_STACK : Z := U_CRT_FRAME + ALLOC_STACK.
Definition U_CA_STACK : Z := 80 + 32.
