(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/check_refusal_c.v, with its module paths changed; 11 of its 27 lines of code are new or changed and 12 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: relocated from libdiginet/fuzz_frame proofs/libdiginet/fuzz_frame/lib/Prog/diginet_body_check_w_c.v at b8f2ecf2c3ff0406d93584348ebba6e5957c14ce to fuzz_transport's images *)
(* Wide contract of diginet_body_check in fuzz_transport.plain.
   Source: src/diginet_codec.c:47-64 at 835f336c. Address 0x17c38 (diginet_body_check_c.v).
   It is diginet_body_check_contract with one premise made wider: body is not 0, or the body is
   empty. A caller such as diginet_frame_build from send_control gives body = NULL with
   body_len = 0; then diginet_cursor_init (0x17d44) sets the cursor length to 0, the first
   diginet_msg_next (0x17d68) answers 0, the prefix scan does not run, and a0 is 0, which is
   body_check []. All other premises and the result are those of diginet_body_check_contract.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require Import diginet_body_check_c.
Import ListNotations.
Open Scope Z_scope.

Definition diginet_body_check_contract_w : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (body lo : Z) (bb : list byte),
    body <> 0 \/ length bb = 0%nat ->
    bytes_at rsegs m body bb ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 144 <= bv_unsigned sp ->
    body + Z.of_nat (length bb) <= bv_unsigned sp - 144 \/ bv_unsigned sp <= body ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (body_check bb)) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - 144, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 body) (Z_to_bv 64 (Z.of_nat (length bb)))
               a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DIGINET_BODY_CHECK) fc None m (seg_rom rsegs)).
