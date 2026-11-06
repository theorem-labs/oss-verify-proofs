(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/U/Prog/check_refusal_c.v, with its module paths and numbers changed; 11 of its 28 lines of code are new or changed and 12 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: relocated from libdiginet/fuzz_frame proofs/libdiginet/fuzz_frame/lib/U/Prog/diginet_body_check_w_c.v at bb3053036017d1d92db6eca9e973ce610be16c08 to fuzz_transport's images *)
(* Wide contract of diginet_body_check in fuzz_transport.ubsan (0x186cc), for body = 0 with no
   bytes. diginet_frame_build (body, body_len, ...) calls diginet_body_check (body, body_len)
   (0x182f4), and a caller of diginet_frame_build can give body = NULL and body_len = 0.
   Source: src/diginet_codec.c:47-64 at 835f336c.
   Difference from U/Prog/diginet_body_check_c.v: the premise body <> 0 becomes
   body <> 0 \/ length bb = 0. All other premises and the result are the same;
   diginet_body_check_contract_of_w (U/Prog/diginet_body_check_w.v) shows that this contract
   gives the narrow one. Its walk takes the contract of diginet_cursor_init
   (U/Prog/diginet_cursor_init_c.v) and the wide contract of diginet_msg_next
   (U/Prog/diginet_msg_next_w_c.v) as hypotheses: the cursor holds the body 0.
   The empty path: diginet_cursor_init (sp - 104, body, 0) stores body, len 0, pos 0 and
   status 0 (its trap branch 0x1881c, c & 7, is not taken: sp mod 8 = 0); diginet_msg_next
   returns 0 (the end) before any check of the body; 0x18730 and 0x18734 go on to the prefix
   scan at 0x18770, and 0x18774 (len < 4) goes to 0x187e0, which returns 0 = body_check [].
   The seven trap branches to 0x18810 are not on this path: 0x18750 and 0x1875c follow an
   answer 1 of diginet_msg_next, and 0x18798, 0x187a4, 0x187a8, 0x187b8 and 0x187c4 are in the
   prefix scan, which runs only for len >= 4.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import diginet_body_check_c.
Import ListNotations.
Open Scope Z_scope.

Definition diginet_body_check_contract_w : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (body lo : Z) (bb : list byte),
    body <> 0 \/ length bb = 0%nat ->
    bytes_at rsegs m body bb ->
    bv_unsigned sp mod 8 = 0 ->
    stk rsegs m lo (bv_unsigned sp) -> 0 < lo -> lo + 144 <= bv_unsigned sp ->
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
