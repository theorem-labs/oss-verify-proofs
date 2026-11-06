(* Modified by Theorem Labs, 2026-10: relocated from libdiginet/fuzz_frame proofs/libdiginet/fuzz_frame/lib/U/Prog/diginet_msg_next_w_c.v at bb3053036017d1d92db6eca9e973ce610be16c08 to fuzz_transport's images *)
(* Wide contract of diginet_msg_next in fuzz_transport.ubsan (0x18844), for a cursor whose body is
   0 with no bytes. diginet_body_check (body, len) puts its body in the cursor
   (diginet_cursor_init) and calls diginet_msg_next (0x1872c); a caller of diginet_frame_build
   can give body = NULL and body_len = 0.
   Source: src/diginet_msg.c:27-103 at 835f336c.
   Difference from U/Prog/diginet_msg_next_c.v: the premise body <> 0 becomes
   body <> 0 \/ length bb = 0. All other premises and the result are the same;
   diginet_msg_next_contract_of_w (U/Prog/diginet_msg_next_w.v) shows that this contract gives
   the narrow one.
   The empty path: pos <= length bb = 0, so pos = 0 = len. On it the function tests c and mp
   against 0 (0x18848, 0x1884c), then c & 7 at 0x18854 (a branch to the trap at 0x18a20; the
   premise c mod 8 = 0 keeps it from firing), loads len and pos, and 0x18860 (bgeu pos, len)
   goes to 0x1890c, which returns 0 with no store. The checks of the body at 0x1886c, 0x1887c,
   0x18880, mp & 7 at 0x18888 and the five index checks are all after 0x18860, so this path
   does not reach them. msg_step [] 0 st is the end: code 0, pos 0, status st, message unchanged.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import diginet_cursor_init_c diginet_msg_next_c.
Import ListNotations.
Open Scope Z_scope.

Definition diginet_msg_next_contract_w : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (c mp body : Z) (bb mj : list byte) (pos : nat) (st : Z),
    c <> 0 -> mp <> 0 -> c mod 8 = 0 -> mp mod 8 = 0 -> body <> 0 \/ length bb = 0%nat ->
    (pos <= length bb)%nat -> st_ok st ->
    rw_cells rsegs m c (cursor_cells body (Z.of_nat (length bb)) pos st) ->
    bytes_at rsegs m body bb ->
    rw_cells rsegs m mp [CB 40 mj] ->
    c + 25 <= mp \/ mp + 40 <= c ->
    c + 25 <= body \/ body + Z.of_nat (length bb) <= c ->
    mp + 40 <= body \/ body + Z.of_nat (length bb) <= mp ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (mr_code (msg_step bb pos st)))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(c, c + 25); (mp, mp + 40)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         rw_cells rsegs m' c (cursor_cells body (Z.of_nat (length bb)) (mr_pos (msg_step bb pos st))
                                (mr_st (msg_step bb pos st))) /\
         rw_cells rsegs m' mp (msg_cells body mj (msg_step bb pos st)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c) (Z_to_bv 64 mp) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DIGINET_MSG_NEXT) fc None m (seg_rom rsegs)).
