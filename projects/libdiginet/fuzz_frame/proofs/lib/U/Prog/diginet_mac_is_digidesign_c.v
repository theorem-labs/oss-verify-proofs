(* Contract of diginet_mac_is_digidesign in fuzz_frame.ubsan, the twin of
   Prog/diginet_mac_is_digidesign_c.v (fuzz_frame.plain).
   Source: src/diginet_frame.c:50-53 at 835f336c.
   Address 0x13994, size 68 bytes. No stack frame and no call.
   Argument: a0 is the address mac of the MAC. The caller is check_parse_fields (0x1311c); it
   gives f->src, the 6 source MAC bytes in its struct diginet_frame.
   Preconditions: mac is not 0. The 6 bytes l at mac are readable (bytes_at).
   Result: a0 is 1 when the bytes 0, 1, 2 of l are 00 a0 7e (oui_of l), else 0. The function
   writes a1 and a2. It writes no memory.
   It keeps all other registers, the memory and the stack.
   UBSan checks: two branches to the trap at 0x139d4 (unimp), the pointer-overflow checks of
   mac + 1 (0x139a4: mac = 2^64 - 1) and of mac + 2 (0x139b8: mac > 2^64 - 3). bytes_at of the 6
   bytes gives mac + 6 <= 2^64, so neither branch is taken.
   The statement is the plain one; only the address differs.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Spec Require Import DgnSpec DgnLib.
Import ListNotations.
Open Scope Z_scope.

Definition DIGINET_MAC_IS_DIGIDESIGN : Z := 0x13994.

Definition diginet_mac_is_digidesign_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mac : Z) (l : list byte),
    mac <> 0 ->
    length l = 6%nat ->
    bytes_at rsegs m mac l ->
    evt rsegs
      (fun ms' => exists a1' a2' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (if oui_of l then 1 else 0)) a1' a2'
                       a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 mac) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DIGINET_MAC_IS_DIGIDESIGN) fc None m (seg_rom rsegs)).
