(* Modified by Theorem Labs, 2026-10: relocated from libdiginet/fuzz_frame proofs/libdiginet/fuzz_frame/lib/Prog/diginet_mac_is_digidesign_c.v at 9bd29914ffdef650a37285056a472ff186b4331a to fuzz_transport's images; the caller named is fuzz_frame's (its pcs dropped) *)
(* Contract of diginet_mac_is_digidesign in fuzz_transport.plain.
   Source: src/diginet_frame.c:50-53 at 835f336c.
   Address 0x176bc, size 48 bytes.
   Argument: a0 is the address mac of the MAC. In fuzz_frame the caller is check_parse_fields; it gives
   f->src, the 6 source MAC bytes in its struct diginet_frame.
   Preconditions: mac is not 0. The 6 bytes l at mac are readable (bytes_at).
   Result: a0 is 1 when the bytes 0, 1, 2 of l are 00 a0 7e (oui_of l), else 0. The function
   writes a1 and a2. It writes no memory.
   It keeps all other registers, the memory and the stack.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
Import ListNotations.
Open Scope Z_scope.

Definition DIGINET_MAC_IS_DIGIDESIGN : Z := 0x176bc.

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
