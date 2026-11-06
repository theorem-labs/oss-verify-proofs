From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

(* joined_byte of the v1.9.0 harness (fuzz/fuzz_ctrl.c:251-254), ubsan build: [0x14400, 0x14454). *)
Definition JOINED_BYTE : Z := 0x14400.

(* ja(p, q, nb, i): the address that joined_byte reads its result from. first->body[i] at p + 5 + i when
   i < nb, else last[9 + i - nb] at q + (9 + i - nb). *)
Definition jb_addr (p q nb i : Z) : Z := if i <? nb then p + 5 + i else q + (9 + i - nb).

(* C1. p = a0, q = a1, i = a2, nb = the byte at p + 4, b = the byte at ja(p, q, nb, i). *)
Definition joined_byte_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (i : Z) (nb b : byte),
    (i = 9 \/ i = 10) -> a2 = Z_to_bv 64 i ->                                          (* S1.2 *)
    bv_unsigned a0 mod 4 = 0 ->                                                        (* S1.3 *)
    bytes_at rsegs m (bv_unsigned a0 + 4) [nb] ->                                      (* S1.4 *)
    (bv_unsigned nb <= i -> bv_unsigned a1 <> 0) ->                                    (* S1.6: q <> 0 *)
    bytes_at rsegs m (jb_addr (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned nb) i) [b] -> (* S1.5, S1.6 *)
    evt rsegs
      (fun ms' => exists a1' a2' a3' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (zxb b) a1' a2' a3' a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 JOINED_BYTE) fc None m (seg_rom rsegs)).
