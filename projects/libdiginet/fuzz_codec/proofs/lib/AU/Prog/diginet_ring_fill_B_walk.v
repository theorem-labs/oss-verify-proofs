(* diginet_ring_fill at image B (fuzz_codec.asan-ubsan): the run of its 9 instructions 0x85bf8-0x85c18, in the form
   lib/A/Prog/CPgEvtLeaf.v's leaf_a012 states. The words are the UBSan image's 0x15a64-0x15a84 and image A's
   0x852f0-0x85310 word for word (cmpkit 86da41d3ef68 strictcmp3: EQUAL, no target), so the run is
   lib/U/Prog/diginet_ring_fill.v's at the image-B pcs and its arithmetic is that file's ring_fill_val:
   0x85bf8 `sltiu a1, a0, 16` and 0x85c08 `negw` form the mask n < 16 ? -1 : 0, 0x85c00 `sllw` and 0x85c04 `not`
   the word ~(-1 << (n mod 32)), 0x85c0c `and` joins them, 0x85c10-0x85c14 `slli` / `srli` 48 zero-extend the
   uint16_t, 0x85c18 `ret`. No branch, no memory access, no call, and no UBSan check. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require diginet_ring_fill.
Import ListNotations.
Open Scope Z_scope.

Module UW := OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog.diginet_ring_fill.

(* from a0 = n sign-extended from 32 bits, the run to the return with a0 = ring_fill_spec n, a1 and a2 written,
   every other register, the floating-point state, the memory and the image kept *)
Lemma diginet_ring_fill_B_run : forall n, 0 <= n < 2 ^ 32 ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt tfibsegs
    (fun ms' => exists (a1' a2' : word),
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (ring_fill_spec n)) a1' a2' a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (ret_pc ra) fc None m (seg_rom tfibsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (s32 n)) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x85bf8) fc None m (seg_rom tfibsegs)).
Proof.
  intros n HN ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  rewrite (UW.ring_fill_val n HN).
  finish.
Qed.
