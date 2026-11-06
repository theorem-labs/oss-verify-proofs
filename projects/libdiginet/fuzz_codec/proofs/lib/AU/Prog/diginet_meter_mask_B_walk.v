(* diginet_meter_mask at image B (fuzz_codec.asan-ubsan): the run of its 7 instructions 0x85ef8-0x85f10, in the form
   lib/A/Prog/CPgEvtLeaf.v's leaf_a012 states. The words are the UBSan image's 0x15b88-0x15ba0 and image A's
   0x855ac-0x855c4 word for word (cmpkit 86da41d3ef68 strictcmp3: EQUAL, no target), so the run is
   lib/U/Prog/diginet_meter_mask.v's at the image-B pcs, with that file's s32_mod_lt, meter_mask_lo and
   meter_mask_hi: 0x85efc `bltu a0, a1(14)` skips 0x85f00 `li a0, 14` when s < 14 (the unsigned compare of s
   sign-extended from 32 bits is s < 14), then 0x85f08 `sllw` and 0x85f0c `not` give 2^min(s, 14) - 1, 0x85f10
   `ret`. No memory access, no call, and no UBSan check. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require diginet_meter_mask.
Import ListNotations.
Open Scope Z_scope.

Module UW := OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog.diginet_meter_mask.

(* from a0 = s sign-extended from 32 bits, the run to the return with a0 = meter_mask_spec s, a1 and a2 written,
   every other register, the floating-point state, the memory and the image kept *)
Lemma diginet_meter_mask_B_run : forall s, 0 <= s < 2 ^ 32 ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt tfibsegs
    (fun ms' => exists (a1' a2' : word),
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (meter_mask_spec s)) a1' a2' a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (ret_pc ra) fc None m (seg_rom tfibsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (s32 s)) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x85ef8) fc None m (seg_rom tfibsegs)).
Proof.
  intros s HN ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  zstep. zstep. if_cases K1.
  - (* s < 14: 0x85efc taken *)
    zify_cond K1. pose proof (UW.s32_mod_lt 14 s ltac:(lia) HN K1) as L.
    zstep. zstep. zstep. zstep.
    rewrite (UW.meter_mask_lo s ltac:(lia)).
    finish.
  - (* s >= 14: a0 := 14 *)
    zify_cond K1.
    assert (L : 14 <= s).
    { destruct (Z.ltb_spec s 14) as [L|L]; [|exact L].
      unfold s32 in K1. rewrite (proj2 (Z.ltb_lt s (2 ^ 31))) in K1 by lia.
      rewrite Z.mod_small in K1 by lia. lia. }
    zstep. zstep. zstep. zstep. zstep.
    rewrite (UW.meter_mask_hi s L).
    finish.
Qed.
