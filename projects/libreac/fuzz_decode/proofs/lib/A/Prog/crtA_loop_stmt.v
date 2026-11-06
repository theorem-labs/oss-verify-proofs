(* crtA_loop_stmt: the statement of check_round_trip's convert loop in image A, crt_loop_stmt_F, alone, so that any
   proof of it (lib/A/Prog/crtA_loop.v crt_loop_holds_F, or a port of image B's loop) and its user
   (lib/A/Prog/crtA_w_mid.v) state against one committed text.

   Ported from a working branch dc455613c81:proofs/libreac/fuzz_decode/lib/A/Prog/crt_iface_F.v:25-61,
   with every pc a name of lib/A/Prog/crtA_iface.v.  Footprint twin of the record's crt_loop_stmt of crt_iface.v:
   the convert loop of check_round_trip (A image), +0xd4 -> +0x1f0.  crt_loop_stmt_F states the loop with a
   footprint RNG: the run is an ExecF.evtF run, each step's data accesses lie in RNG, and RNG holds the ranges the
   loop reads or writes.  With s5 = Q, s0 = P, s6 = t0 = pcm, s8 = ASAN_K, s2 = ns, s3 = nch, for c = 0 .. nch-1
   (a3) and k = 0 .. ns-1:
     - +0xe4 loads the shadow byte at (Q + 8c) >> 3 + ASAN_K; +0xf8 stores 8 bytes at Q + 8c;
     - +0x118, +0x130, +0x148 load the shadow bytes at (pcm + 3(c*ns+k) + i) >> 3 + ASAN_K (i = 0, 1, 2);
       +0x134, +0x14c, +0x160 load the bytes at pcm + 3(c*ns+k) + i (i = 0, 1, 2);
     - +0x15c loads the shadow byte at (P + 4(c*ns+k)) >> 3 + ASAN_K; +0x194 stores 4 bytes at P + 4(c*ns+k).
   No other load or store: the loop does not touch the stack frame.  So RNG holds the P block [P, P + 4*nch*ns),
   the Q block [Q, Q + 8*nch), the pcm bytes [pcm, pcm + 3*nch*ns), and for each block [x, x + n) the 8-aligned
   cover of its shadow bytes [shadow_addr x / 8 * 8, shadow_addr (x + n - 1) / 8 * 8 + 8).  n > 0 for all three
   blocks (nch >= 2, ns >= 1), so no (n = 0 \/ ...) guard.  The post's crt_inv is lib/A/Prog/crtA_conv.v's. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac
  Bytes ZBridge FP.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import AsanKA AsanKAProof ReacDecodeLib check_braid
  crtA_iface crtA_conv.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog Require Import FloatExact.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

Definition crt_loop_stmt_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp s1 s4 s7 s11 a0 a1 a2 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m0 : word -> option byte) (pb : Z -> byte) (P Q pcm nch ns : Z),
    2 <= nch <= 127 -> 1 <= ns <= 12 -> 3 * nch * ns <= 1440 ->
    0 < P -> P + 4 * nch * ns < 2^63 -> P mod 16 = 0 ->
    0 < Q -> Q + 8 * nch < 2^63 -> Q mod 16 = 0 ->
    0 < pcm -> pcm + 3 * nch * ns < 2^63 ->
    (forall i, 0 <= i < 3 * nch * ns -> mrd rsegs m0 (wa (pcm + i)) = Some (pb i)) ->
    wr_at rsegs m0 P (4 * nch * ns) -> wr_at rsegs m0 Q (8 * nch) ->
    addressable m0 P (4 * nch * ns) -> addressable m0 Q (8 * nch) -> addressable m0 pcm (3 * nch * ns) ->
    (P + 4 * nch * ns <= Q \/ Q + 8 * nch <= P) ->
    (P + 4 * nch * ns <= pcm \/ pcm + 3 * nch * ns <= P) ->
    (Q + 8 * nch <= pcm \/ pcm + 3 * nch * ns <= Q) ->
    unbox_s (reg_get F (Z_to_bv 5 15)) = Z_to_bv 32 F2M23 -> frm0 fc ->
    ExecF.rng RNG P (4 * nch * ns) ->
    ExecF.rng RNG Q (8 * nch) ->
    ExecF.rng RNG pcm (3 * nch * ns) ->
    ExecF.rng RNG (shadow_addr P / 8 * 8)
      (shadow_addr (P + 4 * nch * ns - 1) / 8 * 8 + 8 - shadow_addr P / 8 * 8) ->
    ExecF.rng RNG (shadow_addr Q / 8 * 8)
      (shadow_addr (Q + 8 * nch - 1) / 8 * 8 + 8 - shadow_addr Q / 8 * 8) ->
    ExecF.rng RNG (shadow_addr pcm / 8 * 8)
      (shadow_addr (pcm + 3 * nch * ns - 1) / 8 * 8 + 8 - shadow_addr pcm / 8 * 8) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (t0 t1 t2 a0' a1' a2' s6 s9' s10' t3' t4' t5' t6' : word) (F' : bvmap 5 word)
                         (fc' : bv 32) (m : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 P) s1 a0' a1' a2' (Z_to_bv 64 nch) (Z_to_bv 64 (4 * ns))
                    (Z_to_bv 64 CRT_A5) (Z_to_bv 64 (3 * ns)) (Z_to_bv 64 (3 * ns)) (Z_to_bv 64 ns)
                    (Z_to_bv 64 nch) s4 (Z_to_bv 64 Q) s6 s7 (Z_to_bv 64 ASAN_K) s9' s10' s11 t3' t4' t5' t6')
                  F' (Z_to_bv 64 CRT_LOOP_OUT) fc' None m (seg_rom rsegs) /\
         frm0 fc' /\ crt_inv m0 pb P Q nch ns m (nch * ns) nch)
      (MS (mkR ra sp gp tp (Z_to_bv 64 pcm) (Z_to_bv 64 P) (Z_to_bv 64 P) (Z_to_bv 64 P) s1 a0 a1 a2
               (Z_to_bv 64 0) (Z_to_bv 64 (4 * ns)) (Z_to_bv 64 CRT_A5) (Z_to_bv 64 (3 * ns)) (Z_to_bv 64 (3 * ns))
               (Z_to_bv 64 ns) (Z_to_bv 64 nch) s4 (Z_to_bv 64 Q) (Z_to_bv 64 pcm) s7 (Z_to_bv 64 ASAN_K)
               s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CRT_LOOP_IN) fc None m0 (seg_rom rsegs)).
