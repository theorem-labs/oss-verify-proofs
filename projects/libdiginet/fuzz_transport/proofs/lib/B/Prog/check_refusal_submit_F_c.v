(* Footprint form of check_refusal_submit_contract (check_refusal_submit_c.v; image B, entry 0x8640c): the same
   premises, then one rng premise per memory range the code reads or writes, and the run as an ExecF.evtF run under
   the footprint RNG (every data access of every step lies in RNG). The ranges:
     - the frame [sp - 32, sp): the 8-byte stores of ra, s0 and s1 at sp - 8, sp - 16 and sp - 24 (0x86410-0x86418)
       and their loads (0x86514-0x8651c);
     - GOT_CELL_K 8 (0x86428) and CELL_K 8 (0x8642c): the runtime cells that give 0x7fff8000;
     - the shadow bytes shadow_addr (cp + i), 0 <= i < 32: the code loads those of cp + 24 (0x8643c) and, in the loop,
       of cp + i, cp + i + 1 and cp + i + 3 (0x86480, 0x864a4, 0x864c8);
     - [cp, cp + 32), the bytes c: the code loads c[24] = len (0x86444) and, in the loop, c[i], c[i + 1], c[i + 3]
       (0x8648c, 0x864ac, 0x864d0), i + 3 < len <= 32;
     - [CHECK_REFUSAL_SUBMIT_QUEUED, + 4) = [0x5e3d20, 0x5e3d24): g_s.queued (0x86534), loaded only for a system
       command with rc = -10.
   Which bytes of c the loop reads depends on c, so the c and shadow premises cover the 32 bytes the plain contract
   gives (bytes_at rsegs m cp c, length c = 32) and their shadow bytes, as the call site's footprint RNG_W W holds them
   all. The g_s.queued premise has no condition: the range is a harness global's payload, an image byte RNG_W W always
   holds, so a condition would only add a case to the walk. The tests at 0x8641c-0x86420, 0x86470, 0x86494 and
   0x864b4-0x864b8, the compares at 0x864e4-0x864e8, 0x864f0-0x864f4, 0x864fc-0x86500 and 0x86548-0x8654c touch only
   registers, and the trap path (0x8653c - 0x86544) makes no data access of this function's own.
   Form: lib/A/Prog/check_refusal_submit_F_c.v (image A's footprint form: the rng premises after the contract's
   premises, the same post), at image B's frame, load addresses and runtime cells. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA TWorldB check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_refusal_submit_c.
Import ListNotations.
Open Scope Z_scope.

Definition check_refusal_submit_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (Bw Bw' : list byte)
         (cp : Z) (c : list byte) (rc before : Z),
    a0 = Z_to_bv 64 cp ->
    a1 = Z_to_bv 64 rc ->
    a2 = Z_to_bv 64 (bv_swrap 32 before) ->
    -2 ^ 31 <= rc < 2 ^ 31 ->
    0 <= before < 2 ^ 32 ->
    0 < cp ->
    cp mod 4 = 0 ->
    bytes_at rsegs m cp c ->
    length c = 32%nat ->
    tw_at TMAP_B (csw_view m) Bw ->
    TC.check_refusal_submit_m Bw c rc before = Some (Bw', tt) ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + CHECK_REFUSAL_SUBMIT_FRAME <= bv_unsigned sp ->
    off_stk sp CHECK_REFUSAL_SUBMIT_FRAME TG.G_HARNESS_B_LO (TG.G_HARNESS_B_HI - TG.G_HARNESS_B_LO) ->
    asan_cells m ->
    app_mem (bv_unsigned sp - CHECK_REFUSAL_SUBMIT_FRAME) -> app_mem (bv_unsigned sp - 1) ->
    off_stk sp CHECK_REFUSAL_SUBMIT_FRAME GOT_CELL_K 8 ->
    off_stk sp CHECK_REFUSAL_SUBMIT_FRAME CELL_K 8 ->
    off_stk sp CHECK_REFUSAL_SUBMIT_FRAME cp 32 ->
    addressable m cp 32 ->
    ExecF.rng RNG (bv_unsigned sp - CHECK_REFUSAL_SUBMIT_FRAME) CHECK_REFUSAL_SUBMIT_FRAME ->
    ExecF.rng RNG GOT_CELL_K 8 ->
    ExecF.rng RNG CELL_K 8 ->
    (forall i, 0 <= i < 32 -> ExecF.rng RNG (shadow_addr (cp + i)) 1) ->
    ExecF.rng RNG cp 32 ->
    ExecF.rng RNG CHECK_REFUSAL_SUBMIT_QUEUED 4 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (a0' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1 a2 a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_REFUSAL_SUBMIT_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         Bw' = Bw /\
         tw_at TMAP_B (csw_view m') Bw)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_REFUSAL_SUBMIT) fc None m (seg_rom rsegs)).
