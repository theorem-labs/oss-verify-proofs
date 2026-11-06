(* Footprint form of tagged_of_contract (tagged_of_c.v; image B, entry 0x846a0): the same premises, then one rng
   premise per memory range the code reads or writes, and the run as an ExecF.evtF run under the footprint RNG (every
   data access of every step lies in RNG). The ranges, in the code's order:
     - the frame [sp - 16, sp): the 8-byte store of ra at sp - 8 (0x846a4) and its load (0x84754);
     - GOT_CELL_K 8 (0x846b8) and CELL_K 8 (0x846bc): the runtime cells that give 0x7fff8000;
     - [TAGGED_OF_NCMD, + 4) = [0x5df600, 0x5df604): g_ncmd (0x84718);
     - [b, b + 3): the byte loads at 0x846d0 (b), 0x84708 (b + 1), 0x84710 (b + 2);
     - their shadow bytes [shadow_addr b, shadow_addr (b + 2)]: the byte loads at 0x846c8, 0x846f4, 0x84704. The range
       [b, b + 3) need not be 8-aligned, so its shadow range is 1 or 2 bytes.
   The code reads nothing at n < 3 (the test at 0x846ac returns first), so the rng premises of [b, b + 3) and of its
   shadow carry the condition 3 <= n, as tagged_of_c.v's off_stk and addressable premises of b do: a caller at the end
   of its body (n = 1 or 2) need not hold b + 2 in its footprint. The rng premises of the runtime cells and of g_ncmd
   have no condition (the code reads them only at 3 <= n and, for g_ncmd, l[0] = TAG): they are image bytes, which the
   call site's footprint RNG_W W always holds, so a condition would only add a case to the walk. The rng premises of
   [b, b + 3) cover all 3 bytes with no condition on l[0], as the addressable premise does: the code reads b + 1 and
   b + 2 only when l[0] = TAG, but the caller has the 3 bytes and their shadow whenever 3 <= n. The error-path calls
   (__asan_report_load1 at 0x8476c, 0x84778, 0x84788) are not reached (tagged_of_c.v), so no range is given for them;
   the trap path (0x84760) makes no data access of this function's own.
   Form: lib/A/Prog/diginet_mac_is_digidesign_F_c.v (the rng premises of a 3-byte argument range and its shadow) and
   image B's lib/B/Prog/check_latest_frame_F_c.v (the frame, the runtime cells, a harness global's payload), at this
   function's entry and load addresses. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA TWorldB check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import tagged_of_c.
Import ListNotations.
Open Scope Z_scope.

Definition tagged_of_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (Bw Bw' : list byte)
         (b n : Z) (l : list byte) (t : option Z),
    a0 = Z_to_bv 64 b ->
    a1 = Z_to_bv 64 n ->
    0 <= n < 2 ^ 64 ->
    0 < b ->
    bytes_at rsegs m b l ->
    tw_at TMAP_B (csw_view m) Bw ->
    TC.tagged_of_m Bw l n = Some (Bw', t) ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + TAGGED_OF_FRAME <= bv_unsigned sp ->
    off_stk sp TAGGED_OF_FRAME TG.G_HARNESS_B_LO (TG.G_HARNESS_B_HI - TG.G_HARNESS_B_LO) ->
    asan_cells m ->
    app_mem (bv_unsigned sp - TAGGED_OF_FRAME) -> app_mem (bv_unsigned sp - 1) ->
    off_stk sp TAGGED_OF_FRAME GOT_CELL_K 8 ->
    off_stk sp TAGGED_OF_FRAME CELL_K 8 ->
    (3 <= n -> off_stk sp TAGGED_OF_FRAME b 3) ->
    (3 <= n -> addressable m b 3) ->
    ExecF.rng RNG (bv_unsigned sp - TAGGED_OF_FRAME) TAGGED_OF_FRAME ->
    ExecF.rng RNG GOT_CELL_K 8 ->
    ExecF.rng RNG CELL_K 8 ->
    ExecF.rng RNG TAGGED_OF_NCMD 4 ->
    (3 <= n -> ExecF.rng RNG b 3) ->
    (3 <= n -> ExecF.rng RNG (shadow_addr b) (shadow_addr (b + 2) - shadow_addr b + 1)) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (a1' a2' a3' a4' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (tagged_of_res t)) a1' a2' a3' a4' a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - TAGGED_OF_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         Bw' = Bw /\
         tw_at TMAP_B (csw_view m') Bw)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 TAGGED_OF) fc None m (seg_rom rsegs)).
