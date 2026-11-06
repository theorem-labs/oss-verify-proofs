(* Footprint form of diginet_cursor_init_contract (image B, entry 0x8c554, frame 16 bytes), RELOCATED from
   libdiginet/fuzz_decode lib/B/Prog/diginet_cursor_init_F_c.v (file sha256 145d062ad846; donor not released) with
   the numbers of diginet_cursor_init_c.v changed: the same premises, then one ExecF.rng premise per memory range the
   code reads or writes, and the run as an ExecF.evtF run under the footprint RNG (every data access of every step
   lies in RNG). The code
     - stores ra at sp - 8 (0x8c558) and loads it back (0x8c5dc): the frame [sp - 16, sp);
     - loads 8 bytes at GOT_CELL_K (0x8c56c) and 8 bytes at CELL_K (0x8c570);
     - loads the shadow bytes of c, c + 8, c + 16 and c + 24 (0x8c57c, 0x8c594, 0x8c5b8, 0x8c5d0), at
       (a >> 3) + 0x7fff8000: they lie in [shadow_addr c, shadow_addr (c + 25 - 1)];
     - stores 8 bytes at c, c + 8 and c + 16 and one byte at c + 24 (0x8c584, 0x8c5ac, 0x8c5c0, 0x8c5d8): the
       range [c, c + 25).
   The UBSan alignment check (0x8c560 `andi a3,a0,7`, 0x8c564 `bnez a3` to the `unimp` at 0x8c5e8) tests a register
   only. c <> 0 and c mod 8 = 0 are premises, so the code always reaches these accesses and every range premise is
   unconditional; the ranges are image A's (lib/A/Prog/diginet_cursor_init_F_c.v). There is no shadow_rw premise:
   the shadow loads read the bytes that addressable states.
   Form: fuzz_decode's lib/B/Prog/diginet_cursor_init_F_c.v. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA diginet_cursor_init_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF.
Import ListNotations.
Open Scope Z_scope.

Definition diginet_cursor_init_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c body len lo : Z),
    a0 = Z_to_bv 64 c -> a1 = Z_to_bv 64 body -> a2 = Z_to_bv 64 len ->
    0 <= c < 2^64 -> c <> 0 -> 0 <= body < 2^64 -> 0 <= len < 2^64 ->
    (* Image B's UBSan premise: 0x8c560 `andi a3,a0,7` / 0x8c564 `bnez a3` trap (unimp at 0x8c5e8) on a c that is
       not 8-aligned. *)
    c mod 8 = 0 ->
    stk rsegs m lo (bv_unsigned sp) -> lo + DIGINET_CURSOR_INIT_FRAME <= bv_unsigned sp ->
    wr_at rsegs m c 25 ->
    off_stk sp DIGINET_CURSOR_INIT_FRAME c 25 ->
    app_mem (bv_unsigned sp - DIGINET_CURSOR_INIT_FRAME) -> app_mem (bv_unsigned sp - 1) ->
    asan_cells m ->
    off_stk sp DIGINET_CURSOR_INIT_FRAME GOT_CELL_K 8 -> off_stk sp DIGINET_CURSOR_INIT_FRAME CELL_K 8 ->
    addressable m c 25 ->
    (* the frame: ra stored at sp - 8 and loaded back *)
    ExecF.rng RNG (bv_unsigned sp - DIGINET_CURSOR_INIT_FRAME) DIGINET_CURSOR_INIT_FRAME ->
    (* the two asan_cells cells: the GOT word and the shadow base *)
    ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
    (* the 25 written bytes of the cursor *)
    ExecF.rng RNG c 25 ->
    (* the shadow bytes of the cursor, loaded before each store *)
    ExecF.rng RNG (shadow_addr c) (shadow_addr (c + 25 - 1) - shadow_addr c + 1) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (a0' a1' a2' a3' a4' a5' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5'
                       a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - DIGINET_CURSOR_INIT_FRAME, bv_unsigned sp); (c, c + 25)] m m' /\
         wmono rsegs m m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         rw_cells rsegs m' c (PCur.cursor_cells body (if body =? 0 then 0 else len) 0 0))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DIGINET_CURSOR_INIT) fc None m (seg_rom rsegs)).
