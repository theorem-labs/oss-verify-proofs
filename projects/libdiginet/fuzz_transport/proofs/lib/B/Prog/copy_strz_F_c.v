(* Modified by Theorem Labs, 2026-10: copy_strz of fuzz_frame.asan-ubsan, adapted from this unit's lib/A/Prog/diginet_cursor_init_F_c.v: the premises of copy_strz_c.v, then the footprint ranges of copy_strz's code (the frame, the two cells, the 9 bytes at src and their shadow bytes, the 10 bytes at dst and their shadow bytes, all without condition); shape donor of the premises: the UBSan image's contract lib/U/Prog/copy_strz_c.v. *)
(* Footprint form of copy_strz_contract (copy_strz_c.v; image B, entry 0x8bf5c, frame 16 bytes), RELOCATED from
   libdiginet/fuzz_frame lib/B/Prog/copy_strz_F_c.v (file sha256 c3b44f85a2a0; donor not released) with the numbers
   of copy_strz_c.v changed: the same premises, then one ExecF.rng premise per memory range the code reads or
   writes, and the run as an ExecF.evtF run under the footprint RNG (every data access of every step lies in RNG).
   The code
     - stores ra at sp - 8 (0x8bf60) and loads it back (0x8c02c): the frame [sp - 16, sp);
     - loads 8 bytes at GOT_CELL_K (0x8bf6c) and 8 bytes at CELL_K (0x8bf70);
     - loads the bytes src + i (0x8bfb0) and their shadow bytes (0x8bfa8), for i = 0 up to the first 0 byte, at most
       i = 8: a part of [src, src + 9) and of [shadow_addr src, shadow_addr (src + 9 - 1)];
     - loads the shadow bytes of dst + i (0x8bfc4) and of dst + k (0x8c020), stores the bytes dst + i (0x8bfd0) and
       the 0 byte at dst + k (0x8c028), k <= 9: a part of [dst, dst + 10) and of
       [shadow_addr dst, shadow_addr (dst + 10 - 1)].
   The code has no early return: every run loads the cells, the byte at src and its shadow byte, and stores the byte
   at dst + k after loading its shadow byte, so every range premise is unconditional. The premises give the whole 9
   and 10 bytes, with no condition on the values of the bytes, as the addressable premises of copy_strz_c.v do. The
   five UBSan checks (0x8bf8c, 0x8bf98, 0x8bf9c, 0x8bfb8, 0x8c010, branches to the unimp word at 0x8c038) compare
   registers only, so they add no range, and they are not taken (copy_strz_c.v). The error-path calls
   (__asan_report_load1 at 0x8c04c, __asan_report_store1 at 0x8c008 and 0x8c044) are not reached (copy_strz_c.v),
   so no range is given for them. There is no shadow_rw premise: the shadow loads read the bytes that addressable
   states.
   Form: fuzz_frame's lib/B/Prog/copy_strz_F_c.v, after lib/A/Prog/diginet_cursor_init_F_c.v (the rng premises of a
   writing leaf, with no condition). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA copy_strz_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF.
Import ListNotations.
Open Scope Z_scope.

Definition copy_strz_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (s old : list byte) (dst src lo : Z),
    a0 = Z_to_bv 64 dst -> a1 = Z_to_bv 64 src ->
    src <> 0 ->
    (9 <= length s)%nat -> bytes_at rsegs m src s ->
    rw_cells rsegs m dst [CB 10 old] ->
    dst + 10 <= src \/ src + 9 <= dst ->
    stk rsegs m lo (bv_unsigned sp) -> lo + COPY_STRZ_FRAME <= bv_unsigned sp ->
    off_stk sp COPY_STRZ_FRAME src 9 ->
    off_stk sp COPY_STRZ_FRAME dst 10 ->
    app_mem (bv_unsigned sp - COPY_STRZ_FRAME) -> app_mem (bv_unsigned sp - 1) ->
    asan_cells m ->
    off_stk sp COPY_STRZ_FRAME GOT_CELL_K 8 -> off_stk sp COPY_STRZ_FRAME CELL_K 8 ->
    addressable m src 9 ->
    addressable m dst 10 ->
    (* the frame: ra stored at sp - 8 and loaded back *)
    ExecF.rng RNG (bv_unsigned sp - COPY_STRZ_FRAME) COPY_STRZ_FRAME ->
    (* the two asan_cells cells: the GOT word and the shadow base *)
    ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
    (* the 9 bytes at src the code may read, and their shadow bytes *)
    ExecF.rng RNG src 9 ->
    ExecF.rng RNG (shadow_addr src) (shadow_addr (src + 9 - 1) - shadow_addr src + 1) ->
    (* the 10 bytes at dst the code may write, and their shadow bytes, loaded before each store *)
    ExecF.rng RNG dst 10 ->
    ExecF.rng RNG (shadow_addr dst) (shadow_addr (dst + 10 - 1) - shadow_addr dst + 1) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - COPY_STRZ_FRAME, bv_unsigned sp); (dst, dst + 10)] m m' /\
         wmono rsegs m m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         rw_cells rsegs m' dst [CB 10 (DgnSpec.copy_strz 10 9 s old)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 COPY_STRZ) fc None m (seg_rom rsegs)).
