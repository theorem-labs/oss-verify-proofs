(* Modified by Theorem Labs, 2026-10: diginet_announce_parse's footprint contract, in the form of libreac/fuzz_decode's
   lib/A/Prog/reac_decode_F_c.v. *)
(* Footprint form of diginet_announce_parse_contract (fuzz_transport.asan image A, entry 0x8c238, own frame 16
   bytes), RELOCATED from libdiginet/fuzz_frame lib/A/Prog/diginet_announce_parse_F_c.v (file sha256 1cbb0d4c27a5;
   donor not released) with the pcs of
   diginet_announce_parse_c.v changed (+ 0x967c, each read again off the symbol-bearing twin 86efc3a80314): the same
   premises, then one ExecF.rng premise per memory range the code reads or writes, under the condition under which
   the code touches it, and the run as an ExecF.evtF run under the footprint RNG (every data access of every step
   lies in RNG).
   There is no shadow_rw premise: each shadow byte the code loads is one that an addressable premise reads.
   The ranges (diginet_announce_parse_c.v gives the pc of each access):
   - the frame [sp - 16, sp): ra is stored at sp - 8 (0x8c23c) and loaded back (0x8c414);
   - GOT_CELL_K and CELL_K: one 8-byte load each (0x8c250, 0x8c254), on every run (f and ap are not 0);
   - f + 30 (1 byte) and its shadow byte: on every run;
   - [f + 40, f + 48) and its shadow bytes: when cmd is e0 or e1 (ann_cmd; DgnSpec.ann_cmd_land: it is the test
     (cmd & 0xfe) = 0xe0 of 0x8c278);
   - on code 0 (ann_ok): [f + 32, f + 40) (loaded two times), [body + 15, body + 33) (the code reads a prefix of each
     half), the 40 bytes at ap (the code stores into [ap, ap + 20) and [ap + 24, ap + 40)), and the shadow bytes of
     each of these ranges.
   The shadow bytes of [p, p + n) are [shadow_addr p, shadow_addr (p + n - 1)] (p need not be 8-aligned).
   Template: reac_decode_F_c.v:24-75. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_announce_parse_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF.
Import ListNotations.
Open Scope Z_scope.

Definition diginet_announce_parse_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bb aj : list byte)
         (f ap cmd body lo : Z),
    a0 = Z_to_bv 64 f -> a1 = Z_to_bv 64 ap ->
    0 < f < 2^64 -> 0 < ap < 2^64 ->
    0 <= cmd < 2^8 -> 0 < body < 2^64 ->
    bytes_at rsegs m (f + 30) [b8 cmd] ->
    bytes_at rsegs m (f + 32) (le8 (Z_to_bv 64 body) ++ le8 (Z_to_bv 64 (Z.of_nat (length bb)))) ->
    bytes_at rsegs m body bb ->
    stk rsegs m lo (bv_unsigned sp) -> lo + DIGINET_ANNOUNCE_PARSE_FRAME <= bv_unsigned sp ->
    off_stk sp DIGINET_ANNOUNCE_PARSE_FRAME (f + 30) 18 ->
    (ann_ok cmd bb = true -> off_stk sp DIGINET_ANNOUNCE_PARSE_FRAME (body + 15) 18) ->
    (ann_ok cmd bb = true ->
       rw_cells rsegs m ap [CB 40 aj] /\
       (ap + 40 <= f + 30 \/ f + 48 <= ap) /\
       (ap + 40 <= body + 15 \/ body + 33 <= ap) /\
       off_stk sp DIGINET_ANNOUNCE_PARSE_FRAME ap 40) ->
    app_mem (bv_unsigned sp - DIGINET_ANNOUNCE_PARSE_FRAME) -> app_mem (bv_unsigned sp - 1) ->
    asan_cells m ->
    off_stk sp DIGINET_ANNOUNCE_PARSE_FRAME GOT_CELL_K (MIDEND + 8 - GOT_CELL_K) ->
    addressable m (f + 30) 1 ->
    (ann_cmd cmd = true -> addressable m (f + 40) 8) ->
    (ann_ok cmd bb = true -> addressable m (f + 32) 8) ->
    (ann_ok cmd bb = true -> addressable m (body + 15) 18) ->
    (ann_ok cmd bb = true -> addressable m ap 40) ->
    (* the frame *)
    ExecF.rng RNG (bv_unsigned sp - DIGINET_ANNOUNCE_PARSE_FRAME) DIGINET_ANNOUNCE_PARSE_FRAME ->
    (* the two asan_cells cells *)
    ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
    (* the byte cmd and its shadow byte *)
    ExecF.rng RNG (f + 30) 1 ->
    ExecF.rng RNG (shadow_addr (f + 30)) (shadow_addr (f + 30 + 1 - 1) - shadow_addr (f + 30) + 1) ->
    (* the length field and its shadow bytes, when cmd is e0 or e1 *)
    (ann_cmd cmd = true -> ExecF.rng RNG (f + 40) 8) ->
    (ann_cmd cmd = true ->
       ExecF.rng RNG (shadow_addr (f + 40)) (shadow_addr (f + 40 + 8 - 1) - shadow_addr (f + 40) + 1)) ->
    (* on code 0: the body field, the two strings of the body, the 40 bytes at ap, and their shadow bytes *)
    (ann_ok cmd bb = true -> ExecF.rng RNG (f + 32) 8) ->
    (ann_ok cmd bb = true ->
       ExecF.rng RNG (shadow_addr (f + 32)) (shadow_addr (f + 32 + 8 - 1) - shadow_addr (f + 32) + 1)) ->
    (ann_ok cmd bb = true -> ExecF.rng RNG (body + 15) 18) ->
    (ann_ok cmd bb = true ->
       ExecF.rng RNG (shadow_addr (body + 15)) (shadow_addr (body + 15 + 18 - 1) - shadow_addr (body + 15) + 1)) ->
    (ann_ok cmd bb = true -> ExecF.rng RNG ap 40) ->
    (ann_ok cmd bb = true ->
       ExecF.rng RNG (shadow_addr ap) (shadow_addr (ap + 40 - 1) - shadow_addr ap + 1)) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (ann_code cmd (Z.of_nat (length bb))))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         wmono rsegs m m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         (if ann_ok cmd bb
          then munch [(bv_unsigned sp - DIGINET_ANNOUNCE_PARSE_FRAME, bv_unsigned sp); (ap, ap + 40)] m m' /\
               rw_cells rsegs m' ap (PAnn.ann_cells body bb aj)
          else munch [(bv_unsigned sp - DIGINET_ANNOUNCE_PARSE_FRAME, bv_unsigned sp)] m m'))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DIGINET_ANNOUNCE_PARSE) fc None m (seg_rom rsegs)).
