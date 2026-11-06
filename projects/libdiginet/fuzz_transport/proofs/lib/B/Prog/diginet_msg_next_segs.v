(* diginet_msg_next_segs: the footprint statements (lib/Lib/ExecF.v evtF runs) of the image-B walk of diginet_msg_next
   (fuzz_decode.asan-ubsan 0x82328, size 0x610, neutral listing diginet_msg_next.fuzz_decode.asan-ubsan.s), the pieces
   that lib/B/Prog/diginet_msg_next_walk_lib.v carries into the caller-journal contract of
   lib/B/Prog/diginet_msg_next_cg.v. The form is the one of the image-A twin lib/A/Prog/diginet_msg_next_segs.v.

   Image B's diginet_msg_next calls no function: m->sysex and m->sysex_len are cleared by two 8-byte stores
   (0x8241c, 0x82434), so the whole function is ONE footprint run, mn_entry_F, from the entry to the return. It is
   cut at the dispatch on body[pos] (`bne t3,s4` at 0x8246c), at the two arms the dispatch reaches and at the
   epilogue:
     mn_entry_F  0x82328 -> the return. pos >= len returns 0 and stores nothing but the frame; else the code stores
                 m + 24 := pos, m + 8 := 0, m + 16 := 0, m + 3 := 0, m + 2 := 0 and reaches the dispatch;
     mn_disp_F   0x8246c (the dispatch) -> the return: a data byte with no running status (-7), a status byte
                 f1 .. ff (-8), a channel status 80 .. ef or a data byte under the running status (to mn_chan_F),
                 body[pos] = f0 (to mn_sys_F);
     mn_sys_F    0x82470: body[pos] = f0, the search for f7 (loop 0x82480 - 0x824ac) and its two ends;
     mn_chan_F   0x82640: a channel message with status s (t3), its data from index d (a7), m->running = run
                 already stored (0x82508 / 0x8263c);
     mn_fin_F    0x82798: the epilogue (mv a0,a3; 8 loads; sp += 64; ret).
   The UBSan checks (10 branches to the `unimp` word at 0x827c4) are kept not taken: c mod 8 = 0 (0x82360),
   mp mod 8 = 0 (0x823e8), and the 8 checks of body + x (x < length bb) by 0 < body and body + length bb <=
   APPMEM_END (addressable). The 36 error-path calls are kept unreached by addressable of [c, c + 25), [mp, mp + 40)
   and [body, body + length bb): every byte the code reads or stores is addressable.
   mn_post is the state every path returns in: a0 = mr_code (msg_step bb pos st), the entry's ra, sp, gp, tp, s0 - s11,
   the cursor at mr_pos / mr_st, the message bytes msg_cells (lib/Prog/diginet_msg_next_c.v), and no byte changed
   outside the frame [sp - 64, sp), [c, c + 25) and [mp, mp + 40).
   mn_ctx is what holds at every cut point after the stores before the dispatch, at the cut's memory m: the frame
   words, the cursor, the message cells mc, the body, and, at the entry memory m0, the three ranges addressable; m0
   and m differ only in the three ranges (munch). Every statement after the entry states its post relative to m0. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require diginet_cursor_init_c diginet_msg_next_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF.
Import ListNotations.
Open Scope Z_scope.
Module PCur := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.diginet_cursor_init_c.
Module PMsg := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.diginet_msg_next_c.

(* The addresses (lib/B/Prog/DgnDecodeBAddr.v: DDB_diginet_msg_next 0x82328) and the cut points. *)
Definition MN_ENTRY : Z := 0x8c60c.
Definition MN_DISP : Z := 0x8c750.
Definition MN_SYS : Z := 0x8c754.
Definition MN_CHAN : Z := 0x8c924.
Definition MN_FIN : Z := 0x8ca7c.
Definition MN_FRAME : Z := 64.

(* The 64-byte frame [sp - 64, sp) as 8 words: s6 at sp + 0, s5 at sp + 8, s4 at sp + 16, s3 at sp + 24, s2 at
   sp + 32, s1 at sp + 40, s0 at sp + 48, ra at sp + 56 (0x8232c - 0x82348). *)
Definition mn_fr (x22 x21 x20 x19 x18 x9 x8 x1 : word) : list cell :=
  [C8 x22; C8 x21; C8 x20; C8 x19; C8 x18; C8 x9; C8 x8; C8 x1].

(* The 40 message bytes at the dispatch: mj with m + 24 := pos (0x82404), m + 8 := 0 (0x8241c), m + 16 := 0
   (0x82434), m + 3 := 0 (0x8244c) and m + 2 := 0 (0x82468). *)
Definition mn_msg0 (mj : list byte) (pos : nat) : list cell :=
  [C1 (nth 0 mj (b8 0)); C1 (nth 1 mj (b8 0)); C1 (b8 0); C1 (b8 0); CB 4 (firstn 4 (skipn 4 mj));
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (Z.of_nat pos)); CB 8 (skipn 32 mj)].

(* ... and at the channel arm, with m + 1 := run (0x82508 stores 1, 0x8263c stores 0). *)
Definition mn_msg1 (mj : list byte) (pos : nat) (run : Z) : list cell :=
  [C1 (nth 0 mj (b8 0)); C1 (b8 run); C1 (b8 0); C1 (b8 0); CB 4 (firstn 4 (skipn 4 mj));
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (Z.of_nat pos)); CB 8 (skipn 32 mj)].

(* The state every path returns in. ra sp gp tp x8 x9 x18 .. x27 are the entry's values; m0 is the entry memory. *)
Definition mn_post (ra sp gp tp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word) (F : bvmap 5 word)
    (fc : bv 32) (m0 : word -> option byte) (c mp body : Z) (bb mj : list byte) (pos : nat) (st : Z)
    : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' x8 x9 (Z_to_bv 64 (mr_code (msg_step bb pos st)))
               a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp - MN_FRAME, bv_unsigned sp); (c, c + 25); (mp, mp + 40)] m0 m' /\
    rw_cells rsegs m' c (PCur.cursor_cells body (Z.of_nat (length bb)) (mr_pos (msg_step bb pos st))
                           (mr_st (msg_step bb pos st))) /\
    rw_cells rsegs m' mp (PMsg.msg_cells body mj (msg_step bb pos st)).

(* ---- the whole function: 0x82328 -> the return ---- *)
Definition mn_entry_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (c mp body : Z) (bb mj : list byte) (pos : nat) (st : Z) (lo : Z),
    a0 = Z_to_bv 64 c -> a1 = Z_to_bv 64 mp -> c <> 0 -> mp <> 0 ->
    (* image B's UBSan premises: 0x8235c `andi a0,a0,7` / 0x82360 `bnez a0` and 0x823e4 `andi t6,a1,7` /
       0x823e8 `bnez t6` *)
    c mod 8 = 0 -> mp mod 8 = 0 ->
    (pos <= length bb)%nat -> st_ok st -> length mj = 40%nat ->
    stk rsegs m lo (bv_unsigned sp) -> lo + MN_FRAME <= bv_unsigned sp ->
    app_mem (bv_unsigned sp - MN_FRAME) -> app_mem (bv_unsigned sp - 1) ->
    asan_cells m ->
    off_stk sp MN_FRAME GOT_CELL_K 8 -> off_stk sp MN_FRAME CELL_K 8 ->
    rw_cells rsegs m c (PCur.cursor_cells body (Z.of_nat (length bb)) pos st) ->
    rw_cells rsegs m mp [CB 40 mj] ->
    addressable m c 25 -> addressable m mp 40 ->
    off_stk sp MN_FRAME c 25 -> off_stk sp MN_FRAME mp 40 ->
    (c + 25 <= mp \/ mp + 40 <= c) ->
    (* the body is read only when pos < len; 0 < body keeps the UBSan checks 0x823cc / 0x823d0 not taken *)
    ((pos < length bb)%nat ->
       0 < body /\
       bytes_at rsegs m body bb /\
       addressable m body (Z.of_nat (length bb)) /\ off_stk sp MN_FRAME body (Z.of_nat (length bb)) /\
       (c + 25 <= body \/ body + Z.of_nat (length bb) <= c) /\
       (mp + 40 <= body \/ body + Z.of_nat (length bb) <= mp)) ->
    ExecF.rng RNG (bv_unsigned sp - MN_FRAME) MN_FRAME ->
    ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
    ExecF.rng RNG c 25 -> ExecF.rng RNG mp 40 ->
    ExecF.rng RNG (shadow_addr c) (shadow_addr (c + 25 - 1) - shadow_addr c + 1) ->
    ExecF.rng RNG (shadow_addr mp) (shadow_addr (mp + 40 - 1) - shadow_addr mp + 1) ->
    ((pos < length bb)%nat ->
       ExecF.rng RNG body (Z.of_nat (length bb)) /\
       ExecF.rng RNG (shadow_addr body)
         (shadow_addr (body + Z.of_nat (length bb) - 1) - shadow_addr body + 1)) ->
    ExecF.evtF rsegs RNG
      (mn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m c mp body bb mj pos st)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 MN_ENTRY) fc None m (seg_rom rsegs)).

(* ---- after the stores before the dispatch ---- *)

(* What holds at every cut point from the dispatch on. sp0 is the entry's sp (the frame is [sp0 - 64, sp0)); ra0 x8
   x9 x18 .. x22 are the entry's ra, s0, s1, s2 - s6, saved in the frame. m0 is the entry memory, m the memory at
   the cut, mc the message cells at the cut. *)
Definition mn_ctx (RNG : ExecF.footprint) (sp0 ra0 x8 x9 x18 x19 x20 x21 x22 : word)
    (m0 m : word -> option byte) (c mp body : Z) (bb mj : list byte) (pos : nat) (st : Z) (mc : list cell)
    : Prop :=
  (pos < length bb)%nat /\ st_ok st /\ length mj = 40%nat /\
  c mod 8 = 0 /\ mp mod 8 = 0 /\ 0 < body /\
  MN_FRAME <= bv_unsigned sp0 /\ app_mem (bv_unsigned sp0 - MN_FRAME) /\ app_mem (bv_unsigned sp0 - 1) /\
  munch [(bv_unsigned sp0 - MN_FRAME, bv_unsigned sp0); (c, c + 25); (mp, mp + 40)] m0 m /\
  rw_cells rsegs m (bv_unsigned sp0 - MN_FRAME) (mn_fr x22 x21 x20 x19 x18 x9 x8 ra0) /\
  rw_cells rsegs m c (PCur.cursor_cells body (Z.of_nat (length bb)) pos st) /\
  rw_cells rsegs m mp mc /\
  bytes_at rsegs m body bb /\
  addressable m0 c 25 /\ addressable m0 mp 40 /\ addressable m0 body (Z.of_nat (length bb)) /\
  off_stk sp0 MN_FRAME c 25 /\ off_stk sp0 MN_FRAME mp 40 /\ off_stk sp0 MN_FRAME body (Z.of_nat (length bb)) /\
  (c + 25 <= mp \/ mp + 40 <= c) /\
  (c + 25 <= body \/ body + Z.of_nat (length bb) <= c) /\
  (mp + 40 <= body \/ body + Z.of_nat (length bb) <= mp) /\
  ExecF.rng RNG (bv_unsigned sp0 - MN_FRAME) MN_FRAME /\
  ExecF.rng RNG c 25 /\ ExecF.rng RNG mp 40 /\ ExecF.rng RNG body (Z.of_nat (length bb)) /\
  ExecF.rng RNG (shadow_addr c) (shadow_addr (c + 25 - 1) - shadow_addr c + 1) /\
  ExecF.rng RNG (shadow_addr mp) (shadow_addr (mp + 40 - 1) - shadow_addr mp + 1) /\
  ExecF.rng RNG (shadow_addr body) (shadow_addr (body + Z.of_nat (length bb) - 1) - shadow_addr body + 1).

(* 0x8246c, the dispatch `bne t3,s4` (s4 = 240). The registers the code left: a0 = c + 16, a1 = mp, a2 = c,
   a3 = mp + 3, a4 = body + pos, a5 = mp + 2, a6 = mp + 8, a7 = mp + 16, t0 = the shadow address of c + 16,
   t1 = the shadow base, t2 = pos, t3 = body[pos], t4 = body, t5 = len, t6 = mp & 7 = 0, s0 / s1 / s2 / s3 = the
   shadow addresses of mp + 3 / mp + 2 / mp + 8 / mp + 16, s4 = 240; s7 - s11 are the entry's (x23 .. x27). *)
Definition mn_disp_F : Prop :=
  forall (RNG : ExecF.footprint) (sp0 ra0 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word)
         (ra gp tp y21 y22 : word) (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
         (c mp body : Z) (bb mj : list byte) (pos : nat) (st : Z),
    mn_ctx RNG sp0 ra0 x8 x9 x18 x19 x20 x21 x22 m0 m c mp body bb mj pos st (mn_msg0 mj pos) ->
    ExecF.evtF rsegs RNG
      (mn_post ra0 sp0 gp tp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 F fc m0 c mp body bb mj pos st)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - MN_FRAME)) gp tp
               (Z_to_bv 64 (shadow_addr (c + 16))) (Z_to_bv 64 ASAN_K) (Z_to_bv 64 (Z.of_nat pos))
               (Z_to_bv 64 (shadow_addr (mp + 3))) (Z_to_bv 64 (shadow_addr (mp + 2)))
               (Z_to_bv 64 (c + 16)) (Z_to_bv 64 mp) (Z_to_bv 64 c) (Z_to_bv 64 (mp + 3))
               (Z_to_bv 64 (body + Z.of_nat pos)) (Z_to_bv 64 (mp + 2)) (Z_to_bv 64 (mp + 8))
               (Z_to_bv 64 (mp + 16))
               (Z_to_bv 64 (shadow_addr (mp + 8))) (Z_to_bv 64 (shadow_addr (mp + 16))) (Z_to_bv 64 240) y21 y22
               x23 x24 x25 x26 x27
               (Z_to_bv 64 (at8 bb pos)) (Z_to_bv 64 body) (Z_to_bv 64 (Z.of_nat (length bb))) (Z_to_bv 64 0))
          F (Z_to_bv 64 MN_DISP) fc None m (seg_rom rsegs)).

(* 0x82470: body[pos] = 0xf0 (the `bne t3,s4` at 0x8246c falls through); the registers are the dispatch's. *)
Definition mn_sys_F : Prop :=
  forall (RNG : ExecF.footprint) (sp0 ra0 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word)
         (ra gp tp y21 y22 : word) (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
         (c mp body : Z) (bb mj : list byte) (pos : nat) (st : Z),
    mn_ctx RNG sp0 ra0 x8 x9 x18 x19 x20 x21 x22 m0 m c mp body bb mj pos st (mn_msg0 mj pos) ->
    at8 bb pos = 0xf0 ->
    ExecF.evtF rsegs RNG
      (mn_post ra0 sp0 gp tp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 F fc m0 c mp body bb mj pos st)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - MN_FRAME)) gp tp
               (Z_to_bv 64 (shadow_addr (c + 16))) (Z_to_bv 64 ASAN_K) (Z_to_bv 64 (Z.of_nat pos))
               (Z_to_bv 64 (shadow_addr (mp + 3))) (Z_to_bv 64 (shadow_addr (mp + 2)))
               (Z_to_bv 64 (c + 16)) (Z_to_bv 64 mp) (Z_to_bv 64 c) (Z_to_bv 64 (mp + 3))
               (Z_to_bv 64 (body + Z.of_nat pos)) (Z_to_bv 64 (mp + 2)) (Z_to_bv 64 (mp + 8))
               (Z_to_bv 64 (mp + 16))
               (Z_to_bv 64 (shadow_addr (mp + 8))) (Z_to_bv 64 (shadow_addr (mp + 16))) (Z_to_bv 64 240) y21 y22
               x23 x24 x25 x26 x27
               (Z_to_bv 64 240) (Z_to_bv 64 body) (Z_to_bv 64 (Z.of_nat (length bb))) (Z_to_bv 64 0))
          F (Z_to_bv 64 MN_SYS) fc None m (seg_rom rsegs)).

(* 0x82640: a channel message with status s (t3), its data from index d (a7), m->running = run already stored.
   Reached with (s, run, d) = (body[pos], 0, pos + 1) from a status byte 80 .. ef (0x8263c falls through) and with
   (st, 1, pos) from a data byte under the running status st (0x82510 `j`). a4 = mp + 1 on both; a6 is the value
   each path left (the run value it stored); s5 / s6 are the dispatch's. *)
Definition mn_chan_F : Prop :=
  forall (RNG : ExecF.footprint) (sp0 ra0 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word)
         (ra gp tp a6 y21 y22 : word) (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
         (c mp body : Z) (bb mj : list byte) (pos : nat) (st : Z) (s run : Z) (d : nat),
    mn_ctx RNG sp0 ra0 x8 x9 x18 x19 x20 x21 x22 m0 m c mp body bb mj pos st (mn_msg1 mj pos run) ->
    0x80 <= s < 0xf0 -> (run = 0 \/ run = 1) -> (pos <= d <= S pos)%nat ->
    msg_step bb pos st = chan_step bb pos st s run d ->
    ExecF.evtF rsegs RNG
      (mn_post ra0 sp0 gp tp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 F fc m0 c mp body bb mj pos st)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - MN_FRAME)) gp tp
               (Z_to_bv 64 (shadow_addr (c + 16))) (Z_to_bv 64 ASAN_K) (Z_to_bv 64 (Z.of_nat pos))
               (Z_to_bv 64 (shadow_addr (mp + 3))) (Z_to_bv 64 (shadow_addr (mp + 2)))
               (Z_to_bv 64 (c + 16)) (Z_to_bv 64 mp) (Z_to_bv 64 c) (Z_to_bv 64 (mp + 3))
               (Z_to_bv 64 (mp + 1)) (Z_to_bv 64 (mp + 2)) a6 (Z_to_bv 64 (Z.of_nat d))
               (Z_to_bv 64 (shadow_addr (mp + 8))) (Z_to_bv 64 (shadow_addr (mp + 16))) (Z_to_bv 64 240) y21 y22
               x23 x24 x25 x26 x27
               (Z_to_bv 64 s) (Z_to_bv 64 body) (Z_to_bv 64 (Z.of_nat (length bb))) (Z_to_bv 64 0))
          F (Z_to_bv 64 MN_CHAN) fc None m (seg_rom rsegs)).

(* 0x82798: the epilogue, a3 = the result (0x82798 `mv a0,a3`); m1 is the memory the path left (the frame words
   still in place, the cursor and the message at their final bytes, nothing else changed since m0). s7 - s11 are the
   entry's: the function never writes them. *)
Definition mn_fin_F : Prop :=
  forall (RNG : ExecF.footprint) (sp0 ra0 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word)
         (ra gp tp t0 t1 t2 y8 y9 a0 a1 a2 a4 a5 a6 a7 y18 y19 y20 y21 y22 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m0 m1 : word -> option byte)
         (c mp body : Z) (bb mj : list byte) (pos : nat) (st : Z),
    MN_FRAME <= bv_unsigned sp0 ->
    ExecF.rng RNG (bv_unsigned sp0 - MN_FRAME) MN_FRAME ->
    rw_cells rsegs m1 (bv_unsigned sp0 - MN_FRAME) (mn_fr x22 x21 x20 x19 x18 x9 x8 ra0) ->
    munch [(bv_unsigned sp0 - MN_FRAME, bv_unsigned sp0); (c, c + 25); (mp, mp + 40)] m0 m1 ->
    rw_cells rsegs m1 c (PCur.cursor_cells body (Z.of_nat (length bb)) (mr_pos (msg_step bb pos st))
                           (mr_st (msg_step bb pos st))) ->
    rw_cells rsegs m1 mp (PMsg.msg_cells body mj (msg_step bb pos st)) ->
    ExecF.evtF rsegs RNG
      (mn_post ra0 sp0 gp tp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 F fc m0 c mp body bb mj pos st)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - MN_FRAME)) gp tp t0 t1 t2 y8 y9 a0 a1 a2
               (Z_to_bv 64 (mr_code (msg_step bb pos st))) a4 a5 a6 a7
               y18 y19 y20 y21 y22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
          F (Z_to_bv 64 MN_FIN) fc None m1 (seg_rom rsegs)).
