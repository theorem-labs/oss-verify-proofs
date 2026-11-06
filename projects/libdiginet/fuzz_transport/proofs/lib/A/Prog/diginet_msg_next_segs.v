(* diginet_msg_next_segs: the footprint statements (lib/Lib/ExecF.v evtF runs) of the image-A walk of diginet_msg_next
   (fuzz_decode.asan 0x820e8, neutral listing diginet_msg_next.fuzz_decode.asan.s), the pieces that
   lib/A/Prog/diginet_msg_next_walk.v carries into the caller-journal contract of lib/A/Prog/diginet_msg_next_cg.v.

   The code is cut at its one call, `jal __asan_memset` at 0x82204 (m + 8, 0, 16), and the code after the call at
   its cut points:
     mn_entry_F  0x820e8 -> the return (pos >= len: a0 = 0, nothing stored but the frame) or the memset call
                 (pc 0x51180, ra 0x82208), with the frame written (16 words: the spills at sp + 0, 8, 16 and the
                 saved registers) and m + 24 := pos, m + 3 := 0, m + 2 := 0;
     mn_body_F   0x82208 (the return of the memset call) -> the return; composed from
       mn_sys_F    0x82210: body[pos] = 0xf0, the search for 0xf7 (0x82220 - 0x82244) and its two ends;
       mn_chan_F   0x823b8: a channel message with status s, data from d, m->running := run;
       mn_fin_F    0x82528: the epilogue (16 loads, sp += 128, ret);
     and the dispatch 0x82208 - 0x82284, 0x82360 - 0x823b8 (a data byte with or without a running status, a
     status byte f1..ff, a channel status) proved in the file of mn_body_F.
   mn_post is the state every path returns in: a0 = mr_code (msg_step bb pos st), the entry's ra, sp, gp, tp and
   s0 - s11, the cursor at mr_pos / mr_st, the message bytes msg_cells (lib/Prog/diginet_msg_next_c.v), and no byte
   changed outside the frame [sp - 128, sp), [c, c + 25) and [mp, mp + 40).
   mn_ctx is what holds at every cut point after the call: the frame words, the cursor, the message after the
   stores before the call and the memset (mn_msg0), the body, the shadow bytes of the three ranges (addressable),
   the ranges outside the frame and pairwise disjoint, and the footprint. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require diginet_cursor_init_c diginet_msg_next_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF.
Import ListNotations.
Open Scope Z_scope.
Module PCur := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.diginet_cursor_init_c.
Module PMsg := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.diginet_msg_next_c.

(* The addresses (lib/A/Prog/DgnDecodeAddr.v: DD_diginet_msg_next 0x820e8, DD___asan_memset 0x51180). *)
Definition MN_ENTRY : Z := 0x8c9f8.
Definition MN_MEMSET : Z := 0x5284c.
Definition MN_RET_MEMSET : Z := 0x8cb18.
Definition MN_FRAME : Z := 128.

(* The 128-byte frame [sp - 128, sp) as 16 words: the spills at sp + 0 (m + 3), sp + 8 (the shadow address of
   m + 3) and sp + 16 (c + 16), then s11 at sp + 24 .. s0 at sp + 112 and ra at sp + 120. *)
Definition mn_fr (v0 v8 v16 x27 x26 x25 x24 x23 x22 x21 x20 x19 x18 x9 x8 x1 : word) : list cell :=
  [C8 v0; C8 v8; C8 v16; C8 x27; C8 x26; C8 x25; C8 x24; C8 x23; C8 x22; C8 x21; C8 x20; C8 x19; C8 x18; C8 x9;
   C8 x8; C8 x1].

(* The 40 message bytes at the call (0x82204): mj with m + 2 := 0 (0x821f4), m + 3 := 0 (0x821d8) and
   m + 24 := pos (0x821b4). *)
Definition mn_msg_pre (mj : list byte) (pos : nat) : list cell :=
  [C1 (nth 0 mj (b8 0)); C1 (nth 1 mj (b8 0)); C1 (b8 0); C1 (b8 0); CB 4 (firstn 4 (skipn 4 mj));
   CB 16 (firstn 16 (skipn 8 mj)); C8 (Z_to_bv 64 (Z.of_nat pos)); CB 8 (skipn 32 mj)].

(* ... and after the memset call, which sets [m + 8, m + 24) to 0. *)
Definition mn_msg0 (mj : list byte) (pos : nat) : list cell :=
  [C1 (nth 0 mj (b8 0)); C1 (nth 1 mj (b8 0)); C1 (b8 0); C1 (b8 0); CB 4 (firstn 4 (skipn 4 mj));
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (Z.of_nat pos)); CB 8 (skipn 32 mj)].

(* The state every path returns in. ra sp gp tp x8 x9 x18 .. x27 are the entry's values; m0 is the memory the
   statement starts from (the entry memory for mn_entry_F, the memory at the cut for the others). *)
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

(* The state at the memset call (0x82204 has run: pc = __asan_memset, ra = 0x82208), sp = the entry's sp - 128. *)
Definition mn_call (ra sp gp tp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word) (F : bvmap 5 word)
    (fc : bv 32) (m : word -> option byte) (c mp body : Z) (bb mj : list byte) (pos : nat)
    : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m1 : word -> option byte),
    ms' = MS (mkR (Z_to_bv 64 MN_RET_MEMSET) (Z_to_bv 64 (bv_unsigned sp - MN_FRAME)) gp tp t0' t1' t2'
               (Z_to_bv 64 (shadow_addr (mp + 2))) (Z_to_bv 64 mp)
               (Z_to_bv 64 (mp + 8)) (Z_to_bv 64 0) (Z_to_bv 64 16) a3' a4' a5' a6' a7'
               (Z_to_bv 64 c) (Z_to_bv 64 (Z.of_nat pos)) (Z_to_bv 64 (mp + 2)) (Z_to_bv 64 (body + Z.of_nat pos))
               (Z_to_bv 64 (mp + 8)) (Z_to_bv 64 (shadow_addr (c + 16))) (Z_to_bv 64 ASAN_K)
               (Z_to_bv 64 (Z.of_nat (length bb))) (Z_to_bv 64 (at8 bb pos)) (Z_to_bv 64 body) t3' t4' t5' t6')
             F (Z_to_bv 64 MN_MEMSET) fc None m1 (seg_rom rsegs) /\
    munch [(bv_unsigned sp - MN_FRAME, bv_unsigned sp); (mp, mp + 40)] m m1 /\
    rw_cells rsegs m1 (bv_unsigned sp - MN_FRAME)
      (mn_fr (Z_to_bv 64 (mp + 3)) (Z_to_bv 64 (shadow_addr (mp + 3))) (Z_to_bv 64 (c + 16))
         x27 x26 x25 x24 x23 x22 x21 x20 x19 x18 x9 x8 ra) /\
    rw_cells rsegs m1 mp (mn_msg_pre mj pos).

(* ---- the entry: 0x820e8 -> the return (pos >= len) or the memset call ---- *)
Definition mn_entry_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (c mp body : Z) (bb mj : list byte) (pos : nat) (st : Z) (lo : Z),
    a0 = Z_to_bv 64 c -> a1 = Z_to_bv 64 mp -> c <> 0 -> mp <> 0 ->
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
    ((pos < length bb)%nat ->
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
      (fun ms' =>
         mn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m c mp body bb mj pos st ms' \/
         ((pos < length bb)%nat /\
          mn_call ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m c mp body bb mj pos ms'))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 MN_ENTRY) fc None m (seg_rom rsegs)).

(* ---- after the call ---- *)

(* What holds at every cut point after the memset call. sp0 is the entry's sp (the frame is [sp0 - 128, sp0));
   ra0 x8 .. x27 are the entry's ra and s0 - s11, saved in the frame. *)
Definition mn_ctx (RNG : ExecF.footprint) (sp0 ra0 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word)
    (m : word -> option byte) (c mp body : Z) (bb mj : list byte) (pos : nat) (st : Z) : Prop :=
  (pos < length bb)%nat /\ st_ok st /\ length mj = 40%nat /\
  MN_FRAME <= bv_unsigned sp0 /\ app_mem (bv_unsigned sp0 - MN_FRAME) /\ app_mem (bv_unsigned sp0 - 1) /\
  rw_cells rsegs m (bv_unsigned sp0 - MN_FRAME)
    (mn_fr (Z_to_bv 64 (mp + 3)) (Z_to_bv 64 (shadow_addr (mp + 3))) (Z_to_bv 64 (c + 16))
       x27 x26 x25 x24 x23 x22 x21 x20 x19 x18 x9 x8 ra0) /\
  rw_cells rsegs m c (PCur.cursor_cells body (Z.of_nat (length bb)) pos st) /\
  rw_cells rsegs m mp (mn_msg0 mj pos) /\
  bytes_at rsegs m body bb /\
  addressable m c 25 /\ addressable m mp 40 /\ addressable m body (Z.of_nat (length bb)) /\
  off_stk sp0 MN_FRAME c 25 /\ off_stk sp0 MN_FRAME mp 40 /\ off_stk sp0 MN_FRAME body (Z.of_nat (length bb)) /\
  (c + 25 <= mp \/ mp + 40 <= c) /\
  (c + 25 <= body \/ body + Z.of_nat (length bb) <= c) /\
  (mp + 40 <= body \/ body + Z.of_nat (length bb) <= mp) /\
  ExecF.rng RNG (bv_unsigned sp0 - MN_FRAME) MN_FRAME /\
  ExecF.rng RNG c 25 /\ ExecF.rng RNG mp 40 /\ ExecF.rng RNG body (Z.of_nat (length bb)) /\
  ExecF.rng RNG (shadow_addr c) (shadow_addr (c + 25 - 1) - shadow_addr c + 1) /\
  ExecF.rng RNG (shadow_addr mp) (shadow_addr (mp + 40 - 1) - shadow_addr mp + 1) /\
  ExecF.rng RNG (shadow_addr body) (shadow_addr (body + Z.of_nat (length bb) - 1) - shadow_addr body + 1).

(* 0x82208, the return of the memset call: the callee-saved registers as the entry piece left them; ra and the
   other caller-saved registers are any values (the call changed them). *)
Definition mn_body_F : Prop :=
  forall (RNG : ExecF.footprint) (sp0 ra0 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word)
         (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (c mp body : Z) (bb mj : list byte) (pos : nat) (st : Z),
    mn_ctx RNG sp0 ra0 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 m c mp body bb mj pos st ->
    ExecF.evtF rsegs RNG
      (mn_post ra0 sp0 gp tp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 F fc m c mp body bb mj pos st)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - MN_FRAME)) gp tp t0 t1 t2
               (Z_to_bv 64 (shadow_addr (mp + 2))) (Z_to_bv 64 mp) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 c) (Z_to_bv 64 (Z.of_nat pos)) (Z_to_bv 64 (mp + 2)) (Z_to_bv 64 (body + Z.of_nat pos))
               (Z_to_bv 64 (mp + 8)) (Z_to_bv 64 (shadow_addr (c + 16))) (Z_to_bv 64 ASAN_K)
               (Z_to_bv 64 (Z.of_nat (length bb))) (Z_to_bv 64 (at8 bb pos)) (Z_to_bv 64 body) t3 t4 t5 t6)
          F (Z_to_bv 64 MN_RET_MEMSET) fc None m (seg_rom rsegs)).

(* 0x82210: body[pos] = 0xf0 (the `bne s10, a0` at 0x8220c falls through; a0 = 240). *)
Definition mn_sys_F : Prop :=
  forall (RNG : ExecF.footprint) (sp0 ra0 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word)
         (ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (c mp body : Z) (bb mj : list byte) (pos : nat) (st : Z),
    mn_ctx RNG sp0 ra0 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 m c mp body bb mj pos st ->
    at8 bb pos = 0xf0 ->
    ExecF.evtF rsegs RNG
      (mn_post ra0 sp0 gp tp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 F fc m c mp body bb mj pos st)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - MN_FRAME)) gp tp t0 t1 t2
               (Z_to_bv 64 (shadow_addr (mp + 2))) (Z_to_bv 64 mp) (Z_to_bv 64 240) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 c) (Z_to_bv 64 (Z.of_nat pos)) (Z_to_bv 64 (mp + 2)) (Z_to_bv 64 (body + Z.of_nat pos))
               (Z_to_bv 64 (mp + 8)) (Z_to_bv 64 (shadow_addr (c + 16))) (Z_to_bv 64 ASAN_K)
               (Z_to_bv 64 (Z.of_nat (length bb))) (Z_to_bv 64 (at8 bb pos)) (Z_to_bv 64 body) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8cb20) fc None m (seg_rom rsegs)).

(* 0x823b8: a channel message with status s (s10), its data from index d (a2), m->running := run (a5): reached
   with (s, run, d) = (body[pos], 0, pos + 1) from a status byte 80..ef (0x823b4) and with (st, 1, pos) from a data
   byte under the running status st (0x82290). *)
Definition mn_chan_F : Prop :=
  forall (RNG : ExecF.footprint) (sp0 ra0 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word)
         (ra gp tp t0 t1 t2 a0 a1 a3 a4 a6 a7 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (c mp body : Z) (bb mj : list byte) (pos : nat) (st : Z) (s run : Z) (d : nat),
    mn_ctx RNG sp0 ra0 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 m c mp body bb mj pos st ->
    0x80 <= s < 0xf0 -> (run = 0 \/ run = 1) -> (pos <= d <= S pos)%nat ->
    msg_step bb pos st = chan_step bb pos st s run d ->
    ExecF.evtF rsegs RNG
      (mn_post ra0 sp0 gp tp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 F fc m c mp body bb mj pos st)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - MN_FRAME)) gp tp t0 t1 t2
               (Z_to_bv 64 (shadow_addr (mp + 2))) (Z_to_bv 64 mp) a0 a1 (Z_to_bv 64 (Z.of_nat d)) a3 a4
               (Z_to_bv 64 run) a6 a7
               (Z_to_bv 64 c) (Z_to_bv 64 (Z.of_nat pos)) (Z_to_bv 64 (mp + 2)) (Z_to_bv 64 (body + Z.of_nat pos))
               (Z_to_bv 64 (mp + 8)) (Z_to_bv 64 (shadow_addr (c + 16))) (Z_to_bv 64 ASAN_K)
               (Z_to_bv 64 (Z.of_nat (length bb))) (Z_to_bv 64 s) (Z_to_bv 64 body) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8ccc8) fc None m (seg_rom rsegs)).

(* 0x82528: the epilogue, a0 = the result; m1 is the memory the path left (the frame words still in place, the
   cursor and the message at their final bytes, nothing else changed since m). *)
Definition mn_fin_F : Prop :=
  forall (RNG : ExecF.footprint) (sp0 ra0 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word)
         (ra gp tp t0 t1 t2 y8 y9 a1 a2 a3 a4 a5 a6 a7 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 t3 t4 t5 t6 : word)
         (v0 v8 v16 : word) (F : bvmap 5 word) (fc : bv 32) (m m1 : word -> option byte)
         (c mp body : Z) (bb mj : list byte) (pos : nat) (st : Z),
    MN_FRAME <= bv_unsigned sp0 ->
    ExecF.rng RNG (bv_unsigned sp0 - MN_FRAME) MN_FRAME ->
    rw_cells rsegs m1 (bv_unsigned sp0 - MN_FRAME)
      (mn_fr v0 v8 v16 x27 x26 x25 x24 x23 x22 x21 x20 x19 x18 x9 x8 ra0) ->
    munch [(bv_unsigned sp0 - MN_FRAME, bv_unsigned sp0); (c, c + 25); (mp, mp + 40)] m m1 ->
    rw_cells rsegs m1 c (PCur.cursor_cells body (Z.of_nat (length bb)) (mr_pos (msg_step bb pos st))
                           (mr_st (msg_step bb pos st))) ->
    rw_cells rsegs m1 mp (PMsg.msg_cells body mj (msg_step bb pos st)) ->
    ExecF.evtF rsegs RNG
      (mn_post ra0 sp0 gp tp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 F fc m c mp body bb mj pos st)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - MN_FRAME)) gp tp t0 t1 t2 y8 y9
               (Z_to_bv 64 (mr_code (msg_step bb pos st))) a1 a2 a3 a4 a5 a6 a7
               y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8ce38) fc None m1 (seg_rom rsegs)).
