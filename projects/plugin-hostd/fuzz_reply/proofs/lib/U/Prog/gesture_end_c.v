From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import send_line_c.
Import ListNotations.
Open Scope Z_scope.

Definition GESTURE_END : Z := 0x14d1c.
Definition GESTURE_END_FRAME : Z := 16.
Definition END5_ADDR : Z := 0x10353.
Definition END5 : list byte := [Z_to_bv 8 32; Z_to_bv 8 101; Z_to_bv 8 110; Z_to_bv 8 100; Z_to_bv 8 0].

Definition gesture_end_nogrow_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
         (x slack junk : list byte) (cl br dd ei : Z) (mx nout cap out ev : word),
    let H := bv_unsigned a0 in
    let XL := Z.of_nat (length x) in
    let LEN := XL + 5 in
    let SW := GESTURE_END_FRAME + SEND_LINE_FRAME in
    let ERR := bv_unsigned tp + ERRNO_OFF in
    let OUTR := bv_unsigned out + bv_unsigned nout in
    let live := send_live cl br dd LEN in
    stk rsegs m lo (bv_unsigned sp) ->
    lo + SW <= bv_unsigned sp ->
    G_RELAY_HI <= ERR -> ERR + 4 <= lo ->
    ERR mod 4 = 0 ->
    0 < H -> H + XL + 1 < 2 ^ 64 ->
    (live = true -> 0 < bv_unsigned out /\ OUTR + LEN < 2 ^ 64) ->
    mem_inv rsegs m ->
    bytes_at rsegs m H (x ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) x ->
    (- (H + XL + 1)) mod 8 <= Z.of_nat (length slack) ->
    1 <= XL ->
    (H + XL + 1 <= G_RELAY_LO \/ G_RELAY_HI <= H) ->
    (H + XL + 1 <= ERR \/ ERR + 4 <= H) ->
    (H + XL + 1 <= bv_unsigned sp - SW \/ bv_unsigned sp <= H) ->
    (cl = 3 \/ cl = -1) -> (br = 0 \/ br = 1) -> (dd = 0 \/ dd = 1) -> (ei = 0 \/ ei = 1) ->
    rw_cells rsegs m G_CLIENT [C4 (Z_to_bv 64 cl)] ->
    rw_cells rsegs m G_BROKEN [C1 (Z_to_bv 8 br)] ->
    rw_cells rsegs m G_DEAD [C1 (Z_to_bv 8 dd)] ->
    rw_cells rsegs m G_EINTR [C1 (Z_to_bv 8 ei)] ->
    rw_cells rsegs m G_OUTV [C8 mx; C8 nout; C8 cap; C8 out] ->
    rw_cells rsegs m ERR [C4 ev] ->
    (live = true ->
       rw_cells rsegs m OUTR [CB (Z.to_nat LEN) junk] /\
       bv_unsigned nout + LEN <= bv_unsigned cap /\
       G_RELAY_HI <= OUTR /\
       (OUTR + LEN <= ERR \/ ERR + 4 <= OUTR) /\
       OUTR + LEN <= lo /\
       (H + XL + 1 <= OUTR \/ OUTR + LEN <= H)) ->
    let off := send_off cl br LEN in
    let br' := if off then br else dd in
    let ei' := if off then ei else 0 in
    let nout' := if live then Z_to_bv 64 (bv_unsigned nout + LEN) else nout in
    let ev' := if off then ev
               else if dd =? 1 then Z_to_bv 64 EPIPE_V
               else if ei =? 1 then Z_to_bv 64 EINTR_V
               else ev in
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch ([(bv_unsigned sp - SW, bv_unsigned sp); (ERR, ERR + 4);
                 (G_BROKEN, G_BROKEN + 1); (G_EINTR, G_EINTR + 1); (G_OUTV + 8, G_OUTV + 16)]
                ++ (if live then [(OUTR, OUTR + LEN)] else [])) m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         mem_inv rsegs m' /\
         bytes_at rsegs m' H (x ++ [Z_to_bv 8 0]) /\
         rw_cells rsegs m' G_CLIENT [C4 (Z_to_bv 64 cl)] /\
         rw_cells rsegs m' G_BROKEN [C1 (Z_to_bv 8 br')] /\
         rw_cells rsegs m' G_DEAD [C1 (Z_to_bv 8 dd)] /\
         rw_cells rsegs m' G_EINTR [C1 (Z_to_bv 8 ei')] /\
         rw_cells rsegs m' G_OUTV [C8 mx; C8 nout'; C8 cap; C8 out] /\
         rw_cells rsegs m' ERR [C4 ev'] /\
         (live = true -> rw_cells rsegs m' OUTR [CB (Z.to_nat LEN) (x ++ END5)]))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 GESTURE_END) fc None m (seg_rom rsegs)).
