From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Definition SEND_LINE : Z := 0x131bc.
Definition SEND_LINE_FRAME : Z := 96.
Definition G_CLIENT : Z := 0x20d3c.
Definition G_RELAY_LO : Z := 0x30fc0.
Definition G_BROKEN : Z := 0x30fc4.
Definition G_DEAD : Z := 0x30fcc.
Definition G_EINTR : Z := 0x30fd0.
Definition G_OUTV : Z := 0x30ff8.
Definition G_RELAY_HI : Z := 0x31018.
Definition ERRNO_OFF : Z := -164.
Definition EINTR_V : Z := 4.
Definition EPIPE_V : Z := 32.

Definition send_off (cl br len : Z) : bool := (cl <? 0) || (br =? 1) || (len =? 0).
Definition send_live (cl br dd len : Z) : bool := negb (send_off cl br len) && (dd =? 0).

Definition send_line_nogrow_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
         (B junk : list byte) (cl br dd ei : Z) (mx nout cap out ev : word),
    let LINE := bv_unsigned a0 in
    let LEN := bv_unsigned a1 in
    let ERR := bv_unsigned tp + ERRNO_OFF in
    let OUTR := bv_unsigned out + bv_unsigned nout in
    let live := send_live cl br dd LEN in
    stk rsegs m lo (bv_unsigned sp) ->
    lo + SEND_LINE_FRAME <= bv_unsigned sp ->
    G_RELAY_HI <= ERR -> ERR + 4 <= lo ->
    mem_inv rsegs m ->
    bytes_at rsegs m LINE B -> Z.of_nat (length B) = LEN ->
    (LINE + LEN <= G_RELAY_LO \/ G_RELAY_HI <= LINE) ->
    (LINE + LEN <= ERR \/ ERR + 4 <= LINE) ->
    (LINE + LEN <= bv_unsigned sp - SEND_LINE_FRAME \/ bv_unsigned sp <= LINE) ->
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
       (LINE + LEN <= OUTR \/ OUTR + LEN <= LINE)) ->
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
         munch ([(bv_unsigned sp - SEND_LINE_FRAME, bv_unsigned sp); (ERR, ERR + 4);
                 (G_BROKEN, G_BROKEN + 1); (G_EINTR, G_EINTR + 1); (G_OUTV + 8, G_OUTV + 16)]
                ++ (if live then [(OUTR, OUTR + LEN)] else [])) m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         mem_inv rsegs m' /\
         bytes_at rsegs m' LINE B /\
         rw_cells rsegs m' G_CLIENT [C4 (Z_to_bv 64 cl)] /\
         rw_cells rsegs m' G_BROKEN [C1 (Z_to_bv 8 br')] /\
         rw_cells rsegs m' G_DEAD [C1 (Z_to_bv 8 dd)] /\
         rw_cells rsegs m' G_EINTR [C1 (Z_to_bv 8 ei')] /\
         rw_cells rsegs m' G_OUTV [C8 mx; C8 nout'; C8 cap; C8 out] /\
         rw_cells rsegs m' ERR [C4 ev'] /\
         (live = true -> rw_cells rsegs m' OUTR [CB (Z.to_nat LEN) B]))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SEND_LINE) fc None m (seg_rom rsegs)).
