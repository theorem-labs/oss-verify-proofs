From Stdlib Require Import ZArith List.
From Stdlib Require Import Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_CTRL_CHECKSUM_VERIFY : Z := 0x83b94.
Definition REAC_CTRL_CHECKSUM_VERIFY_FRAME : Z := 16.

Definition reac_ctrl_checksum_verify_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p lo : Z) (bs : list byte),
    0 < p -> p + 50 <= 2^64 ->
    a0 = Z_to_bv 64 p ->
    length bs = 32%nat ->
    bytes_at rsegs m (p + 18) bs ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_CTRL_CHECKSUM_VERIFY_FRAME <= bv_unsigned sp ->
    (p + 50 <= bv_unsigned sp - REAC_CTRL_CHECKSUM_VERIFY_FRAME \/ bv_unsigned sp <= p + 18) ->
    asan_cells m -> shadow_rw m ->
    addressable m (p + 18) 32 ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(bv_unsigned sp - REAC_CTRL_CHECKSUM_VERIFY_FRAME, bv_unsigned sp)] x) ->
    evt rsegs
      (fun ms' => exists (t0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 (if blocksum bs =? 0 then 0 else -1))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - REAC_CTRL_CHECKSUM_VERIFY_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ (mem_inv rsegs m -> mem_inv rsegs m') /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_CHECKSUM_VERIFY) fc None m (seg_rom rsegs)).

(* Route (C) (a Theorem Labs lane 09:20Z; form of a Theorem Labs lane 09:37Z, 09:38Z and 10:33Z): the contract without its shadow_rw premise.
   The run needs no shadow byte present through that premise: it loads one shadow byte, at shadow_addr a, per data
   byte a in [p + 18, p + 50), and addressable m (p + 18) 32 already gives each of those bytes (rt_shadow_rd /
   rt_addressable in reac_ctrl_checksum_verify.v and reac_ctrl_checksum_verify_F.v, which introduce the shadow_rw
   premise and never use it); it stores no shadow byte (the munch post keeps every byte outside its 16-byte frame).
   So the premise drops, with no region. Twin of image A's reac_ctrl_checksum_verify_c.v (a Theorem Labs lane 70b81742a12). *)
Definition reac_ctrl_checksum_verify_contract_on : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p lo : Z) (bs : list byte),
    0 < p -> p + 50 <= 2^64 ->
    a0 = Z_to_bv 64 p ->
    length bs = 32%nat ->
    bytes_at rsegs m (p + 18) bs ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_CTRL_CHECKSUM_VERIFY_FRAME <= bv_unsigned sp ->
    (p + 50 <= bv_unsigned sp - REAC_CTRL_CHECKSUM_VERIFY_FRAME \/ bv_unsigned sp <= p + 18) ->
    asan_cells m ->
    addressable m (p + 18) 32 ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(bv_unsigned sp - REAC_CTRL_CHECKSUM_VERIFY_FRAME, bv_unsigned sp)] x) ->
    evt rsegs
      (fun ms' => exists (t0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 (if blocksum bs =? 0 then 0 else -1))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - REAC_CTRL_CHECKSUM_VERIFY_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ (mem_inv rsegs m -> mem_inv rsegs m') /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_CHECKSUM_VERIFY) fc None m (seg_rom rsegs)).

(* The old statement from the one without the premise. *)
Lemma reac_ctrl_checksum_verify_contract_of_on :
  reac_ctrl_checksum_verify_contract_on -> reac_ctrl_checksum_verify_contract.
Proof.
  intros H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p lo bs
    H1 H2 H3 H4 H5 H6 H7 H8 H9 _;
    exact (H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p lo
             bs H1 H2 H3 H4 H5 H6 H7 H8 H9).
Qed.

(* Footprint form: the same run as an ExecF.evtF under a footprint RNG, with one rng premise per region the run
   reads or writes: the 16-byte frame (ra save/restore), the GOT cell and the runtime cell of the shadow offset
   (two 8-byte loads), the 32 data bytes, and the shadow bytes of the 32 data bytes (one 1-byte load at
   (a >> 3) + ASAN_K per data byte a). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF.

Definition reac_ctrl_checksum_verify_contract_F : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p lo : Z) (bs : list byte),
    0 < p -> p + 50 <= 2^64 ->
    a0 = Z_to_bv 64 p ->
    length bs = 32%nat ->
    bytes_at rsegs m (p + 18) bs ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_CTRL_CHECKSUM_VERIFY_FRAME <= bv_unsigned sp ->
    (p + 50 <= bv_unsigned sp - REAC_CTRL_CHECKSUM_VERIFY_FRAME \/ bv_unsigned sp <= p + 18) ->
    asan_cells m -> shadow_rw m ->
    addressable m (p + 18) 32 ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(bv_unsigned sp - REAC_CTRL_CHECKSUM_VERIFY_FRAME, bv_unsigned sp)] x) ->
    rng RNG (bv_unsigned sp - REAC_CTRL_CHECKSUM_VERIFY_FRAME) REAC_CTRL_CHECKSUM_VERIFY_FRAME ->
    rng RNG GOT_CELL_K 8 -> rng RNG CELL_K 8 ->
    rng RNG (p + 18) 32 ->
    rng RNG ((p + 18) / 8 + ASAN_K) ((p + 49) / 8 - (p + 18) / 8 + 1) ->
    evtF rsegs RNG
      (fun ms' => exists (t0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 (if blocksum bs =? 0 then 0 else -1))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - REAC_CTRL_CHECKSUM_VERIFY_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ (mem_inv rsegs m -> mem_inv rsegs m') /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_CHECKSUM_VERIFY) fc None m (seg_rom rsegs)).

(* The footprint contract without its shadow_rw premise (the same reason as reac_ctrl_checksum_verify_contract_on:
   the shadow bytes the run loads, the rng row ((p + 18) / 8 + ASAN_K) .., come from addressable). *)
Definition reac_ctrl_checksum_verify_contract_F_on : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p lo : Z) (bs : list byte),
    0 < p -> p + 50 <= 2^64 ->
    a0 = Z_to_bv 64 p ->
    length bs = 32%nat ->
    bytes_at rsegs m (p + 18) bs ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_CTRL_CHECKSUM_VERIFY_FRAME <= bv_unsigned sp ->
    (p + 50 <= bv_unsigned sp - REAC_CTRL_CHECKSUM_VERIFY_FRAME \/ bv_unsigned sp <= p + 18) ->
    asan_cells m ->
    addressable m (p + 18) 32 ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(bv_unsigned sp - REAC_CTRL_CHECKSUM_VERIFY_FRAME, bv_unsigned sp)] x) ->
    rng RNG (bv_unsigned sp - REAC_CTRL_CHECKSUM_VERIFY_FRAME) REAC_CTRL_CHECKSUM_VERIFY_FRAME ->
    rng RNG GOT_CELL_K 8 -> rng RNG CELL_K 8 ->
    rng RNG (p + 18) 32 ->
    rng RNG ((p + 18) / 8 + ASAN_K) ((p + 49) / 8 - (p + 18) / 8 + 1) ->
    evtF rsegs RNG
      (fun ms' => exists (t0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 (if blocksum bs =? 0 then 0 else -1))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - REAC_CTRL_CHECKSUM_VERIFY_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ (mem_inv rsegs m -> mem_inv rsegs m') /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_CHECKSUM_VERIFY) fc None m (seg_rom rsegs)).

(* The old footprint statement from the one without the premise. *)
Lemma reac_ctrl_checksum_verify_contract_F_of_on :
  reac_ctrl_checksum_verify_contract_F_on -> reac_ctrl_checksum_verify_contract_F.
Proof.
  intros H RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p
    lo bs H1 H2 H3 H4 H5 H6 H7 H8 H9 _;
    exact (H RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p
             lo bs H1 H2 H3 H4 H5 H6 H7 H8 H9).
Qed.

(* The plain statement without the premise from the footprint one at RNG_all (the script of image B's
   reac_ctrl_checksum_verify_holds_of_F in reac_ctrl_checksum_verify_F.v, without the shadow_rw premise). *)
Lemma reac_ctrl_checksum_verify_contract_of_F_on :
  reac_ctrl_checksum_verify_contract_F_on -> reac_ctrl_checksum_verify_contract_on.
Proof.
  intros HF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m p lo bs Hp Hp50 Ha0 Hlen HB ST HLO HD HCE HADR HW.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof ST as (ST0 & _ & _).
  pose proof HLO as HLO'. unfold REAC_CTRL_CHECKSUM_VERIFY_FRAME in HLO'.
  apply (evtF_evt rsegs RNG_all).
  apply (HF RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p lo bs); try assumption;
    apply rng_all; unfold REAC_CTRL_CHECKSUM_VERIFY_FRAME, GOT_CELL_K, CELL_K, ASAN_K;
    Z.div_mod_to_equations; lia.
Qed.
