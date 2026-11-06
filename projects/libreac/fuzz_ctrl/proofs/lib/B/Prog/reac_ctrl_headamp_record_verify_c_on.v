(* lib/B/Prog/reac_ctrl_headamp_record_verify_c_on.v -- route (C) (a Theorem Labs lane 09:20Z; wave lead a Theorem Labs lane): the ADDITIVE
   `_on` statements of image B's reac_ctrl_headamp_record_verify_c.v, STATEMENTS ONLY (LEAF: it Requires only what
   reac_ctrl_headamp_record_verify_c.v Requires, plus that file). reac_ctrl_headamp_record_verify_c.v stays
   unchanged apart from comment text. The proofs are in lib/B/Prog/reac_ctrl_headamp_record_verify_F_on.v.
   rule 24: no function proved.
   This is the image-B twin of image A's route (C) text (lib/A/Prog/reac_ctrl_headamp_record_verify_c.v, blob
   86718f5a3d6 (the blob this tree had at release c5e779efe8c), :37-75 and :113-154; a Theorem Labs lane's text as a Theorem Labs lane re-took it at 36bfd511da3): the same names,
   comments (lane names aside) and form, which DROP the shadow_rw premise with no region. Image A keeps this text inside its _c.v; image
   B's _c.v is accepted and stays unchanged apart from comment text, so the text is in this new file. The statements differ from A's only
   where image B's accepted contracts differ from A's: the post's existential registers (B: t0' a1' .. a7'; A: a1' ..
   a6', with t0 and a7 kept). *)
(* This delivery then edited comment text only: the code is unchanged from release c5e779efe8c, the comments are not. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLeaf.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import reac_ctrl_headamp_record_verify_c.
Import ListNotations.
Open Scope Z_scope.

(* Route (C) (a Theorem Labs lane 09:20Z; form of a Theorem Labs lane 09:37Z, 09:38Z and 10:33Z): the contract without its shadow_rw premise.
   The run needs no shadow byte present through that premise: it loads one shadow byte, at shadow_addr a, per record
   byte a in p + 18, p + 19 and p + 34 .. p + 39, and addressable m (p + 18) 2 / addressable m (p + 34) 6 already give
   each of those bytes; it stores no shadow byte (its only store is ra into its frame, and the munch post keeps every
   byte outside the frame). So the premise drops, with no region. *)
Definition reac_ctrl_headamp_record_verify_contract_on : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p lo : Z) (b0 b1 : byte) (rec : list byte),
    a0 = Z_to_bv 64 p ->
    0 < p -> p + 40 <= 2^64 ->
    bytes_at rsegs m (p + 18) [b0; b1] ->
    length rec = 6%nat ->
    bytes_at rsegs m (p + 34) rec ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_CTRL_HEADAMP_RECORD_VERIFY_FRAME <= bv_unsigned sp ->
    (p + 20 <= bv_unsigned sp - REAC_CTRL_HEADAMP_RECORD_VERIFY_FRAME \/ bv_unsigned sp <= p + 18) ->
    (p + 40 <= bv_unsigned sp - REAC_CTRL_HEADAMP_RECORD_VERIFY_FRAME \/ bv_unsigned sp <= p + 34) ->
    asan_cells m ->
    addressable m (p + 18) 2 -> addressable m (p + 34) 6 ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(bv_unsigned sp - REAC_CTRL_HEADAMP_RECORD_VERIFY_FRAME, bv_unsigned sp)] x) ->
    evt rsegs
      (fun ms' => exists (t0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 (if hv b0 b1 rec then 0 else -1))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - REAC_CTRL_HEADAMP_RECORD_VERIFY_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ (mem_inv rsegs m -> mem_inv rsegs m') /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_HEADAMP_RECORD_VERIFY) fc None m (seg_rom rsegs)).

(* The old statement from the one without the premise. *)
Lemma reac_ctrl_headamp_record_verify_contract_of_on :
  reac_ctrl_headamp_record_verify_contract_on -> reac_ctrl_headamp_record_verify_contract.
Proof.
  intros H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p lo
    b0 b1 rec H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 _;
    exact (H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p lo
             b0 b1 rec H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11).
Qed.

(* The footprint contract without its shadow_rw premise (the same reason as
   reac_ctrl_headamp_record_verify_contract_on: the shadow bytes of the two shadow rng rows come from addressable). *)
Definition reac_ctrl_headamp_record_verify_contract_F_on : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p lo : Z) (b0 b1 : byte) (rec : list byte),
    a0 = Z_to_bv 64 p ->
    0 < p -> p + 40 <= 2^64 ->
    bytes_at rsegs m (p + 18) [b0; b1] ->
    length rec = 6%nat ->
    bytes_at rsegs m (p + 34) rec ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_CTRL_HEADAMP_RECORD_VERIFY_FRAME <= bv_unsigned sp ->
    (p + 20 <= bv_unsigned sp - REAC_CTRL_HEADAMP_RECORD_VERIFY_FRAME \/ bv_unsigned sp <= p + 18) ->
    (p + 40 <= bv_unsigned sp - REAC_CTRL_HEADAMP_RECORD_VERIFY_FRAME \/ bv_unsigned sp <= p + 34) ->
    asan_cells m ->
    addressable m (p + 18) 2 -> addressable m (p + 34) 6 ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(bv_unsigned sp - REAC_CTRL_HEADAMP_RECORD_VERIFY_FRAME, bv_unsigned sp)] x) ->
    ExecF.rng RNG (bv_unsigned sp - REAC_CTRL_HEADAMP_RECORD_VERIFY_FRAME) REAC_CTRL_HEADAMP_RECORD_VERIFY_FRAME ->
    ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
    ExecF.rng RNG (p + 18) 2 -> ExecF.rng RNG (p + 34) 6 ->
    ExecF.rng RNG (shadow_addr (p + 18)) (shadow_addr (p + 19) - shadow_addr (p + 18) + 1) ->
    ExecF.rng RNG (shadow_addr (p + 34)) (shadow_addr (p + 39) - shadow_addr (p + 34) + 1) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (t0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 (if hv b0 b1 rec then 0 else -1))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - REAC_CTRL_HEADAMP_RECORD_VERIFY_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ (mem_inv rsegs m -> mem_inv rsegs m') /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_HEADAMP_RECORD_VERIFY) fc None m (seg_rom rsegs)).

(* The old footprint statement from the one without the premise. *)
Lemma reac_ctrl_headamp_record_verify_contract_F_of_on :
  reac_ctrl_headamp_record_verify_contract_F_on -> reac_ctrl_headamp_record_verify_contract_F.
Proof.
  intros H RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p
    lo b0 b1 rec H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 _;
    exact (H RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p
             lo b0 b1 rec H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11).
Qed.
