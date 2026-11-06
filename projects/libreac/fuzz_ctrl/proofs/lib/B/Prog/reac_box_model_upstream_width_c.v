From Stdlib Require Import ZArith List.
From Stdlib Require Import Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcPorts.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_BOX_MODEL_UPSTREAM_WIDTH : Z := 0x87354.
Definition REAC_BOX_MODEL_UPSTREAM_WIDTH_FRAME : Z := 16.

Definition reac_box_model_upstream_width_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mp lo : Z) (bs : list byte),
    bv_unsigned a0 = mp ->
    (mp <> 0 -> mp + 24 <= 2^64 /\ length bs = 8%nat /\ bytes_at rsegs m (mp + 16) bs) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_BOX_MODEL_UPSTREAM_WIDTH_FRAME <= bv_unsigned sp ->
    (mp <> 0 -> mp + 24 <= bv_unsigned sp - REAC_BOX_MODEL_UPSTREAM_WIDTH_FRAME \/ bv_unsigned sp <= mp + 16) ->
    asan_cells m -> shadow_rw m ->
    (mp <> 0 -> mp mod 8 = 0) ->
    (mp <> 0 -> addressable m (mp + 16) 8) ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(bv_unsigned sp - REAC_BOX_MODEL_UPSTREAM_WIDTH_FRAME, bv_unsigned sp)] x) ->
    evt rsegs
      (fun ms' => exists (a1' a2' a3' a4' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bm_uw mp bs))
                       a1' a2' a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - REAC_BOX_MODEL_UPSTREAM_WIDTH_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ (mem_inv rsegs m -> mem_inv rsegs m') /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_BOX_MODEL_UPSTREAM_WIDTH) fc None m (seg_rom rsegs)).

(* Footprint form (RECIPE.md step 1 (a working note, not in this delivery)): the same run as an ExecF.evtF under a footprint RNG, with one rng
   premise per region the run reads or writes: the 16-byte frame, the GOT cell and the runtime cell that hold the
   shadow offset (two 8-byte loads), and, when mp is not 0, the 8 bytes at mp + 16 and their shadow byte (the
   instrumented check loads the byte at ((mp + 16) >> 3) + ASAN_K; mp is 8-aligned, so the 8 bytes have one shadow
   byte). reac_box_model_upstream_width_contract_of_F gives the old statement back with RNG_all. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF.

Definition reac_box_model_upstream_width_contract_F : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mp lo : Z) (bs : list byte),
    bv_unsigned a0 = mp ->
    (mp <> 0 -> mp + 24 <= 2^64 /\ length bs = 8%nat /\ bytes_at rsegs m (mp + 16) bs) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_BOX_MODEL_UPSTREAM_WIDTH_FRAME <= bv_unsigned sp ->
    (mp <> 0 -> mp + 24 <= bv_unsigned sp - REAC_BOX_MODEL_UPSTREAM_WIDTH_FRAME \/ bv_unsigned sp <= mp + 16) ->
    asan_cells m -> shadow_rw m ->
    (mp <> 0 -> mp mod 8 = 0) ->
    (mp <> 0 -> addressable m (mp + 16) 8) ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(bv_unsigned sp - REAC_BOX_MODEL_UPSTREAM_WIDTH_FRAME, bv_unsigned sp)] x) ->
    rng RNG (bv_unsigned sp - REAC_BOX_MODEL_UPSTREAM_WIDTH_FRAME) REAC_BOX_MODEL_UPSTREAM_WIDTH_FRAME ->
    rng RNG GOT_CELL_K 8 -> rng RNG CELL_K 8 ->
    (mp <> 0 -> rng RNG (mp + 16) 8 /\
                rng RNG ((mp + 16) / 8 + ASAN_K) ((mp + 23) / 8 - (mp + 16) / 8 + 1)) ->
    evtF rsegs RNG
      (fun ms' => exists (a1' a2' a3' a4' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bm_uw mp bs))
                       a1' a2' a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - REAC_BOX_MODEL_UPSTREAM_WIDTH_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ (mem_inv rsegs m -> mem_inv rsegs m') /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_BOX_MODEL_UPSTREAM_WIDTH) fc None m (seg_rom rsegs)).

(* RECIPE step 1: the old statement as a corollary of the footprint form at ExecF.RNG_all, every rng premise by
   ExecF.rng_all (the 8 bytes at mp + 16 and their shadow byte are inside the application memory by addressable).
   reac_box_model_upstream_widthF.v proves reac_box_model_upstream_width_contract_F and derives
   reac_box_model_upstream_width_contract from it. *)
Lemma reac_box_model_upstream_width_contract_of_F :
  reac_box_model_upstream_width_contract_F -> reac_box_model_upstream_width_contract.
Proof.
  intros HF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m mp lo bs Ha0 HM ST HLO HD HCE HSW HAL HADR HW.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof ST as (ST0 & ST1 & _).
  pose proof HLO as HLOz. unfold REAC_BOX_MODEL_UPSTREAM_WIDTH_FRAME in HLOz.
  eapply ExecF.evtF_evt,
    (HF ExecF.RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
        t3 t4 t5 t6 F fc m mp lo bs); try assumption.
  - apply ExecF.rng_all; unfold REAC_BOX_MODEL_UPSTREAM_WIDTH_FRAME; lia.
  - apply ExecF.rng_all; unfold GOT_CELL_K; lia.
  - apply ExecF.rng_all; unfold CELL_K; lia.
  - intros E. destruct (HADR E) as (A0 & _ & An & _). unfold APPMEM_END in An.
    unfold ASAN_K.
    split; apply ExecF.rng_all; try Z.div_mod_to_equations; lia.
Qed.


(* Route (C), CORRECTED to a Theorem Labs lane's premise-free form (a Theorem Labs lane 11:26Z measurement; approved a Theorem Labs lane 11:30Z): this run
   reads and stores NO shadow byte THROUGH the shadow_rw premise -- HSW is introduced in reac_box_model_upstream_width.v and never used
   (its shadow bytes come from addressable, rt_shadow_rd) -- so the _on forms DROP `shadow_rw m ->` and name no
   region. Supersedes the narrowed form of c436911dedc, which carried a reac_box_model_upstream_width_shadow_R; that
   predicate is gone. Same names as image A. *)
Definition reac_box_model_upstream_width_contract_on : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mp lo : Z) (bs : list byte),
    bv_unsigned a0 = mp ->
    (mp <> 0 -> mp + 24 <= 2^64 /\ length bs = 8%nat /\ bytes_at rsegs m (mp + 16) bs) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_BOX_MODEL_UPSTREAM_WIDTH_FRAME <= bv_unsigned sp ->
    (mp <> 0 -> mp + 24 <= bv_unsigned sp - REAC_BOX_MODEL_UPSTREAM_WIDTH_FRAME \/ bv_unsigned sp <= mp + 16) ->
    asan_cells m ->
    (mp <> 0 -> mp mod 8 = 0) ->
    (mp <> 0 -> addressable m (mp + 16) 8) ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(bv_unsigned sp - REAC_BOX_MODEL_UPSTREAM_WIDTH_FRAME, bv_unsigned sp)] x) ->
    evt rsegs
      (fun ms' => exists (a1' a2' a3' a4' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bm_uw mp bs))
                       a1' a2' a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - REAC_BOX_MODEL_UPSTREAM_WIDTH_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ (mem_inv rsegs m -> mem_inv rsegs m') /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_BOX_MODEL_UPSTREAM_WIDTH) fc None m (seg_rom rsegs)).

Lemma reac_box_model_upstream_width_contract_of_on : reac_box_model_upstream_width_contract_on -> reac_box_model_upstream_width_contract.
Proof. intros H. unfold reac_box_model_upstream_width_contract. intros. apply H; assumption. Qed.

Definition reac_box_model_upstream_width_contract_F_on : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mp lo : Z) (bs : list byte),
    bv_unsigned a0 = mp ->
    (mp <> 0 -> mp + 24 <= 2^64 /\ length bs = 8%nat /\ bytes_at rsegs m (mp + 16) bs) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_BOX_MODEL_UPSTREAM_WIDTH_FRAME <= bv_unsigned sp ->
    (mp <> 0 -> mp + 24 <= bv_unsigned sp - REAC_BOX_MODEL_UPSTREAM_WIDTH_FRAME \/ bv_unsigned sp <= mp + 16) ->
    asan_cells m ->
    (mp <> 0 -> mp mod 8 = 0) ->
    (mp <> 0 -> addressable m (mp + 16) 8) ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(bv_unsigned sp - REAC_BOX_MODEL_UPSTREAM_WIDTH_FRAME, bv_unsigned sp)] x) ->
    rng RNG (bv_unsigned sp - REAC_BOX_MODEL_UPSTREAM_WIDTH_FRAME) REAC_BOX_MODEL_UPSTREAM_WIDTH_FRAME ->
    rng RNG GOT_CELL_K 8 -> rng RNG CELL_K 8 ->
    (mp <> 0 -> rng RNG (mp + 16) 8 /\
                rng RNG ((mp + 16) / 8 + ASAN_K) ((mp + 23) / 8 - (mp + 16) / 8 + 1)) ->
    evtF rsegs RNG
      (fun ms' => exists (a1' a2' a3' a4' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bm_uw mp bs))
                       a1' a2' a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - REAC_BOX_MODEL_UPSTREAM_WIDTH_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ (mem_inv rsegs m -> mem_inv rsegs m') /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_BOX_MODEL_UPSTREAM_WIDTH) fc None m (seg_rom rsegs)).

Lemma reac_box_model_upstream_width_contract_F_of_on : reac_box_model_upstream_width_contract_F_on -> reac_box_model_upstream_width_contract_F.
Proof. intros H. unfold reac_box_model_upstream_width_contract_F. intros. apply H; assumption. Qed.