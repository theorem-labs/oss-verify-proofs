From Stdlib Require Import ZArith List.
From Stdlib Require Import Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcPorts.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_BOX_MODEL_UPSTREAM_WIDTH : Z := 0x869c4.
Definition REAC_BOX_MODEL_UPSTREAM_WIDTH_FRAME : Z := 16.

Definition reac_box_model_upstream_width_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mp lo : Z) (bs : list byte),
    bv_unsigned a0 = mp ->
    (mp <> 0 -> mp + 24 <= 2^64 /\ length bs = 8%nat /\ bytes_at rsegs m (mp + 16) bs) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_BOX_MODEL_UPSTREAM_WIDTH_FRAME <= bv_unsigned sp ->
    (mp <> 0 -> mp + 24 <= bv_unsigned sp - REAC_BOX_MODEL_UPSTREAM_WIDTH_FRAME \/ bv_unsigned sp <= mp + 16) ->
    asan_cells m -> shadow_rw m ->
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
   shadow offset (two 8-byte loads), and, when mp is not 0, the 8 bytes at mp + 16 and their shadow bytes (the
   instrumented check loads the bytes at ((mp + 16) >> 3) + ASAN_K and ((mp + 20) >> 3) + ASAN_K; mp need not be
   8-aligned here, as in the old statement, so the span is ((mp + 23) >> 3) - ((mp + 16) >> 3) + 1 shadow bytes).
   reac_box_model_upstream_width_contract_of_F gives the old statement back with RNG_all. *)
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
   ExecF.rng_all (the 8 bytes at mp + 16 and their shadow bytes are inside the application memory by addressable).
   reac_box_model_upstream_widthF.v proves reac_box_model_upstream_width_contract_F and derives
   reac_box_model_upstream_width_contract from it. *)
Lemma reac_box_model_upstream_width_contract_of_F :
  reac_box_model_upstream_width_contract_F -> reac_box_model_upstream_width_contract.
Proof.
  intros HF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m mp lo bs Ha0 HM ST HLO HD HCE HSW HADR HW.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof ST as (ST0 & ST1 & _).
  pose proof HLO as HLOz. unfold REAC_BOX_MODEL_UPSTREAM_WIDTH_FRAME in HLOz.
  eapply ExecF.evtF_evt,
    (HF ExecF.RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
        F fc m mp lo bs); try assumption.
  - apply ExecF.rng_all; unfold REAC_BOX_MODEL_UPSTREAM_WIDTH_FRAME; lia.
  - apply ExecF.rng_all; unfold GOT_CELL_K; lia.
  - apply ExecF.rng_all; unfold CELL_K; lia.
  - intros E. destruct (HADR E) as (A0 & _ & An & _). unfold APPMEM_END in An.
    unfold ASAN_K.
    split; apply ExecF.rng_all; try Z.div_mod_to_equations; lia.
Qed.

(* ---- route (C) (a Theorem Labs lane 09:20Z; wave lead a Theorem Labs lane, form rule 09:37Z): the _on twins. The run reads no shadow byte
   through the universal `shadow_rw m` premise (its two instrumented loads read the shadow of [mp + 16, mp + 24),
   which `addressable m (mp + 16) 8` already supplies), so the premise is DROPPED (no region). The post never stated
   shadow_rw. The old names follow from the twins by dropping that premise. ---- *)
Definition reac_box_model_upstream_width_contract_on : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mp lo : Z) (bs : list byte),
    bv_unsigned a0 = mp ->
    (mp <> 0 -> mp + 24 <= 2^64 /\ length bs = 8%nat /\ bytes_at rsegs m (mp + 16) bs) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_BOX_MODEL_UPSTREAM_WIDTH_FRAME <= bv_unsigned sp ->
    (mp <> 0 -> mp + 24 <= bv_unsigned sp - REAC_BOX_MODEL_UPSTREAM_WIDTH_FRAME \/ bv_unsigned sp <= mp + 16) ->
    asan_cells m ->
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

Definition reac_box_model_upstream_width_contract_F_on : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mp lo : Z) (bs : list byte),
    bv_unsigned a0 = mp ->
    (mp <> 0 -> mp + 24 <= 2^64 /\ length bs = 8%nat /\ bytes_at rsegs m (mp + 16) bs) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_BOX_MODEL_UPSTREAM_WIDTH_FRAME <= bv_unsigned sp ->
    (mp <> 0 -> mp + 24 <= bv_unsigned sp - REAC_BOX_MODEL_UPSTREAM_WIDTH_FRAME \/ bv_unsigned sp <= mp + 16) ->
    asan_cells m ->
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

Lemma reac_box_model_upstream_width_contract_of_on :
  reac_box_model_upstream_width_contract_on -> reac_box_model_upstream_width_contract.
Proof.
  intros HO ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m mp lo bs Ha0 HM ST HLO HD HCE _ HADR HW.
  exact (HO ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m mp lo bs Ha0 HM ST HLO HD HCE HADR HW).
Qed.

Lemma reac_box_model_upstream_width_contract_F_of_on :
  reac_box_model_upstream_width_contract_F_on -> reac_box_model_upstream_width_contract_F.
Proof.
  intros HO RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m mp lo bs Ha0 HM ST HLO HD HCE _ HADR HW.
  exact (HO RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m mp lo bs Ha0 HM ST HLO HD HCE HADR HW).
Qed.

(* The footprint twin gives the plain twin at ExecF.RNG_all, as reac_box_model_upstream_width_contract_of_F does. *)
Lemma reac_box_model_upstream_width_contract_on_of_F_on :
  reac_box_model_upstream_width_contract_F_on -> reac_box_model_upstream_width_contract_on.
Proof.
  intros HF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m mp lo bs Ha0 HM ST HLO HD HCE HADR HW.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof ST as (ST0 & ST1 & _).
  pose proof HLO as HLOz. unfold REAC_BOX_MODEL_UPSTREAM_WIDTH_FRAME in HLOz.
  eapply ExecF.evtF_evt,
    (HF ExecF.RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
        F fc m mp lo bs); try assumption.
  - apply ExecF.rng_all; unfold REAC_BOX_MODEL_UPSTREAM_WIDTH_FRAME; lia.
  - apply ExecF.rng_all; unfold GOT_CELL_K; lia.
  - apply ExecF.rng_all; unfold CELL_K; lia.
  - intros E. destruct (HADR E) as (A0 & _ & An & _). unfold APPMEM_END in An.
    unfold ASAN_K.
    split; apply ExecF.rng_all; try Z.div_mod_to_equations; lia.
Qed.
