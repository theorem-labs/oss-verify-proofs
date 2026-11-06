(* lib/B/Prog/reac_box_model_block_cF_on.v -- route (C) (a Theorem Labs lane 09:20Z; wave lead a Theorem Labs lane): the ADDITIVE `_on` form of
   reac_box_model_block's FOOTPRINT contract, STATEMENT ONLY, for the lifted image-B runs that call it through the
   footprint form (reac_box_catalogue_matchF_on.v :3519, ctrl_lay_blockF_on.v :4355).  IMAGE B ONLY, as a Theorem Labs lane's
   asan_stack_malloc_cF_on.v: image A has no footprint twin.  A Theorem Labs lane, 2026-10-29.

   SOURCE OF THE TEXT: reac_box_model_block_contract_F and reac_box_model_block_post, lib/B/Prog/reac_box_model_block_c.v
   (blob 2339efccffe), character for character.  THE TWO CHANGES (script-checked, see the commit):
     1. the universal premise `shadow_rw m` becomes
        `shadow_rw_on (reac_box_model_block_shadow_R (bv_unsigned sp) FS p b o row nb) m`;
     2. the post reac_box_model_block_post becomes a Theorem Labs lane's reac_box_model_block_post_on (whose only change against
        reac_box_model_block_post is the region transport `forall P : Z -> Prop, shadow_rw_on P m -> shadow_rw_on P m'`).
   Every other binder, premise (the footprint ones included) and post conjunct is the accepted text.

   reac_box_model_block_shadow_R and reac_box_model_block_post_on are a Theorem Labs lane's, cited BY NAME from
   lib/B/Prog/reac_box_model_block_c_on.v 1b2bf09eaa2 (the blob this tree had at release c5e779efe8c) (a working branch a87f2d57299), which Requires the
   reac_box_model_block_c.v (unchanged apart from comment text).

   THERE IS NO PROOF of this form (statement only).  It is STRONGER than reac_box_model_block_contract_F, so NO proof may
   assume it until reac_box_model_block's run narrows (route (C) phase 2) and proves it.
   rule 24: no function proved.  proves no function (kind: statement text). *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcBox RcSynth.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import asan_stack_malloc_c RcAsanFP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import reac_box_model_block_c reac_box_model_block_c_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF RngBytes.
Import ListNotations.
Open Scope Z_scope.

Definition reac_box_model_block_contract_F_on : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p b o FS : Z) (row nb ob : list byte),
    a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 b -> a2 = Z_to_bv 64 o ->
    0 <= p < 2^64 -> 0 <= b < 2^64 -> 0 <= o < 2^64 ->
    bv_unsigned sp mod 16 = 0 ->
    stk rsegs m (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) (bv_unsigned sp) ->
    (p <> 0 -> p mod 8 = 0 /\ length row = 296%nat /\ bytes_at rsegs m p row /\
               (bv_unsigned sp <= p \/ p + 296 <= bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) /\
               (o = 0 \/ o + 32 <= p \/ p + 296 <= o)) ->
    (p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
               name_ok nb /\ bytes_at rsegs m (rname row) nb /\
               (bv_unsigned sp <= rname row \/
                rname row + Z.of_nat (length nb) <= bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) /\
               (o = 0 \/ o + 32 <= rname row \/ rname row + Z.of_nat (length nb) <= o)) ->
    (o <> 0 -> rw_cells rsegs m o [CB 32 ob] /\
               (bv_unsigned sp <= o \/ o + 32 <= bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) /\
               (o + 32 <= JOIN_0013 \/ JOIN_0014 + 32 <= o)) ->
    mem_inv rsegs m ->
    (* asan-ubsan *)
    asan_cells m -> shadow_rw_on (reac_box_model_block_shadow_R (bv_unsigned sp) FS p b o row nb) m ->
    HIGHMEM_BEG <= bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K -> bv_unsigned sp <= APPMEM_END ->
    addressable m (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) REAC_BOX_MODEL_BLOCK_K ->
    (p <> 0 -> addressable m p 296) ->
    (p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
               addressable m (rname row) (Z.of_nat (length nb))) ->
    (o <> 0 -> addressable m o 32 /\ app_mem (o + 32) /\ (o + 32 <= RT_LO \/ RT_HI <= o)) ->
    (b = 1 -> addressable m JOIN_0014 32) -> (b = 2 -> addressable m JOIN_0013 32) ->
    fp [0%nat] m (bv_unsigned tp) FS (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) (bv_unsigned sp)
      (reac_box_model_block_W o (bv_unsigned sp)) (reac_box_model_block_D p o) ->
    (p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
               fp_dj [(rname row, rname row + Z.of_nat (length nb))] (fp_w [0%nat] FS)) ->
    reac_box_model_block_tls m (bv_unsigned tp) FS (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) (bv_unsigned sp) ->
    (* the footprint is byte-wise (the callees __asan_memcpy / __asan_memset carry it), then the regions the run
       reads or writes *)
    RngBytes.rng_bytes RNG ->
    ExecF.rng RNG 0x10000 0x5ee000 ->
    ExecF.rng RNG (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) REAC_BOX_MODEL_BLOCK_K ->
    sh_cover RNG (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) REAC_BOX_MODEL_BLOCK_K ->
    ExecF.rng RNG FS (fs_frame FS 0%nat 0 - FS) ->
    Forall (fun iv => ExecF.rng RNG (fst iv) (snd iv - fst iv)) (fp_w [0%nat] FS) ->
    (forall DT TS C T DB k, asan_tls_cells m (bv_unsigned tp) DT TS C T DB k ->
       Forall (fun iv => ExecF.rng RNG (fst iv) (snd iv - fst iv)) (fp_tls (bv_unsigned tp) DT TS C T DB k)) ->
    (p <> 0 -> ExecF.rng RNG (p + 16) 275 /\ sh_cover RNG (p + 16) 275) ->
    (p <> 0 -> o <> 0 -> ExecF.rng RNG o 32 /\ sh_cover RNG o 32) ->
    (b = 1 -> sh_cover RNG JOIN_0014 32) ->
    (b = 2 -> sh_cover RNG JOIN_0013 32) ->
    (p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
       ExecF.rng RNG (rname row) (Z.of_nat (length nb)) /\ sh_cover RNG (rname row) (Z.of_nat (length nb))) ->
    ExecF.evtF rsegs RNG
      (reac_box_model_block_post_on ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_BOX_MODEL_BLOCK) fc None m (seg_rom rsegs)).
