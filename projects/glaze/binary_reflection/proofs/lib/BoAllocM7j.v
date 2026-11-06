(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_50a9c_51a9c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM7 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM7i. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_50a9c_51a9c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM7 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM7i.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

Section FPGen1.
Context {fx : FPState}.

Section RFJ.
  Variable segs : list Segment.
  Variable rb : word.
  Hypothesis HRF : code_ato segs rb 0x5143c rf_words.
  Hypothesis RB : (U rb mod 2 = 0)%Z /\ (U rb + 2 ^ 24 < 2 ^ 64)%Z.

  Lemma R5143c : fetch_word segs (at_ rb 0x5143c) = Some W_5143c.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 0 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R51440 : fetch_word segs (at_ rb 0x51440) = Some W_51440.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 1 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R51444 : fetch_word segs (at_ rb 0x51444) = Some W_51444.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 2 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R51448 : fetch_word segs (at_ rb 0x51448) = Some W_51448.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 3 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R5144c : fetch_word segs (at_ rb 0x5144c) = Some W_5144c.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 4 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R51450 : fetch_word segs (at_ rb 0x51450) = Some W_51450.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 5 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R51454 : fetch_word segs (at_ rb 0x51454) = Some W_51454.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 6 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R51458 : fetch_word segs (at_ rb 0x51458) = Some W_51458.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 7 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R5145c : fetch_word segs (at_ rb 0x5145c) = Some W_5145c.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 8 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R51460 : fetch_word segs (at_ rb 0x51460) = Some W_51460.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 9 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R51464 : fetch_word segs (at_ rb 0x51464) = Some W_51464.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 10 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R51468 : fetch_word segs (at_ rb 0x51468) = Some W_51468.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 11 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R5146c : fetch_word segs (at_ rb 0x5146c) = Some W_5146c.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 12 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R51470 : fetch_word segs (at_ rb 0x51470) = Some W_51470.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 13 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R51474 : fetch_word segs (at_ rb 0x51474) = Some W_51474.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 14 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R51478 : fetch_word segs (at_ rb 0x51478) = Some W_51478.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 15 _ HRF eq_refl). Qed.






   (* [comment removed for export] *)
  Lemma R51498 : fetch_word segs (at_ rb 0x51498) = Some W_51498.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 23 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R5149c : fetch_word segs (at_ rb 0x5149c) = Some W_5149c.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 24 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R514a0 : fetch_word segs (at_ rb 0x514a0) = Some W_514a0.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 25 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R514a4 : fetch_word segs (at_ rb 0x514a4) = Some W_514a4.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 26 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R514a8 : fetch_word segs (at_ rb 0x514a8) = Some W_514a8.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 27 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R514ac : fetch_word segs (at_ rb 0x514ac) = Some W_514ac.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 28 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R514b0 : fetch_word segs (at_ rb 0x514b0) = Some W_514b0.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 29 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R514b4 : fetch_word segs (at_ rb 0x514b4) = Some W_514b4.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 30 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R514b8 : fetch_word segs (at_ rb 0x514b8) = Some W_514b8.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 31 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R514bc : fetch_word segs (at_ rb 0x514bc) = Some W_514bc.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 32 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R514c0 : fetch_word segs (at_ rb 0x514c0) = Some W_514c0.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 33 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R514c4 : fetch_word segs (at_ rb 0x514c4) = Some W_514c4.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 34 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R514c8 : fetch_word segs (at_ rb 0x514c8) = Some W_514c8.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 35 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R514cc : fetch_word segs (at_ rb 0x514cc) = Some W_514cc.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 36 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R514d0 : fetch_word segs (at_ rb 0x514d0) = Some W_514d0.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 37 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R514d4 : fetch_word segs (at_ rb 0x514d4) = Some W_514d4.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 38 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R514d8 : fetch_word segs (at_ rb 0x514d8) = Some W_514d8.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 39 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R514dc : fetch_word segs (at_ rb 0x514dc) = Some W_514dc.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 40 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R514e0 : fetch_word segs (at_ rb 0x514e0) = Some W_514e0.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 41 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R514e4 : fetch_word segs (at_ rb 0x514e4) = Some W_514e4.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 42 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R514e8 : fetch_word segs (at_ rb 0x514e8) = Some W_514e8.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 43 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R514ec : fetch_word segs (at_ rb 0x514ec) = Some W_514ec.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 44 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R514f0 : fetch_word segs (at_ rb 0x514f0) = Some W_514f0.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 45 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R514f4 : fetch_word segs (at_ rb 0x514f4) = Some W_514f4.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 46 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R514f8 : fetch_word segs (at_ rb 0x514f8) = Some W_514f8.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 47 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R514fc : fetch_word segs (at_ rb 0x514fc) = Some W_514fc.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 48 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R51500 : fetch_word segs (at_ rb 0x51500) = Some W_51500.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 49 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R51504 : fetch_word segs (at_ rb 0x51504) = Some W_51504.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 50 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R51508 : fetch_word segs (at_ rb 0x51508) = Some W_51508.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 51 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R5150c : fetch_word segs (at_ rb 0x5150c) = Some W_5150c.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 52 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R51510 : fetch_word segs (at_ rb 0x51510) = Some W_51510.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 53 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R51514 : fetch_word segs (at_ rb 0x51514) = Some W_51514.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 54 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R51518 : fetch_word segs (at_ rb 0x51518) = Some W_51518.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 55 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R5151c : fetch_word segs (at_ rb 0x5151c) = Some W_5151c.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 56 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R51520 : fetch_word segs (at_ rb 0x51520) = Some W_51520.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 57 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R51524 : fetch_word segs (at_ rb 0x51524) = Some W_51524.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 58 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R51528 : fetch_word segs (at_ rb 0x51528) = Some W_51528.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 59 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R5152c : fetch_word segs (at_ rb 0x5152c) = Some W_5152c.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 60 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R51530 : fetch_word segs (at_ rb 0x51530) = Some W_51530.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 61 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R51534 : fetch_word segs (at_ rb 0x51534) = Some W_51534.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 62 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R51538 : fetch_word segs (at_ rb 0x51538) = Some W_51538.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 63 _ HRF eq_refl). Qed.   (* [comment removed for export] *)

  Variables (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ra sp cache pc alloc : word) (c : Z).
  Hypothesis Hret : ret_ok ra.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H10 : getr regs 10 = cache.
  Hypothesis H11 : getr regs 11 = pc.
  Hypothesis H12 : getr regs 12 = alloc.
  Hypothesis H13 : getr regs 13 = Z_to_bv 64 c.
  Hypothesis Hstk : store_ok segs mem (at_ sp (-32)) 32 = true.
  Hypothesis G1 : (2 ^ 32 + 32 <= U sp)%Z /\ (U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Gpc : (U cache + 2640 <= U sp - 32)%Z /\ (U pc = U cache + 80 * c)%Z /\ (1 <= c <= 30)%Z.
  Hypothesis HTW : store_ok segs mem (at_ cache 80) 2480 = true.      (* [comment removed for export] *)
  #[local] Abbreviation RFM1 := (rf_m1 regs mem ra sp).
  #[local] Abbreviation ICM k := (ic_mem regs mem ra sp cache k).

  Ltac sokS Hs0 lo N :=
    repeat (eapply store_ok_mono; [apply wbytes_grows|]);
    eapply (store_ok_sub segs mem lo _ N); [rewrite at_u; lia | exact Hs0 | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia].
  Ltac fsd8 F D aa :=
    chain_step; [reflexivity
      | eapply step_sd_at with (a := aa);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
        | gres; rwH; reflexivity
        | sokS Hstk (at_ sp (-32)) 32%nat ]
      | step_simpl]; vn.
  Ltac vz := cbv delta [v_add v_addi v_mul v_slli v_srli v_sub] beta; rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia; unorm;
             first [reflexivity | f_equal; lia | apply bv_eq; wd_ulia].
  (* [comment removed for export] *)
  Ltac grows_ic := lazymatch goal with
    | |- mem_grows ?m ?m => apply mem_grows_refl
    | |- mem_grows _ (wbytes _ _ _) => eapply mem_grows_trans; [|apply wbytes_grows]; grows_ic
    | |- mem_grows _ (ic_mem _ _ _ _ _ _) => apply ic_mem_grows
    | |- mem_grows _ (rf_m1 _ _ _ _) => apply rf_m1_grows
    end.
  Ltac sokT := eapply (store_ok_mono segs _ mem); [grows_ic|];
    eapply (store_ok_sub segs mem (at_ cache 80) _ 2480%nat); [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | exact HTW | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ] | rewrite !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia].
  Ltac fsw4 F D aa :=
    chain_step; [reflexivity
      | eapply step_sw_at with (a := aa);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
        | gres; rwH; reflexivity
        | sokT ]
      | step_simpl]; vn.
  Ltac fsd8c F D aa :=
    chain_step; [reflexivity
      | eapply step_sd_at with (a := aa);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
        | gres; rwH; reflexivity
        | sokT ]
      | step_simpl]; vn.
  (* [comment removed for export] *)
  Ltac icK Hx := first [ gres_frame Hx | repeat (rewrite getr_other; [| let E := fresh in intros E; apply Hx; rewrite E; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto]); reflexivity ].

  Lemma ic_20_23 : forall r,
      getr r 11 = at_ cache 1608 -> getr r 13 = Z_to_bv 64 640 -> getr r 15 = Z_to_bv 64 4 -> getr r 16 = Z_to_bv 64 15 -> getr r 17 = Z_to_bv 64 1024 -> getr r 5 = Z_to_bv 64 16 -> getr r 6 = Z_to_bv 64 17 -> getr r 7 = Z_to_bv 64 512 ->
      exists r', msteps segs (mkst r (at_ rb 0x514e0) (ICM 19) rom) (mkst r' (at_ rb 0x514e0) (ICM 23) rom)
        /\ (getr r' 11 = at_ cache 1928 /\ getr r' 13 = Z_to_bv 64 768 /\ getr r' 15 = Z_to_bv 64 8 /\ getr r' 16 = Z_to_bv 64 15 /\ getr r' 17 = Z_to_bv 64 1024 /\ getr r' 5 = Z_to_bv 64 16 /\ getr r' 6 = Z_to_bv 64 17 /\ getr r' 7 = Z_to_bv 64 512)
        /\ (forall x : reg, ~ In x [11; 13; 15; 16; 17; 5; 6; 7; 28; 29; 30] -> getr r' x = getr r x).
  Proof using HTW Gpc G1 c pc RB HRF.
    intros r Q11 Q13 Q15 Q16 Q17 Q5 Q6 Q7.
    destruct G1 as [G1a G1b]. destruct Gpc as (Gp1 & Gp2 & Gp3). pose proof (u64_range sp) as Hspr. pose proof (u64_range cache). pose proof (u64_range pc).
    wd_eexists. split; [|split].
    -
      (* [comment removed for export] *)
      ab_ft R514e0 D_514e0 ltac:(condz). an R514e4 D_514e4. an R514e8 D_514e8. ab_ft R514ec D_514ec ltac:(condz).
      an R514f0 D_514f0. an R514f4 D_514f4. an R514f8 D_514f8. an R514fc D_514fc. an R51500 D_51500. an R51504 D_51504. an R51508 D_51508.
      an R5150c D_5150c. an R51510 D_51510. ab_tk R51514 D_51514 ltac:(condz).
      an R514bc D_514bc. an R514c0 D_514c0. an R514c4 D_514c4. an R514c8 D_514c8. an R514cc D_514cc.
      fsw4 R514d0 D_514d0 (at_ cache 1604). fsd8c R514d4 D_514d4 (at_ cache 1608).
      change (wbytes (wbytes (ICM 19) _ _) _ _) with (ICM 20).
      an R514d8 D_514d8.
      ab_ft R514dc D_514dc ltac:(condz).
      (* [comment removed for export] *)
      ab_ft R514e0 D_514e0 ltac:(condz). an R514e4 D_514e4. an R514e8 D_514e8. ab_ft R514ec D_514ec ltac:(condz).
      an R514f0 D_514f0. an R514f4 D_514f4. an R514f8 D_514f8. an R514fc D_514fc. an R51500 D_51500. an R51504 D_51504. an R51508 D_51508.
      an R5150c D_5150c. an R51510 D_51510. ab_tk R51514 D_51514 ltac:(condz).
      an R514bc D_514bc. an R514c0 D_514c0. an R514c4 D_514c4. an R514c8 D_514c8. an R514cc D_514cc.
      fsw4 R514d0 D_514d0 (at_ cache 1684). fsd8c R514d4 D_514d4 (at_ cache 1688).
      change (wbytes (wbytes (ICM 20) _ _) _ _) with (ICM 21).
      an R514d8 D_514d8.
      ab_ft R514dc D_514dc ltac:(condz).
      (* [comment removed for export] *)
      ab_ft R514e0 D_514e0 ltac:(condz). an R514e4 D_514e4. an R514e8 D_514e8. ab_ft R514ec D_514ec ltac:(condz).
      an R514f0 D_514f0. an R514f4 D_514f4. an R514f8 D_514f8. an R514fc D_514fc. an R51500 D_51500. an R51504 D_51504. an R51508 D_51508.
      an R5150c D_5150c. an R51510 D_51510. ab_tk R51514 D_51514 ltac:(condz).
      an R514bc D_514bc. an R514c0 D_514c0. an R514c4 D_514c4. an R514c8 D_514c8. an R514cc D_514cc.
      fsw4 R514d0 D_514d0 (at_ cache 1764). fsd8c R514d4 D_514d4 (at_ cache 1768).
      change (wbytes (wbytes (ICM 21) _ _) _ _) with (ICM 22).
      an R514d8 D_514d8.
      ab_ft R514dc D_514dc ltac:(condz).
      (* [comment removed for export] *)
      ab_ft R514e0 D_514e0 ltac:(condz). an R514e4 D_514e4. an R514e8 D_514e8. ab_ft R514ec D_514ec ltac:(condz).
      an R514f0 D_514f0. an R514f4 D_514f4. an R514f8 D_514f8. an R514fc D_514fc. an R51500 D_51500. an R51504 D_51504. an R51508 D_51508.
      an R5150c D_5150c. an R51510 D_51510. ab_tk R51514 D_51514 ltac:(condz).
      an R514bc D_514bc. an R514c0 D_514c0. an R514c4 D_514c4. an R514c8 D_514c8. an R514cc D_514cc.
      fsw4 R514d0 D_514d0 (at_ cache 1844). fsd8c R514d4 D_514d4 (at_ cache 1848).
      change (wbytes (wbytes (ICM 22) _ _) _ _) with (ICM 23).
      an R514d8 D_514d8.
      ab_ft R514dc D_514dc ltac:(condz).
      wd_refl.
    - repeat split; gres; first [reflexivity | assumption].
    - intros x Hx. gres. icK Hx.
  Qed.

  Lemma ic_24_27 : forall r,
      getr r 11 = at_ cache 1928 -> getr r 13 = Z_to_bv 64 768 -> getr r 15 = Z_to_bv 64 8 -> getr r 16 = Z_to_bv 64 15 -> getr r 17 = Z_to_bv 64 1024 -> getr r 5 = Z_to_bv 64 16 -> getr r 6 = Z_to_bv 64 17 -> getr r 7 = Z_to_bv 64 512 ->
      exists r', msteps segs (mkst r (at_ rb 0x514e0) (ICM 23) rom) (mkst r' (at_ rb 0x514e0) (ICM 27) rom)
        /\ (getr r' 11 = at_ cache 2248 /\ getr r' 13 = Z_to_bv 64 896 /\ getr r' 15 = Z_to_bv 64 12 /\ getr r' 16 = Z_to_bv 64 15 /\ getr r' 17 = Z_to_bv 64 1024 /\ getr r' 5 = Z_to_bv 64 16 /\ getr r' 6 = Z_to_bv 64 17 /\ getr r' 7 = Z_to_bv 64 512)
        /\ (forall x : reg, ~ In x [11; 13; 15; 16; 17; 5; 6; 7; 28; 29; 30] -> getr r' x = getr r x).
  Proof using HTW Gpc G1 c pc RB HRF.
    intros r Q11 Q13 Q15 Q16 Q17 Q5 Q6 Q7.
    destruct G1 as [G1a G1b]. destruct Gpc as (Gp1 & Gp2 & Gp3). pose proof (u64_range sp) as Hspr. pose proof (u64_range cache). pose proof (u64_range pc).
    wd_eexists. split; [|split].
    -
      (* [comment removed for export] *)
      ab_ft R514e0 D_514e0 ltac:(condz). an R514e4 D_514e4. an R514e8 D_514e8. ab_ft R514ec D_514ec ltac:(condz).
      an R514f0 D_514f0. an R514f4 D_514f4. an R514f8 D_514f8. an R514fc D_514fc. an R51500 D_51500. an R51504 D_51504. an R51508 D_51508.
      an R5150c D_5150c. an R51510 D_51510. ab_tk R51514 D_51514 ltac:(condz).
      an R514bc D_514bc. an R514c0 D_514c0. an R514c4 D_514c4. an R514c8 D_514c8. an R514cc D_514cc.
      fsw4 R514d0 D_514d0 (at_ cache 1924). fsd8c R514d4 D_514d4 (at_ cache 1928).
      change (wbytes (wbytes (ICM 23) _ _) _ _) with (ICM 24).
      an R514d8 D_514d8.
      ab_ft R514dc D_514dc ltac:(condz).
      (* [comment removed for export] *)
      ab_ft R514e0 D_514e0 ltac:(condz). an R514e4 D_514e4. an R514e8 D_514e8. ab_ft R514ec D_514ec ltac:(condz).
      an R514f0 D_514f0. an R514f4 D_514f4. an R514f8 D_514f8. an R514fc D_514fc. an R51500 D_51500. an R51504 D_51504. an R51508 D_51508.
      an R5150c D_5150c. an R51510 D_51510. ab_tk R51514 D_51514 ltac:(condz).
      an R514bc D_514bc. an R514c0 D_514c0. an R514c4 D_514c4. an R514c8 D_514c8. an R514cc D_514cc.
      fsw4 R514d0 D_514d0 (at_ cache 2004). fsd8c R514d4 D_514d4 (at_ cache 2008).
      change (wbytes (wbytes (ICM 24) _ _) _ _) with (ICM 25).
      an R514d8 D_514d8.
      ab_ft R514dc D_514dc ltac:(condz).
      (* [comment removed for export] *)
      ab_ft R514e0 D_514e0 ltac:(condz). an R514e4 D_514e4. an R514e8 D_514e8. ab_ft R514ec D_514ec ltac:(condz).
      an R514f0 D_514f0. an R514f4 D_514f4. an R514f8 D_514f8. an R514fc D_514fc. an R51500 D_51500. an R51504 D_51504. an R51508 D_51508.
      an R5150c D_5150c. an R51510 D_51510. ab_tk R51514 D_51514 ltac:(condz).
      an R514bc D_514bc. an R514c0 D_514c0. an R514c4 D_514c4. an R514c8 D_514c8. an R514cc D_514cc.
      fsw4 R514d0 D_514d0 (at_ cache 2084). fsd8c R514d4 D_514d4 (at_ cache 2088).
      change (wbytes (wbytes (ICM 25) _ _) _ _) with (ICM 26).
      an R514d8 D_514d8.
      ab_ft R514dc D_514dc ltac:(condz).
      (* [comment removed for export] *)
      ab_ft R514e0 D_514e0 ltac:(condz). an R514e4 D_514e4. an R514e8 D_514e8. ab_ft R514ec D_514ec ltac:(condz).
      an R514f0 D_514f0. an R514f4 D_514f4. an R514f8 D_514f8. an R514fc D_514fc. an R51500 D_51500. an R51504 D_51504. an R51508 D_51508.
      an R5150c D_5150c. an R51510 D_51510. ab_tk R51514 D_51514 ltac:(condz).
      an R514bc D_514bc. an R514c0 D_514c0. an R514c4 D_514c4. an R514c8 D_514c8. an R514cc D_514cc.
      fsw4 R514d0 D_514d0 (at_ cache 2164). fsd8c R514d4 D_514d4 (at_ cache 2168).
      change (wbytes (wbytes (ICM 26) _ _) _ _) with (ICM 27).
      an R514d8 D_514d8.
      ab_ft R514dc D_514dc ltac:(condz).
      wd_refl.
    - repeat split; gres; first [reflexivity | assumption].
    - intros x Hx. gres. icK Hx.
  Qed.

  Lemma ic_28_30 : forall r,
      getr r 11 = at_ cache 2248 -> getr r 13 = Z_to_bv 64 896 -> getr r 15 = Z_to_bv 64 12 -> getr r 16 = Z_to_bv 64 15 -> getr r 17 = Z_to_bv 64 1024 -> getr r 5 = Z_to_bv 64 16 -> getr r 6 = Z_to_bv 64 17 -> getr r 7 = Z_to_bv 64 512 ->
      exists r', msteps segs (mkst r (at_ rb 0x514e0) (ICM 27) rom) (mkst r' (at_ rb 0x514e0) (ICM 30) rom)
        /\ (getr r' 11 = at_ cache 2488 /\ getr r' 13 = Z_to_bv 64 992 /\ getr r' 15 = Z_to_bv 64 15 /\ getr r' 16 = Z_to_bv 64 15 /\ getr r' 17 = Z_to_bv 64 1024 /\ getr r' 5 = Z_to_bv 64 16 /\ getr r' 6 = Z_to_bv 64 17 /\ getr r' 7 = Z_to_bv 64 512)
        /\ (forall x : reg, ~ In x [11; 13; 15; 16; 17; 5; 6; 7; 28; 29; 30] -> getr r' x = getr r x).
  Proof using HTW Gpc G1 c pc RB HRF.
    intros r Q11 Q13 Q15 Q16 Q17 Q5 Q6 Q7.
    destruct G1 as [G1a G1b]. destruct Gpc as (Gp1 & Gp2 & Gp3). pose proof (u64_range sp) as Hspr. pose proof (u64_range cache). pose proof (u64_range pc).
    wd_eexists. split; [|split].
    -
      (* [comment removed for export] *)
      ab_ft R514e0 D_514e0 ltac:(condz). an R514e4 D_514e4. an R514e8 D_514e8. ab_ft R514ec D_514ec ltac:(condz).
      an R514f0 D_514f0. an R514f4 D_514f4. an R514f8 D_514f8. an R514fc D_514fc. an R51500 D_51500. an R51504 D_51504. an R51508 D_51508.
      an R5150c D_5150c. an R51510 D_51510. ab_tk R51514 D_51514 ltac:(condz).
      an R514bc D_514bc. an R514c0 D_514c0. an R514c4 D_514c4. an R514c8 D_514c8. an R514cc D_514cc.
      fsw4 R514d0 D_514d0 (at_ cache 2244). fsd8c R514d4 D_514d4 (at_ cache 2248).
      change (wbytes (wbytes (ICM 27) _ _) _ _) with (ICM 28).
      an R514d8 D_514d8.
      ab_ft R514dc D_514dc ltac:(condz).
      (* [comment removed for export] *)
      ab_ft R514e0 D_514e0 ltac:(condz). an R514e4 D_514e4. an R514e8 D_514e8. ab_ft R514ec D_514ec ltac:(condz).
      an R514f0 D_514f0. an R514f4 D_514f4. an R514f8 D_514f8. an R514fc D_514fc. an R51500 D_51500. an R51504 D_51504. an R51508 D_51508.
      an R5150c D_5150c. an R51510 D_51510. ab_tk R51514 D_51514 ltac:(condz).
      an R514bc D_514bc. an R514c0 D_514c0. an R514c4 D_514c4. an R514c8 D_514c8. an R514cc D_514cc.
      fsw4 R514d0 D_514d0 (at_ cache 2324). fsd8c R514d4 D_514d4 (at_ cache 2328).
      change (wbytes (wbytes (ICM 28) _ _) _ _) with (ICM 29).
      an R514d8 D_514d8.
      ab_ft R514dc D_514dc ltac:(condz).
      (* [comment removed for export] *)
      ab_ft R514e0 D_514e0 ltac:(condz). an R514e4 D_514e4. an R514e8 D_514e8. ab_ft R514ec D_514ec ltac:(condz).
      an R514f0 D_514f0. an R514f4 D_514f4. an R514f8 D_514f8. an R514fc D_514fc. an R51500 D_51500. an R51504 D_51504. an R51508 D_51508.
      an R5150c D_5150c. an R51510 D_51510. ab_tk R51514 D_51514 ltac:(condz).
      an R514bc D_514bc. an R514c0 D_514c0. an R514c4 D_514c4. an R514c8 D_514c8. an R514cc D_514cc.
      fsw4 R514d0 D_514d0 (at_ cache 2404). fsd8c R514d4 D_514d4 (at_ cache 2408).
      change (wbytes (wbytes (ICM 29) _ _) _ _) with (ICM 30).
      an R514d8 D_514d8.
      ab_ft R514dc D_514dc ltac:(condz).
      wd_refl.
    - repeat split; gres; first [reflexivity | assumption].
    - intros x Hx. gres. icK Hx.
  Qed.

  Lemma ic_31 : forall r,
      getr r 11 = at_ cache 2488 -> getr r 13 = Z_to_bv 64 992 -> getr r 15 = Z_to_bv 64 15 -> getr r 16 = Z_to_bv 64 15 -> getr r 17 = Z_to_bv 64 1024 -> getr r 5 = Z_to_bv 64 16 -> getr r 6 = Z_to_bv 64 17 -> getr r 7 = Z_to_bv 64 512 ->
      exists r', msteps segs (mkst r (at_ rb 0x514e0) (ICM 30) rom) (mkst r' (at_ rb 0x51534) (ICM 31) rom)
        /\ (forall x : reg, ~ In x [11; 13; 15; 16; 17; 5; 6; 7; 28; 29; 30] -> getr r' x = getr r x).
  Proof using HTW Gpc G1 c pc RB HRF.
    intros r Q11 Q13 Q15 Q16 Q17 Q5 Q6 Q7.
    destruct G1 as [G1a G1b]. destruct Gpc as (Gp1 & Gp2 & Gp3). pose proof (u64_range sp) as Hspr. pose proof (u64_range cache). pose proof (u64_range pc).
    wd_eexists. split.
    -
      (* [comment removed for export] *)
      ab_tk R514e0 D_514e0 ltac:(condz). an R51520 D_51520. an R51524 D_51524. an R51528 D_51528. ab_ft R5152c D_5152c ltac:(condz). an R51530 D_51530. an R51518 D_51518. an R5151c D_5151c.
      an R514bc D_514bc. an R514c0 D_514c0. an R514c4 D_514c4. an R514c8 D_514c8. an R514cc D_514cc.
      fsw4 R514d0 D_514d0 (at_ cache 2484). fsd8c R514d4 D_514d4 (at_ cache 2488).
      change (wbytes (wbytes (ICM 30) _ _) _ _) with (ICM 31).
      an R514d8 D_514d8.
      ab_tk R514dc D_514dc ltac:(condz).
      wd_refl.
    - intros x Hx. gres. icK Hx.
  Qed.


  (* [comment removed for export] *)
  Lemma rf_pro0 :
    rdn segs mem (at_ pc 4) 4 = Some (LE4 0) ->
    exists r,
      msteps segs (mkst regs (at_ rb 0x5143c) mem rom) (mkst r (at_ rb 0x5153c) (ICM 31) rom)
      /\ getr r 1 = at_ rb 0x5147c /\ getr r 2 = at_ sp (-32) /\ getr r 8 = pc /\ getr r 9 = Z_to_bv 64 (icmc c / 2)
      /\ getr r 10 = alloc /\ getr r 11 = at_ cache 2560 /\ getr r 12 = Z_to_bv 64 c /\ getr r 13 = at_ pc 16 /\ getr r 14 = Z_to_bv 64 (icmc c / 2)
      /\ regs_agree (fun i : reg => In i [1; 2; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30]) regs r.
  Proof using HTW Gpc G1 Hstk H13 H12 H11 H10 H2 H1 RB HRF.
    intros Rmc0.
    destruct G1 as [G1a G1b]. destruct Gpc as (Gp1 & Gp2 & Gp3). pose proof (u64_range sp) as Hspr. pose proof (u64_range cache). pose proof (u64_range pc).
    pose proof (icmc_range c ltac:(lia)) as [Ic1 Ic2].
    (* [comment removed for export] *)
    assert (P0 : exists r0, msteps segs (mkst regs (at_ rb 0x5143c) mem rom) (mkst r0 (at_ rb 0x514e0) (ICM 0) rom)
              /\ (getr r0 11 = at_ cache 88 /\ getr r0 13 = Z_to_bv 64 32 /\ getr r0 15 = Z_to_bv 64 18446744073709551601 /\ getr r0 16 = Z_to_bv 64 15
                  /\ getr r0 17 = Z_to_bv 64 1024 /\ getr r0 5 = Z_to_bv 64 16 /\ getr r0 6 = Z_to_bv 64 17 /\ getr r0 7 = Z_to_bv 64 512)
              /\ getr r0 2 = at_ sp (-32) /\ getr r0 8 = pc /\ getr r0 10 = cache /\ getr r0 12 = alloc /\ getr r0 14 = Z_to_bv 64 c
              /\ regs_agree (fun i : reg => In i [1; 2; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30]) regs r0).
    { wd_eexists. split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
      - an R5143c D_5143c.                                   (* [comment removed for export] *)
        fsd8 R51440 D_51440 (at_ sp (-8)).                   (* [comment removed for export] *)
        fsd8 R51444 D_51444 (at_ sp (-16)).                  (* [comment removed for export] *)
        fsd8 R51448 D_51448 (at_ sp (-24)).                  (* [comment removed for export] *)
        change (wbytes _ _ _) with RFM1.
        an R5144c D_5144c.                                   (* [comment removed for export] *)
        an R51450 D_51450.                                   (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_lw with (bs := LE4 0) (v := Z_to_bv 64 0);
            [exact R51454 | reflexivity | exact D_51454
            | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at;
              rewrite <- Rmc0; apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply (rf_m1_outside rb regs mem ra sp G1); rewrite at_u in Hx by lia; cbn in Hx; lia]
            | apply bytes4_small; lia]
          | step_simpl]; rewrite (v_lw_small 0) by lia; vn.   (* [comment removed for export] *)
        ab_tk R51458 D_51458 ltac:(condz).                  (* [comment removed for export] *)
        an R51498 D_51498.                                   (* [comment removed for export] *)
        an R5149c D_5149c. an R514a0 D_514a0. an R514a4 D_514a4. an R514a8 D_514a8.   (* [comment removed for export] *)
        an R514ac D_514ac. an R514b0 D_514b0. an R514b4 D_514b4.                      (* [comment removed for export] *)
        an R514b8 D_514b8.                                   (* [comment removed for export] *)
        wd_refl.
      - repeat split; gres; reflexivity.
      - gres; reflexivity. - gres; rwH; reflexivity. - gres; rwH; reflexivity. - gres; rwH; reflexivity. - gres; rwH; reflexivity.
      - ra_solve. }
    destruct P0 as (r0 & RUN0 & (A11 & A13 & A15 & A16 & A17 & A5 & A6 & A7) & A2 & A8 & A10 & A12 & A14 & AK).
    Ltac icstep L r A11 A13 A15 A16 A17 A5 A6 A7 :=
      destruct (L r A11 A13 A15 A16 A17 A5 A6 A7) as (?r & ?RUN & (?B11 & ?B13 & ?B15 & ?B16 & ?B17 & ?B5 & ?B6 & ?B7) & ?BK).
    destruct (ic_1_5 segs rb HRF RB regs mem rom ra sp cache pc c G1 Gpc HTW r0 A11 A13 A15 A16 A17 A5 A6 A7) as (r1 & RUN1 & (B11 & B13 & B15 & B16 & B17 & B5 & B6 & B7) & BK1).
    destruct (ic_6_10 segs rb HRF RB regs mem rom ra sp cache pc c G1 Gpc HTW r1 B11 B13 B15 B16 B17 B5 B6 B7) as (r2 & RUN2 & (C11 & C13 & C15 & C16 & C17 & C5 & C6 & C7) & BK2).
    destruct (ic_11_15 segs rb HRF RB regs mem rom ra sp cache pc c G1 Gpc HTW r2 C11 C13 C15 C16 C17 C5 C6 C7) as (r3 & RUN3 & (D11 & D13 & D15 & D16 & D17 & D5 & D6 & D7) & BK3).
    destruct (ic_16_19 segs rb HRF RB regs mem rom ra sp cache pc c G1 Gpc HTW r3 D11 D13 D15 D16 D17 D5 D6 D7) as (r4 & RUN4 & (E11 & E13 & E15 & E16 & E17 & E5 & E6 & E7) & BK4).
    destruct (ic_20_23 r4 E11 E13 E15 E16 E17 E5 E6 E7) as (r5 & RUN5 & (F11 & F13 & F15 & F16 & F17 & F5 & F6 & F7) & BK5).
    destruct (ic_24_27 r5 F11 F13 F15 F16 F17 F5 F6 F7) as (r6 & RUN6 & (I11 & I13 & I15 & I16 & I17 & I5 & I6 & I7) & BK6).
    destruct (ic_28_30 r6 I11 I13 I15 I16 I17 I5 I6 I7) as (r7 & RUN7 & (J11 & J13 & J15 & J16 & J17 & J5 & J6 & J7) & BK7).
    destruct (ic_31 r7 J11 J13 J15 J16 J17 J5 J6 J7) as (r8 & RUN8 & BK8).
    assert (KK : forall x : reg, ~ In x [11; 13; 15; 16; 17; 5; 6; 7; 28; 29; 30] -> getr r8 x = getr r0 x).
    { intros x Hx. rewrite (BK8 x Hx), (BK7 x Hx), (BK6 x Hx), (BK5 x Hx), (BK4 x Hx), (BK3 x Hx), (BK2 x Hx). exact (BK1 x Hx). }
    assert (K2 : getr r8 2 = at_ sp (-32)) by (rewrite KK by notin; exact A2).
    assert (K8 : getr r8 8 = pc) by (rewrite KK by notin; exact A8).
    assert (K10 : getr r8 10 = cache) by (rewrite KK by notin; exact A10).
    assert (K12 : getr r8 12 = alloc) by (rewrite KK by notin; exact A12).
    assert (K14 : getr r8 14 = Z_to_bv 64 c) by (rewrite KK by notin; exact A14).
    assert (Rmc31 : rdn segs (ICM 31) (at_ pc 4) 4 = Some (LE4 (icmc c))).
    { replace (at_ pc 4) with (at_ cache (80 * c + 4)) by (apply bv_eq; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ]). apply (ic_mem_mc segs rb regs mem ra sp cache pc c G1 Gpc); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia. }
    wd_eexists. split.
    - eapply msteps_trans; [exact RUN0|]. eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|].
      eapply msteps_trans; [exact RUN4|]. eapply msteps_trans; [exact RUN5|]. eapply msteps_trans; [exact RUN6|]. eapply msteps_trans; [exact RUN7|].
      eapply msteps_trans; [exact RUN8|].
      chain_step; [reflexivity
        | eapply step_lw with (bs := LE4 (icmc c)) (v := Z_to_bv 64 (icmc c));
          [exact R51534 | reflexivity | exact D_51534
          | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; exact Rmc31
          | apply bytes4_small; lia]
        | step_simpl]; rewrite (v_lw_small (icmc c)) by lia; vn.   (* [comment removed for export] *)
      an R51538 D_51538.                                   (* [comment removed for export] *)
      an R5145c D_5145c. rewrite (v_srliw1_small (icmc c)) by lia.   (* [comment removed for export] *)
      an R51460 D_51460.                                   (* [comment removed for export] *)
      av R51464 D_51464 (at_ cache 2560) ltac:(rewrite ?at_at; vz).   (* [comment removed for export] *)
      av R51468 D_51468 (at_ pc 16) ltac:(vz).            (* [comment removed for export] *)
      an R5146c D_5146c.                                   (* [comment removed for export] *)
      an R51470 D_51470.                                   (* [comment removed for export] *)
      an R51474 D_51474.                                   (* [comment removed for export] *)
      an R51478 D_51478.                                   (* [comment removed for export] *)
      wd_refl.
    - post.
      repeat (first [ apply regs_agree_upd; [solve [in_list] |]
                    | apply regs_agree_upd_keep; [ | first [reflexivity | rwH; rewrite ?at_0; reflexivity | symmetry; assumption] | let X := fresh in intros X; discriminate X ] ]).
      intros x Hx. rewrite KK; [exact (AK x Hx)|]. intros Hin. apply Hx. cbn [In] in Hin |- *. first [ solve [clear - Hin; tauto] | tauto ].
  Qed.

End RFJ.
End FPGen1.
