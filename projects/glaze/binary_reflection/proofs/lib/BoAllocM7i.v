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
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_50a9c_51a9c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM7. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_50a9c_51a9c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM7.
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

Section RFI.
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

  Lemma ic_1_5 : forall r,
      getr r 11 = at_ cache 88 -> getr r 13 = Z_to_bv 64 32 -> getr r 15 = Z_to_bv 64 18446744073709551601 -> getr r 16 = Z_to_bv 64 15 -> getr r 17 = Z_to_bv 64 1024 -> getr r 5 = Z_to_bv 64 16 -> getr r 6 = Z_to_bv 64 17 -> getr r 7 = Z_to_bv 64 512 ->
      exists r', msteps segs (mkst r (at_ rb 0x514e0) (ICM 0) rom) (mkst r' (at_ rb 0x514e0) (ICM 5) rom)
        /\ (getr r' 11 = at_ cache 488 /\ getr r' 13 = Z_to_bv 64 192 /\ getr r' 15 = Z_to_bv 64 18446744073709551606 /\ getr r' 16 = Z_to_bv 64 15 /\ getr r' 17 = Z_to_bv 64 1024 /\ getr r' 5 = Z_to_bv 64 16 /\ getr r' 6 = Z_to_bv 64 17 /\ getr r' 7 = Z_to_bv 64 512)
        /\ (forall x : reg, ~ In x [11; 13; 15; 16; 17; 5; 6; 7; 28; 29; 30] -> getr r' x = getr r x).
  Proof using HTW Gpc G1 c pc RB HRF.
    intros r Q11 Q13 Q15 Q16 Q17 Q5 Q6 Q7.
    destruct G1 as [G1a G1b]. destruct Gpc as (Gp1 & Gp2 & Gp3). pose proof (u64_range sp) as Hspr. pose proof (u64_range cache). pose proof (u64_range pc).
    wd_eexists. split; [|split].
    -
      (* [comment removed for export] *)
      ab_ft R514e0 D_514e0 ltac:(condz). an R514e4 D_514e4. an R514e8 D_514e8. ab_tk R514ec D_514ec ltac:(condz).
      an R5150c D_5150c. an R51510 D_51510. ab_ft R51514 D_51514 ltac:(condz). an R51518 D_51518. an R5151c D_5151c.
      an R514bc D_514bc. an R514c0 D_514c0. an R514c4 D_514c4. an R514c8 D_514c8. an R514cc D_514cc.
      fsw4 R514d0 D_514d0 (at_ cache 84). fsd8c R514d4 D_514d4 (at_ cache 88).
      change (wbytes (wbytes (ICM 0) _ _) _ _) with (ICM 1).
      an R514d8 D_514d8.
      ab_ft R514dc D_514dc ltac:(condz).
      (* [comment removed for export] *)
      ab_ft R514e0 D_514e0 ltac:(condz). an R514e4 D_514e4. an R514e8 D_514e8. ab_tk R514ec D_514ec ltac:(condz).
      an R5150c D_5150c. an R51510 D_51510. ab_ft R51514 D_51514 ltac:(condz). an R51518 D_51518. an R5151c D_5151c.
      an R514bc D_514bc. an R514c0 D_514c0. an R514c4 D_514c4. an R514c8 D_514c8. an R514cc D_514cc.
      fsw4 R514d0 D_514d0 (at_ cache 164). fsd8c R514d4 D_514d4 (at_ cache 168).
      change (wbytes (wbytes (ICM 1) _ _) _ _) with (ICM 2).
      an R514d8 D_514d8.
      ab_ft R514dc D_514dc ltac:(condz).
      (* [comment removed for export] *)
      ab_ft R514e0 D_514e0 ltac:(condz). an R514e4 D_514e4. an R514e8 D_514e8. ab_tk R514ec D_514ec ltac:(condz).
      an R5150c D_5150c. an R51510 D_51510. ab_ft R51514 D_51514 ltac:(condz). an R51518 D_51518. an R5151c D_5151c.
      an R514bc D_514bc. an R514c0 D_514c0. an R514c4 D_514c4. an R514c8 D_514c8. an R514cc D_514cc.
      fsw4 R514d0 D_514d0 (at_ cache 244). fsd8c R514d4 D_514d4 (at_ cache 248).
      change (wbytes (wbytes (ICM 2) _ _) _ _) with (ICM 3).
      an R514d8 D_514d8.
      ab_ft R514dc D_514dc ltac:(condz).
      (* [comment removed for export] *)
      ab_ft R514e0 D_514e0 ltac:(condz). an R514e4 D_514e4. an R514e8 D_514e8. ab_tk R514ec D_514ec ltac:(condz).
      an R5150c D_5150c. an R51510 D_51510. ab_ft R51514 D_51514 ltac:(condz). an R51518 D_51518. an R5151c D_5151c.
      an R514bc D_514bc. an R514c0 D_514c0. an R514c4 D_514c4. an R514c8 D_514c8. an R514cc D_514cc.
      fsw4 R514d0 D_514d0 (at_ cache 324). fsd8c R514d4 D_514d4 (at_ cache 328).
      change (wbytes (wbytes (ICM 3) _ _) _ _) with (ICM 4).
      an R514d8 D_514d8.
      ab_ft R514dc D_514dc ltac:(condz).
      (* [comment removed for export] *)
      ab_ft R514e0 D_514e0 ltac:(condz). an R514e4 D_514e4. an R514e8 D_514e8. ab_tk R514ec D_514ec ltac:(condz).
      an R5150c D_5150c. an R51510 D_51510. ab_tk R51514 D_51514 ltac:(condz).
      an R514bc D_514bc. an R514c0 D_514c0. an R514c4 D_514c4. an R514c8 D_514c8. an R514cc D_514cc.
      fsw4 R514d0 D_514d0 (at_ cache 404). fsd8c R514d4 D_514d4 (at_ cache 408).
      change (wbytes (wbytes (ICM 4) _ _) _ _) with (ICM 5).
      an R514d8 D_514d8.
      ab_ft R514dc D_514dc ltac:(condz).
      wd_refl.
    - repeat split; gres; first [reflexivity | assumption].
    - intros x Hx. gres. icK Hx.
  Qed.

  Lemma ic_6_10 : forall r,
      getr r 11 = at_ cache 488 -> getr r 13 = Z_to_bv 64 192 -> getr r 15 = Z_to_bv 64 18446744073709551606 -> getr r 16 = Z_to_bv 64 15 -> getr r 17 = Z_to_bv 64 1024 -> getr r 5 = Z_to_bv 64 16 -> getr r 6 = Z_to_bv 64 17 -> getr r 7 = Z_to_bv 64 512 ->
      exists r', msteps segs (mkst r (at_ rb 0x514e0) (ICM 5) rom) (mkst r' (at_ rb 0x514e0) (ICM 10) rom)
        /\ (getr r' 11 = at_ cache 888 /\ getr r' 13 = Z_to_bv 64 352 /\ getr r' 15 = Z_to_bv 64 18446744073709551611 /\ getr r' 16 = Z_to_bv 64 15 /\ getr r' 17 = Z_to_bv 64 1024 /\ getr r' 5 = Z_to_bv 64 16 /\ getr r' 6 = Z_to_bv 64 17 /\ getr r' 7 = Z_to_bv 64 512)
        /\ (forall x : reg, ~ In x [11; 13; 15; 16; 17; 5; 6; 7; 28; 29; 30] -> getr r' x = getr r x).
  Proof using HTW Gpc G1 c pc RB HRF.
    intros r Q11 Q13 Q15 Q16 Q17 Q5 Q6 Q7.
    destruct G1 as [G1a G1b]. destruct Gpc as (Gp1 & Gp2 & Gp3). pose proof (u64_range sp) as Hspr. pose proof (u64_range cache). pose proof (u64_range pc).
    wd_eexists. split; [|split].
    -
      (* [comment removed for export] *)
      ab_ft R514e0 D_514e0 ltac:(condz). an R514e4 D_514e4. an R514e8 D_514e8. ab_tk R514ec D_514ec ltac:(condz).
      an R5150c D_5150c. an R51510 D_51510. ab_tk R51514 D_51514 ltac:(condz).
      an R514bc D_514bc. an R514c0 D_514c0. an R514c4 D_514c4. an R514c8 D_514c8. an R514cc D_514cc.
      fsw4 R514d0 D_514d0 (at_ cache 484). fsd8c R514d4 D_514d4 (at_ cache 488).
      change (wbytes (wbytes (ICM 5) _ _) _ _) with (ICM 6).
      an R514d8 D_514d8.
      ab_ft R514dc D_514dc ltac:(condz).
      (* [comment removed for export] *)
      ab_ft R514e0 D_514e0 ltac:(condz). an R514e4 D_514e4. an R514e8 D_514e8. ab_tk R514ec D_514ec ltac:(condz).
      an R5150c D_5150c. an R51510 D_51510. ab_tk R51514 D_51514 ltac:(condz).
      an R514bc D_514bc. an R514c0 D_514c0. an R514c4 D_514c4. an R514c8 D_514c8. an R514cc D_514cc.
      fsw4 R514d0 D_514d0 (at_ cache 564). fsd8c R514d4 D_514d4 (at_ cache 568).
      change (wbytes (wbytes (ICM 6) _ _) _ _) with (ICM 7).
      an R514d8 D_514d8.
      ab_ft R514dc D_514dc ltac:(condz).
      (* [comment removed for export] *)
      ab_ft R514e0 D_514e0 ltac:(condz). an R514e4 D_514e4. an R514e8 D_514e8. ab_tk R514ec D_514ec ltac:(condz).
      an R5150c D_5150c. an R51510 D_51510. ab_tk R51514 D_51514 ltac:(condz).
      an R514bc D_514bc. an R514c0 D_514c0. an R514c4 D_514c4. an R514c8 D_514c8. an R514cc D_514cc.
      fsw4 R514d0 D_514d0 (at_ cache 644). fsd8c R514d4 D_514d4 (at_ cache 648).
      change (wbytes (wbytes (ICM 7) _ _) _ _) with (ICM 8).
      an R514d8 D_514d8.
      ab_ft R514dc D_514dc ltac:(condz).
      (* [comment removed for export] *)
      ab_ft R514e0 D_514e0 ltac:(condz). an R514e4 D_514e4. an R514e8 D_514e8. ab_tk R514ec D_514ec ltac:(condz).
      an R5150c D_5150c. an R51510 D_51510. ab_tk R51514 D_51514 ltac:(condz).
      an R514bc D_514bc. an R514c0 D_514c0. an R514c4 D_514c4. an R514c8 D_514c8. an R514cc D_514cc.
      fsw4 R514d0 D_514d0 (at_ cache 724). fsd8c R514d4 D_514d4 (at_ cache 728).
      change (wbytes (wbytes (ICM 8) _ _) _ _) with (ICM 9).
      an R514d8 D_514d8.
      ab_ft R514dc D_514dc ltac:(condz).
      (* [comment removed for export] *)
      ab_ft R514e0 D_514e0 ltac:(condz). an R514e4 D_514e4. an R514e8 D_514e8. ab_tk R514ec D_514ec ltac:(condz).
      an R5150c D_5150c. an R51510 D_51510. ab_tk R51514 D_51514 ltac:(condz).
      an R514bc D_514bc. an R514c0 D_514c0. an R514c4 D_514c4. an R514c8 D_514c8. an R514cc D_514cc.
      fsw4 R514d0 D_514d0 (at_ cache 804). fsd8c R514d4 D_514d4 (at_ cache 808).
      change (wbytes (wbytes (ICM 9) _ _) _ _) with (ICM 10).
      an R514d8 D_514d8.
      ab_ft R514dc D_514dc ltac:(condz).
      wd_refl.
    - repeat split; gres; first [reflexivity | assumption].
    - intros x Hx. gres. icK Hx.
  Qed.

  Lemma ic_11_15 : forall r,
      getr r 11 = at_ cache 888 -> getr r 13 = Z_to_bv 64 352 -> getr r 15 = Z_to_bv 64 18446744073709551611 -> getr r 16 = Z_to_bv 64 15 -> getr r 17 = Z_to_bv 64 1024 -> getr r 5 = Z_to_bv 64 16 -> getr r 6 = Z_to_bv 64 17 -> getr r 7 = Z_to_bv 64 512 ->
      exists r', msteps segs (mkst r (at_ rb 0x514e0) (ICM 10) rom) (mkst r' (at_ rb 0x514e0) (ICM 15) rom)
        /\ (getr r' 11 = at_ cache 1288 /\ getr r' 13 = Z_to_bv 64 512 /\ getr r' 15 = Z_to_bv 64 0 /\ getr r' 16 = Z_to_bv 64 15 /\ getr r' 17 = Z_to_bv 64 1024 /\ getr r' 5 = Z_to_bv 64 16 /\ getr r' 6 = Z_to_bv 64 17 /\ getr r' 7 = Z_to_bv 64 512)
        /\ (forall x : reg, ~ In x [11; 13; 15; 16; 17; 5; 6; 7; 28; 29; 30] -> getr r' x = getr r x).
  Proof using HTW Gpc G1 c pc RB HRF.
    intros r Q11 Q13 Q15 Q16 Q17 Q5 Q6 Q7.
    destruct G1 as [G1a G1b]. destruct Gpc as (Gp1 & Gp2 & Gp3). pose proof (u64_range sp) as Hspr. pose proof (u64_range cache). pose proof (u64_range pc).
    wd_eexists. split; [|split].
    -
      (* [comment removed for export] *)
      ab_ft R514e0 D_514e0 ltac:(condz). an R514e4 D_514e4. an R514e8 D_514e8. ab_tk R514ec D_514ec ltac:(condz).
      an R5150c D_5150c. an R51510 D_51510. ab_tk R51514 D_51514 ltac:(condz).
      an R514bc D_514bc. an R514c0 D_514c0. an R514c4 D_514c4. an R514c8 D_514c8. an R514cc D_514cc.
      fsw4 R514d0 D_514d0 (at_ cache 884). fsd8c R514d4 D_514d4 (at_ cache 888).
      change (wbytes (wbytes (ICM 10) _ _) _ _) with (ICM 11).
      an R514d8 D_514d8.
      ab_ft R514dc D_514dc ltac:(condz).
      (* [comment removed for export] *)
      ab_ft R514e0 D_514e0 ltac:(condz). an R514e4 D_514e4. an R514e8 D_514e8. ab_tk R514ec D_514ec ltac:(condz).
      an R5150c D_5150c. an R51510 D_51510. ab_tk R51514 D_51514 ltac:(condz).
      an R514bc D_514bc. an R514c0 D_514c0. an R514c4 D_514c4. an R514c8 D_514c8. an R514cc D_514cc.
      fsw4 R514d0 D_514d0 (at_ cache 964). fsd8c R514d4 D_514d4 (at_ cache 968).
      change (wbytes (wbytes (ICM 11) _ _) _ _) with (ICM 12).
      an R514d8 D_514d8.
      ab_ft R514dc D_514dc ltac:(condz).
      (* [comment removed for export] *)
      ab_ft R514e0 D_514e0 ltac:(condz). an R514e4 D_514e4. an R514e8 D_514e8. ab_tk R514ec D_514ec ltac:(condz).
      an R5150c D_5150c. an R51510 D_51510. ab_tk R51514 D_51514 ltac:(condz).
      an R514bc D_514bc. an R514c0 D_514c0. an R514c4 D_514c4. an R514c8 D_514c8. an R514cc D_514cc.
      fsw4 R514d0 D_514d0 (at_ cache 1044). fsd8c R514d4 D_514d4 (at_ cache 1048).
      change (wbytes (wbytes (ICM 12) _ _) _ _) with (ICM 13).
      an R514d8 D_514d8.
      ab_ft R514dc D_514dc ltac:(condz).
      (* [comment removed for export] *)
      ab_ft R514e0 D_514e0 ltac:(condz). an R514e4 D_514e4. an R514e8 D_514e8. ab_tk R514ec D_514ec ltac:(condz).
      an R5150c D_5150c. an R51510 D_51510. ab_tk R51514 D_51514 ltac:(condz).
      an R514bc D_514bc. an R514c0 D_514c0. an R514c4 D_514c4. an R514c8 D_514c8. an R514cc D_514cc.
      fsw4 R514d0 D_514d0 (at_ cache 1124). fsd8c R514d4 D_514d4 (at_ cache 1128).
      change (wbytes (wbytes (ICM 13) _ _) _ _) with (ICM 14).
      an R514d8 D_514d8.
      ab_ft R514dc D_514dc ltac:(condz).
      (* [comment removed for export] *)
      ab_ft R514e0 D_514e0 ltac:(condz). an R514e4 D_514e4. an R514e8 D_514e8. ab_tk R514ec D_514ec ltac:(condz).
      an R5150c D_5150c. an R51510 D_51510. ab_tk R51514 D_51514 ltac:(condz).
      an R514bc D_514bc. an R514c0 D_514c0. an R514c4 D_514c4. an R514c8 D_514c8. an R514cc D_514cc.
      fsw4 R514d0 D_514d0 (at_ cache 1204). fsd8c R514d4 D_514d4 (at_ cache 1208).
      change (wbytes (wbytes (ICM 14) _ _) _ _) with (ICM 15).
      an R514d8 D_514d8.
      ab_ft R514dc D_514dc ltac:(condz).
      wd_refl.
    - repeat split; gres; first [reflexivity | assumption].
    - intros x Hx. gres. icK Hx.
  Qed.

  Lemma ic_16_19 : forall r,
      getr r 11 = at_ cache 1288 -> getr r 13 = Z_to_bv 64 512 -> getr r 15 = Z_to_bv 64 0 -> getr r 16 = Z_to_bv 64 15 -> getr r 17 = Z_to_bv 64 1024 -> getr r 5 = Z_to_bv 64 16 -> getr r 6 = Z_to_bv 64 17 -> getr r 7 = Z_to_bv 64 512 ->
      exists r', msteps segs (mkst r (at_ rb 0x514e0) (ICM 15) rom) (mkst r' (at_ rb 0x514e0) (ICM 19) rom)
        /\ (getr r' 11 = at_ cache 1608 /\ getr r' 13 = Z_to_bv 64 640 /\ getr r' 15 = Z_to_bv 64 4 /\ getr r' 16 = Z_to_bv 64 15 /\ getr r' 17 = Z_to_bv 64 1024 /\ getr r' 5 = Z_to_bv 64 16 /\ getr r' 6 = Z_to_bv 64 17 /\ getr r' 7 = Z_to_bv 64 512)
        /\ (forall x : reg, ~ In x [11; 13; 15; 16; 17; 5; 6; 7; 28; 29; 30] -> getr r' x = getr r x).
  Proof using HTW Gpc G1 c pc RB HRF.
    intros r Q11 Q13 Q15 Q16 Q17 Q5 Q6 Q7.
    destruct G1 as [G1a G1b]. destruct Gpc as (Gp1 & Gp2 & Gp3). pose proof (u64_range sp) as Hspr. pose proof (u64_range cache). pose proof (u64_range pc).
    wd_eexists. split; [|split].
    -
      (* [comment removed for export] *)
      ab_ft R514e0 D_514e0 ltac:(condz). an R514e4 D_514e4. an R514e8 D_514e8. ab_tk R514ec D_514ec ltac:(condz).
      an R5150c D_5150c. an R51510 D_51510. ab_tk R51514 D_51514 ltac:(condz).
      an R514bc D_514bc. an R514c0 D_514c0. an R514c4 D_514c4. an R514c8 D_514c8. an R514cc D_514cc.
      fsw4 R514d0 D_514d0 (at_ cache 1284). fsd8c R514d4 D_514d4 (at_ cache 1288).
      change (wbytes (wbytes (ICM 15) _ _) _ _) with (ICM 16).
      an R514d8 D_514d8.
      ab_ft R514dc D_514dc ltac:(condz).
      (* [comment removed for export] *)
      ab_ft R514e0 D_514e0 ltac:(condz). an R514e4 D_514e4. an R514e8 D_514e8. ab_ft R514ec D_514ec ltac:(condz).
      an R514f0 D_514f0. an R514f4 D_514f4. an R514f8 D_514f8. an R514fc D_514fc. an R51500 D_51500. an R51504 D_51504. an R51508 D_51508.
      an R5150c D_5150c. an R51510 D_51510. ab_tk R51514 D_51514 ltac:(condz).
      an R514bc D_514bc. an R514c0 D_514c0. an R514c4 D_514c4. an R514c8 D_514c8. an R514cc D_514cc.
      fsw4 R514d0 D_514d0 (at_ cache 1364). fsd8c R514d4 D_514d4 (at_ cache 1368).
      change (wbytes (wbytes (ICM 16) _ _) _ _) with (ICM 17).
      an R514d8 D_514d8.
      ab_ft R514dc D_514dc ltac:(condz).
      (* [comment removed for export] *)
      ab_ft R514e0 D_514e0 ltac:(condz). an R514e4 D_514e4. an R514e8 D_514e8. ab_ft R514ec D_514ec ltac:(condz).
      an R514f0 D_514f0. an R514f4 D_514f4. an R514f8 D_514f8. an R514fc D_514fc. an R51500 D_51500. an R51504 D_51504. an R51508 D_51508.
      an R5150c D_5150c. an R51510 D_51510. ab_tk R51514 D_51514 ltac:(condz).
      an R514bc D_514bc. an R514c0 D_514c0. an R514c4 D_514c4. an R514c8 D_514c8. an R514cc D_514cc.
      fsw4 R514d0 D_514d0 (at_ cache 1444). fsd8c R514d4 D_514d4 (at_ cache 1448).
      change (wbytes (wbytes (ICM 17) _ _) _ _) with (ICM 18).
      an R514d8 D_514d8.
      ab_ft R514dc D_514dc ltac:(condz).
      (* [comment removed for export] *)
      ab_ft R514e0 D_514e0 ltac:(condz). an R514e4 D_514e4. an R514e8 D_514e8. ab_ft R514ec D_514ec ltac:(condz).
      an R514f0 D_514f0. an R514f4 D_514f4. an R514f8 D_514f8. an R514fc D_514fc. an R51500 D_51500. an R51504 D_51504. an R51508 D_51508.
      an R5150c D_5150c. an R51510 D_51510. ab_tk R51514 D_51514 ltac:(condz).
      an R514bc D_514bc. an R514c0 D_514c0. an R514c4 D_514c4. an R514c8 D_514c8. an R514cc D_514cc.
      fsw4 R514d0 D_514d0 (at_ cache 1524). fsd8c R514d4 D_514d4 (at_ cache 1528).
      change (wbytes (wbytes (ICM 18) _ _) _ _) with (ICM 19).
      an R514d8 D_514d8.
      ab_ft R514dc D_514dc ltac:(condz).
      wd_refl.
    - repeat split; gres; first [reflexivity | assumption].
    - intros x Hx. gres. icK Hx.
  Qed.

End RFI.
End FPGen1.
