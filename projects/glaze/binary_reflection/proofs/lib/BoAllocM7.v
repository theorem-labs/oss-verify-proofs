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
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_50a9c_51a9c. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_50a9c_51a9c.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma v_srliw1_small : forall z, (0 <= z < 2 ^ 31)%Z -> v_srliw (Z_to_bv 64 z) 1 = Z_to_bv 64 (z / 2).
Proof.
  intros z Hz. (lazymatch goal with |- ?G => let G' := eval unfold v_srliw in G in change_no_check G' end). f_equal. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1)%Z with 2%Z.
  rewrite u_Z2bv by lia. (lazymatch goal with |- ?G => let G' := eval unfold bv_swrap, bv_wrap in G in change_no_check G' end).
  change (bv_modulus 32) with 4294967296%Z. change (bv_half_modulus 32) with 2147483648%Z.
  rewrite (Z.mod_small z) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition ic_tab : list (Z * Z) :=
  [(16, 32); (16, 64); (16, 96); (16, 128); (12, 160); (10, 192); (8, 224); (8, 256); (6, 288); (6, 320); (4, 352); (4, 384); (4, 416); (4, 448); (4, 480); (4, 512); (2, 768); (2, 1024); (2, 1536); (2, 2048); (2, 3072); (2, 4096); (2, 6144); (2, 8192); (2, 12288); (2, 16384); (2, 24576); (2, 32768); (2, 49152); (2, 65536); (16, 64)]%Z.
Definition icmc (i : Z) : Z := fst (nth (Z.to_nat (i - 1)) ic_tab (0, 0))%Z.
Definition iccs (i : Z) : Z := snd (nth (Z.to_nat (i - 1)) ic_tab (0, 0))%Z.
Lemma ic_tab_range : forall k : nat, (k < 31)%nat -> (2 <= fst (nth k ic_tab (0, 0)) <= 16)%Z /\ (fst (nth k ic_tab (0, 0)) mod 2 = 0)%Z.
Proof. intros k Hk. do 31 (destruct k as [|k]; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); split; [lia | reflexivity] |]). lia. Qed.
Lemma icmc_range : forall c, (1 <= c <= 31)%Z -> (2 <= icmc c <= 16)%Z /\ (icmc c mod 2 = 0)%Z.
Proof. intros c0 Hc. (lazymatch goal with |- ?G => let G' := eval unfold icmc in G in change_no_check G' end). apply ic_tab_range. lia. Qed.


Section FPGen1.
Context {fx : FPState}.

Definition rf_words : list (option (bv 32)) :=
  [Some W_5143c; Some W_51440; Some W_51444; Some W_51448; Some W_5144c; Some W_51450; Some W_51454; Some W_51458;
   Some W_5145c; Some W_51460; Some W_51464; Some W_51468; Some W_5146c; Some W_51470; Some W_51474; Some W_51478;
   Some W_5147c; Some W_51480; Some W_51484; Some W_51488; Some W_5148c; Some W_51490; Some W_51494; Some W_51498;
   Some W_5149c; Some W_514a0; Some W_514a4; Some W_514a8; Some W_514ac; Some W_514b0; Some W_514b4; Some W_514b8;
   Some W_514bc; Some W_514c0; Some W_514c4; Some W_514c8; Some W_514cc; Some W_514d0; Some W_514d4; Some W_514d8;
   Some W_514dc; Some W_514e0; Some W_514e4; Some W_514e8; Some W_514ec; Some W_514f0; Some W_514f4; Some W_514f8;
   Some W_514fc; Some W_51500; Some W_51504; Some W_51508; Some W_5150c; Some W_51510; Some W_51514; Some W_51518;
   Some W_5151c; Some W_51520; Some W_51524; Some W_51528; Some W_5152c; Some W_51530; Some W_51534; Some W_51538]%list.

Section RF.
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
  Lemma R51478 : fetch_word segs (at_ rb 0x51478) = Some W_51478.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 15 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R5147c : fetch_word segs (at_ rb 0x5147c) = Some W_5147c.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 16 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R51480 : fetch_word segs (at_ rb 0x51480) = Some W_51480.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 17 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R51484 : fetch_word segs (at_ rb 0x51484) = Some W_51484.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 18 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R51488 : fetch_word segs (at_ rb 0x51488) = Some W_51488.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 19 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R5148c : fetch_word segs (at_ rb 0x5148c) = Some W_5148c.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 20 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R51490 : fetch_word segs (at_ rb 0x51490) = Some W_51490.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 21 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R51494 : fetch_word segs (at_ rb 0x51494) = Some W_51494.  Proof using HRF. exact (code_ato_get segs rb 0x5143c rf_words 22 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
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
  Variables (ra sp cache pc alloc : word) (c mc : Z).
  Hypothesis Hret : ret_ok ra.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H10 : getr regs 10 = cache.
  Hypothesis H11 : getr regs 11 = pc.
  Hypothesis H12 : getr regs 12 = alloc.
  Hypothesis H13 : getr regs 13 = Z_to_bv 64 c.
  Hypothesis Hmc : (2 <= mc <= 16)%Z /\ (mc mod 2 = 0)%Z.
  Hypothesis Hstk : store_ok segs mem (at_ sp (-32)) 32 = true.
  Hypothesis G1 : (2 ^ 32 + 32 <= U sp)%Z /\ (U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Gpc : (U cache + 2640 <= U sp - 32)%Z /\ (U pc = U cache + 80 * c)%Z /\ (1 <= c <= 30)%Z.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis Rmc : rdn segs mem (at_ pc 4) 4 = Some (LE4 mc).

  (* [comment removed for export] *)
  Definition rf_m1 : word -> option byte :=
    wbytes (wbytes (wbytes mem (at_ sp (-8)) (LE8 ra)) (at_ sp (-16)) (LE8 (getr regs 8))) (at_ sp (-24)) (LE8 (getr regs 9)).
  Lemma rf_m1_outside : forall x : word, (U x < U sp - 32 \/ U sp <= U x)%Z -> rf_m1 x = mem x.
  Proof using G1 rb.
    clear Hmc Rmc.
    intros x Hx. pose proof (u64_range sp). destruct G1 as [G1a G1b]. (lazymatch goal with |- ?G => let G' := eval unfold rf_m1 in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); try lia. reflexivity.
  Qed.
  Lemma rf_m1_grows : mem_grows mem rf_m1.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold rf_m1 in G in change_no_check G' end). do 3 (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.

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
  Lemma rf_pro :
    exists r,
      msteps segs (mkst regs (at_ rb 0x5143c) mem rom) (mkst r (at_ rb 0x5153c) rf_m1 rom)
      /\ getr r 1 = at_ rb 0x5147c /\ getr r 2 = at_ sp (-32) /\ getr r 8 = pc /\ getr r 9 = Z_to_bv 64 (mc / 2)
      /\ getr r 10 = alloc /\ getr r 11 = at_ cache 2560 /\ getr r 12 = Z_to_bv 64 c /\ getr r 13 = at_ pc 16 /\ getr r 14 = Z_to_bv 64 (mc / 2)
      /\ regs_agree (fun i : reg => In i [1; 2; 8; 9; 10; 11; 12; 13; 14]) regs r.
  Proof using Rmc Gpc G1 Hstk Hmc H13 H12 H11 H10 H2 H1 HRF.
    destruct G1 as [G1a G1b]. destruct Hmc as [Hmc1 Hmc2]. destruct Gpc as (Gp1 & Gp2 & Gp3). pose proof (u64_range sp) as Hspr. pose proof (u64_range cache). pose proof (u64_range pc).
    wd_eexists. split.
    - an R5143c D_5143c.                                   (* [comment removed for export] *)
      fsd8 R51440 D_51440 (at_ sp (-8)).                   (* [comment removed for export] *)
      fsd8 R51444 D_51444 (at_ sp (-16)).                  (* [comment removed for export] *)
      fsd8 R51448 D_51448 (at_ sp (-24)).                  (* [comment removed for export] *)
      change (wbytes _ _ _) with rf_m1.
      an R5144c D_5144c.                                   (* [comment removed for export] *)
      an R51450 D_51450.                                   (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lw with (bs := LE4 mc) (v := Z_to_bv 64 mc);
          [exact R51454 | reflexivity | exact D_51454
          | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at;
            rewrite <- Rmc; apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply rf_m1_outside; rewrite at_u in Hx by lia; cbn in Hx; lia]
          | apply bytes4_small; lia]
        | step_simpl]; rewrite (v_lw_small mc) by lia; vn.   (* [comment removed for export] *)
      ab_ft R51458 D_51458 ltac:(condz).                  (* [comment removed for export] *)
      an R5145c D_5145c. rewrite (v_srliw1_small mc) by lia.   (* [comment removed for export] *)
      an R51460 D_51460.                                   (* [comment removed for export] *)
      av R51464 D_51464 (at_ cache 2560) ltac:(rewrite ?at_at; vz).   (* [comment removed for export] *)
      av R51468 D_51468 (at_ pc 16) ltac:(vz).            (* [comment removed for export] *)
      an R5146c D_5146c.                                   (* [comment removed for export] *)
      an R51470 D_51470.                                   (* [comment removed for export] *)
      an R51474 D_51474.                                   (* [comment removed for export] *)
      an R51478 D_51478.                                   (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.

  Lemma rf_m1_slots : forall (k : Z) (v : word),
    In (k, v) [(-8, ra); (-16, getr regs 8); (-24, getr regs 9)]%Z -> rdn segs rf_m1 (at_ sp k) 8 = Some (LE8 v).
  Proof using G1 rb.
    clear Hmc Rmc. intros k v Hin. pose proof (u64_range sp). destruct G1 as [G1a G1b]. (lazymatch goal with |- ?G => let G' := eval unfold rf_m1 in G in change_no_check G' end). cbn [In] in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; rd8_chain|]). destruct Hin.
  Qed.


  (* [comment removed for export] *)
  Hypothesis HTW : store_ok segs mem (at_ cache 80) 2480 = true.      (* [comment removed for export] *)
  Fixpoint ic_mem (k : nat) : word -> option byte :=
    match k with
    | O => rf_m1
    | S k' => wbytes (wbytes (ic_mem k') (at_ cache (80 * Z.of_nat (S k') + 4)) (LE4 (icmc (Z.of_nat (S k')))))
                     (at_ cache (80 * Z.of_nat (S k') + 8)) (LE8 (Z_to_bv 64 (iccs (Z.of_nat (S k')))))
    end.
  Lemma ic_mem_grows : forall k, mem_grows mem (ic_mem k).
  Proof using.
    induction k as [|k IH]; [apply rf_m1_grows|]. (lazymatch goal with |- ?G => let G' := eval cbn [ic_mem] in G in change_no_check G' end).
    eapply mem_grows_trans; [exact IH|]. eapply mem_grows_trans; apply wbytes_grows.
  Qed.

  (* [comment removed for export] *)
  Ltac grows_ic := lazymatch goal with
    | |- mem_grows ?m ?m => apply mem_grows_refl
    | |- mem_grows _ (wbytes _ _ _) => eapply mem_grows_trans; [|apply wbytes_grows]; grows_ic
    | |- mem_grows _ (ic_mem _) => apply ic_mem_grows
    | |- mem_grows _ rf_m1 => apply rf_m1_grows
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

  (* [comment removed for export] *)
  Lemma ic_mem_mc : forall k c, (1 <= c <= Z.of_nat k)%Z -> (Z.of_nat k <= 31)%Z ->
    rdn segs (ic_mem k) (at_ cache (80 * c + 4)) 4 = Some (LE4 (icmc c)).
  Proof using Gpc G1 c pc rb.
    clear Hmc Rmc.
    induction k as [|k IH]; intros c0 Hc Hk; [lia|]. (lazymatch goal with |- ?G => let G' := eval cbn [ic_mem] in G in change_no_check G' end). pose proof (u64_range cache). destruct Gpc as (Gp1 & Gp2 & Gp3). pose proof (u64_range sp).
    rewrite rdn_wbytes_out; [ | rewrite length_N_to_le_bytes, !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ].
    destruct (Z.eq_dec c0 (Z.of_nat (S k))) as [->|NE].
    - pose proof (rdn_wbytes_hit segs (LE4 (icmc (Z.of_nat (S k)))) (ic_mem k) (at_ cache (80 * Z.of_nat (S k) + 4))) as Hh.
      rewrite length_N_to_le_bytes in Hh. apply Hh. rewrite at_u by lia. lia.
    - rewrite rdn_wbytes_out; [ | rewrite length_N_to_le_bytes, !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ].
      apply IH; lia.
  Qed.


  (* [comment removed for export] *)
  Lemma rf_epi : forall (M : word -> option byte) r0 (res : word),
    getr r0 1 = at_ rb 0x5147c -> getr r0 2 = at_ sp (-32) -> getr r0 8 = pc -> getr r0 9 = Z_to_bv 64 (mc / 2) -> getr r0 10 = res ->
    U res <> 0%Z ->
    store_ok segs M (at_ pc 0) 4 = true ->
    (forall (k : Z) (v : word), In (k, v) [(-8, ra); (-16, getr regs 8); (-24, getr regs 9)]%Z -> rdn segs M (at_ sp k) 8 = Some (LE8 v)) ->
    (U pc + 4 <= U sp - 32 \/ U sp <= U pc)%Z ->
    exists r,
      msteps segs (mkst r0 (at_ rb 0x5147c) M rom) (mkst r ra (wbytes M pc (LE4 (mc / 2))) rom)
      /\ getr r 10 = res /\ getr r 2 = sp /\ getr r 8 = getr regs 8 /\ getr r 9 = getr regs 9 /\ getr r 1 = ra
      /\ (forall i : reg, ~ In i [1; 2; 8; 9] -> getr r i = getr r0 i).
  Proof using Gpc G1 Hmc Hret c cache RB HRF.
    clear Rmc.
    intros M r0 res R1 R2 R8 R9 R10 NZ SOK FR Dpc.
    destruct G1 as [G1a G1b]. destruct Hmc as [Hmc1 Hmc2]. destruct Gpc as (Gp1 & Gp2 & Gp3). pose proof (u64_range sp) as Hspr. pose proof (u64_range pc). pose proof (u64_range res).
    set (M' := wbytes M pc (LE4 (mc / 2))).
    assert (FR' : forall (k : Z) (v : word), In (k, v) [(-8, ra); (-16, getr regs 8); (-24, getr regs 9)]%Z -> rdn segs M' (at_ sp k) 8 = Some (LE8 v)).
    { intros k v Hin. assert (Hk : (-24 <= k <= -8)%Z) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      rewrite <- (FR k v Hin). (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|].
      intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. rewrite wbytes_outside; [reflexivity | rewrite length_N_to_le_bytes; lia | rewrite length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    wd_eexists. split.
    - ab_ft R5147c D_5147c ltac:(condz).                  (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_sw_at with (a := pc);
          [exact R51480 | reflexivity | exact D_51480
          | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi, ?at_add_0_r; reflexivity
          | gres; rwH; reflexivity
          | rewrite <- (at_0 pc); exact SOK ]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      change (wbytes M _ _) with M'.
      Ltac cldF F D vv H := chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 vv) (v := vv);
          [exact F | reflexivity | exact D | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi, ?at_at; zlit_at; apply H; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto | apply bytes_le_to_Z_8]
        | step_simpl]; vn.
      cldF R51484 D_51484 ra (FR' (-8)%Z).                 (* [comment removed for export] *)
      cldF R51488 D_51488 (getr regs 8) (FR' (-16)%Z).     (* [comment removed for export] *)
      cldF R5148c D_5148c (getr regs 9) (FR' (-24)%Z).     (* [comment removed for export] *)
      an R51490 D_51490.                                   (* [comment removed for export] *)
      aret R51494 D_51494 ra.                              (* [comment removed for export] *)
      wd_refl.
    - split; [gres; rwH; reflexivity|].
      split; [gres; rwH; first [reflexivity | rewrite ?at_at; apply bv_eq; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ]] |].
      split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
      intros i Hni. gres. rewrite !getr_other; [reflexivity| | | |]; intros E; apply Hni; rewrite <- E; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto.
  Qed.
End RF.
End FPGen1.
