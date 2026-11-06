(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.As_code_50024_51024.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocM7.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.As_code_50024_51024.
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
  [Some W_509c4; Some W_509c8; Some W_509cc; Some W_509d0; Some W_509d4; Some W_509d8; Some W_509dc; Some W_509e0;
   Some W_509e4; Some W_509e8; Some W_509ec; Some W_509f0; Some W_509f4; Some W_509f8; Some W_509fc; Some W_50a00;
   Some W_50a04; Some W_50a08; Some W_50a0c; Some W_50a10; Some W_50a14; Some W_50a18; Some W_50a1c; Some W_50a20;
   Some W_50a24; Some W_50a28; Some W_50a2c; Some W_50a30; Some W_50a34; Some W_50a38; Some W_50a3c; Some W_50a40;
   Some W_50a44; Some W_50a48; Some W_50a4c; Some W_50a50; Some W_50a54; Some W_50a58; Some W_50a5c; Some W_50a60;
   Some W_50a64; Some W_50a68; Some W_50a6c; Some W_50a70; Some W_50a74; Some W_50a78; Some W_50a7c; Some W_50a80;
   Some W_50a84; Some W_50a88; Some W_50a8c; Some W_50a90; Some W_50a94; Some W_50a98; Some W_50a9c; Some W_50aa0;
   Some W_50aa4; Some W_50aa8; Some W_50aac; Some W_50ab0; Some W_50ab4; Some W_50ab8; Some W_50abc; Some W_50ac0]%list.

Section RF.
  Variable segs : list Segment.
  Variable rb : word.
  Hypothesis HRF : code_ato segs rb 0x509cc rf_words.
  Hypothesis RB : (U rb mod 2 = 0)%Z /\ (U rb + 2 ^ 24 < 2 ^ 64)%Z.

  Lemma R509c4 : fetch_word segs (at_ rb 0x509cc) = Some W_509c4.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 0 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R509c8 : fetch_word segs (at_ rb 0x509d0) = Some W_509c8.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 1 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R509cc : fetch_word segs (at_ rb 0x509d4) = Some W_509cc.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 2 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R509d0 : fetch_word segs (at_ rb 0x509d8) = Some W_509d0.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 3 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R509d4 : fetch_word segs (at_ rb 0x509dc) = Some W_509d4.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 4 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R509d8 : fetch_word segs (at_ rb 0x509e0) = Some W_509d8.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 5 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R509dc : fetch_word segs (at_ rb 0x509e4) = Some W_509dc.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 6 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R509e0 : fetch_word segs (at_ rb 0x509e8) = Some W_509e0.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 7 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R509e4 : fetch_word segs (at_ rb 0x509ec) = Some W_509e4.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 8 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R509e8 : fetch_word segs (at_ rb 0x509f0) = Some W_509e8.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 9 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R509ec : fetch_word segs (at_ rb 0x509f4) = Some W_509ec.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 10 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R509f0 : fetch_word segs (at_ rb 0x509f8) = Some W_509f0.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 11 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R509f4 : fetch_word segs (at_ rb 0x509fc) = Some W_509f4.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 12 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R509f8 : fetch_word segs (at_ rb 0x50a00) = Some W_509f8.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 13 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R509fc : fetch_word segs (at_ rb 0x50a04) = Some W_509fc.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 14 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a00 : fetch_word segs (at_ rb 0x50a08) = Some W_50a00.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 15 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a04 : fetch_word segs (at_ rb 0x50a0c) = Some W_50a04.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 16 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a08 : fetch_word segs (at_ rb 0x50a10) = Some W_50a08.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 17 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a0c : fetch_word segs (at_ rb 0x50a14) = Some W_50a0c.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 18 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a10 : fetch_word segs (at_ rb 0x50a18) = Some W_50a10.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 19 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a14 : fetch_word segs (at_ rb 0x50a1c) = Some W_50a14.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 20 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a18 : fetch_word segs (at_ rb 0x50a20) = Some W_50a18.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 21 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a1c : fetch_word segs (at_ rb 0x50a24) = Some W_50a1c.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 22 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a20 : fetch_word segs (at_ rb 0x50a28) = Some W_50a20.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 23 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a24 : fetch_word segs (at_ rb 0x50a2c) = Some W_50a24.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 24 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a28 : fetch_word segs (at_ rb 0x50a30) = Some W_50a28.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 25 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a2c : fetch_word segs (at_ rb 0x50a34) = Some W_50a2c.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 26 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a30 : fetch_word segs (at_ rb 0x50a38) = Some W_50a30.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 27 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a34 : fetch_word segs (at_ rb 0x50a3c) = Some W_50a34.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 28 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a38 : fetch_word segs (at_ rb 0x50a40) = Some W_50a38.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 29 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a3c : fetch_word segs (at_ rb 0x50a44) = Some W_50a3c.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 30 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a40 : fetch_word segs (at_ rb 0x50a48) = Some W_50a40.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 31 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a44 : fetch_word segs (at_ rb 0x50a4c) = Some W_50a44.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 32 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a48 : fetch_word segs (at_ rb 0x50a50) = Some W_50a48.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 33 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a4c : fetch_word segs (at_ rb 0x50a54) = Some W_50a4c.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 34 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a50 : fetch_word segs (at_ rb 0x50a58) = Some W_50a50.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 35 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a54 : fetch_word segs (at_ rb 0x50a5c) = Some W_50a54.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 36 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a58 : fetch_word segs (at_ rb 0x50a60) = Some W_50a58.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 37 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a5c : fetch_word segs (at_ rb 0x50a64) = Some W_50a5c.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 38 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a60 : fetch_word segs (at_ rb 0x50a68) = Some W_50a60.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 39 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a64 : fetch_word segs (at_ rb 0x50a6c) = Some W_50a64.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 40 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a68 : fetch_word segs (at_ rb 0x50a70) = Some W_50a68.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 41 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a6c : fetch_word segs (at_ rb 0x50a74) = Some W_50a6c.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 42 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a70 : fetch_word segs (at_ rb 0x50a78) = Some W_50a70.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 43 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a74 : fetch_word segs (at_ rb 0x50a7c) = Some W_50a74.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 44 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a78 : fetch_word segs (at_ rb 0x50a80) = Some W_50a78.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 45 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a7c : fetch_word segs (at_ rb 0x50a84) = Some W_50a7c.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 46 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a80 : fetch_word segs (at_ rb 0x50a88) = Some W_50a80.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 47 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a84 : fetch_word segs (at_ rb 0x50a8c) = Some W_50a84.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 48 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a88 : fetch_word segs (at_ rb 0x50a90) = Some W_50a88.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 49 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a8c : fetch_word segs (at_ rb 0x50a94) = Some W_50a8c.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 50 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a90 : fetch_word segs (at_ rb 0x50a98) = Some W_50a90.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 51 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a94 : fetch_word segs (at_ rb 0x50a9c) = Some W_50a94.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 52 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a98 : fetch_word segs (at_ rb 0x50aa0) = Some W_50a98.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 53 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a9c : fetch_word segs (at_ rb 0x50aa4) = Some W_50a9c.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 54 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50aa0 : fetch_word segs (at_ rb 0x50aa8) = Some W_50aa0.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 55 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50aa4 : fetch_word segs (at_ rb 0x50aac) = Some W_50aa4.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 56 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50aa8 : fetch_word segs (at_ rb 0x50ab0) = Some W_50aa8.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 57 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50aac : fetch_word segs (at_ rb 0x50ab4) = Some W_50aac.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 58 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50ab0 : fetch_word segs (at_ rb 0x50ab8) = Some W_50ab0.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 59 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50ab4 : fetch_word segs (at_ rb 0x50abc) = Some W_50ab4.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 60 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50ab8 : fetch_word segs (at_ rb 0x50ac0) = Some W_50ab8.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 61 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50abc : fetch_word segs (at_ rb 0x50ac4) = Some W_50abc.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 62 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50ac0 : fetch_word segs (at_ rb 0x50ac8) = Some W_50ac0.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 63 _ HRF eq_refl). Qed.   (* [comment removed for export] *)

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
      msteps segs (mkst regs (at_ rb 0x509cc) mem rom) (mkst r (at_ rb 0x50acc) rf_m1 rom)
      /\ getr r 1 = at_ rb 0x50a0c /\ getr r 2 = at_ sp (-32) /\ getr r 8 = pc /\ getr r 9 = Z_to_bv 64 (mc / 2)
      /\ getr r 10 = alloc /\ getr r 11 = at_ cache 2560 /\ getr r 12 = Z_to_bv 64 c /\ getr r 13 = at_ pc 16 /\ getr r 14 = Z_to_bv 64 (mc / 2)
      /\ regs_agree (fun i : reg => In i [1; 2; 8; 9; 10; 11; 12; 13; 14]) regs r.
  Proof using Rmc Gpc G1 Hstk Hmc H13 H12 H11 H10 H2 H1 HRF.
    destruct G1 as [G1a G1b]. destruct Hmc as [Hmc1 Hmc2]. destruct Gpc as (Gp1 & Gp2 & Gp3). pose proof (u64_range sp) as Hspr. pose proof (u64_range cache). pose proof (u64_range pc).
    wd_eexists. split.
    - an R509c4 D_509c4.                                   (* [comment removed for export] *)
      fsd8 R509c8 D_509c8 (at_ sp (-8)).                   (* [comment removed for export] *)
      fsd8 R509cc D_509cc (at_ sp (-16)).                  (* [comment removed for export] *)
      fsd8 R509d0 D_509d0 (at_ sp (-24)).                  (* [comment removed for export] *)
      change (wbytes _ _ _) with rf_m1.
      an R509d4 D_509d4.                                   (* [comment removed for export] *)
      an R509d8 D_509d8.                                   (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lw with (bs := LE4 mc) (v := Z_to_bv 64 mc);
          [exact R509dc | reflexivity | exact D_509dc
          | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at;
            rewrite <- Rmc; apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply rf_m1_outside; rewrite at_u in Hx by lia; cbn in Hx; lia]
          | apply bytes4_small; lia]
        | step_simpl]; rewrite (v_lw_small mc) by lia; vn.   (* [comment removed for export] *)
      ab_ft R509e0 D_509e0 ltac:(condz).                  (* [comment removed for export] *)
      an R509e4 D_509e4. rewrite (v_srliw1_small mc) by lia.   (* [comment removed for export] *)
      an R509e8 D_509e8.                                   (* [comment removed for export] *)
      av R509ec D_509ec (at_ cache 2560) ltac:(rewrite ?at_at; vz).   (* [comment removed for export] *)
      av R509f0 D_509f0 (at_ pc 16) ltac:(vz).            (* [comment removed for export] *)
      an R509f4 D_509f4.                                   (* [comment removed for export] *)
      an R509f8 D_509f8.                                   (* [comment removed for export] *)
      an R509fc D_509fc.                                   (* [comment removed for export] *)
      an R50a00 D_50a00.                                   (* [comment removed for export] *)
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
    getr r0 1 = at_ rb 0x50a0c -> getr r0 2 = at_ sp (-32) -> getr r0 8 = pc -> getr r0 9 = Z_to_bv 64 (mc / 2) -> getr r0 10 = res ->
    U res <> 0%Z ->
    store_ok segs M (at_ pc 0) 4 = true ->
    (forall (k : Z) (v : word), In (k, v) [(-8, ra); (-16, getr regs 8); (-24, getr regs 9)]%Z -> rdn segs M (at_ sp k) 8 = Some (LE8 v)) ->
    (U pc + 4 <= U sp - 32 \/ U sp <= U pc)%Z ->
    exists r,
      msteps segs (mkst r0 (at_ rb 0x50a0c) M rom) (mkst r ra (wbytes M pc (LE4 (mc / 2))) rom)
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
    - ab_ft R50a04 D_50a04 ltac:(condz).                  (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_sw_at with (a := pc);
          [exact R50a08 | reflexivity | exact D_50a08
          | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi, ?at_add_0_r; reflexivity
          | gres; rwH; reflexivity
          | rewrite <- (at_0 pc); exact SOK ]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      change (wbytes M _ _) with M'.
      Ltac cldF F D vv H := chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 vv) (v := vv);
          [exact F | reflexivity | exact D | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi, ?at_at; zlit_at; apply H; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto | apply bytes_le_to_Z_8]
        | step_simpl]; vn.
      cldF R50a0c D_50a0c ra (FR' (-8)%Z).                 (* [comment removed for export] *)
      cldF R50a10 D_50a10 (getr regs 8) (FR' (-16)%Z).     (* [comment removed for export] *)
      cldF R50a14 D_50a14 (getr regs 9) (FR' (-24)%Z).     (* [comment removed for export] *)
      an R50a18 D_50a18.                                   (* [comment removed for export] *)
      aret R50a1c D_50a1c ra.                              (* [comment removed for export] *)
      wd_refl.
    - split; [gres; rwH; reflexivity|].
      split; [gres; rwH; first [reflexivity | rewrite ?at_at; apply bv_eq; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ]] |].
      split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
      intros i Hni. gres. rewrite !getr_other; [reflexivity| | | |]; intros E; apply Hni; rewrite <- E; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto.
  Qed.
End RF.
End FPGen1.
End AsAllocM7.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.As_code_50024_51024. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.As_code_50024_51024 AsAllocM7.
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
  Hypothesis HRF : code_ato segs rb 0x509cc rf_words.
  Hypothesis RB : (U rb mod 2 = 0)%Z /\ (U rb + 2 ^ 24 < 2 ^ 64)%Z.

  Lemma R509c4 : fetch_word segs (at_ rb 0x509cc) = Some W_509c4.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 0 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R509c8 : fetch_word segs (at_ rb 0x509d0) = Some W_509c8.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 1 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R509cc : fetch_word segs (at_ rb 0x509d4) = Some W_509cc.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 2 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R509d0 : fetch_word segs (at_ rb 0x509d8) = Some W_509d0.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 3 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R509d4 : fetch_word segs (at_ rb 0x509dc) = Some W_509d4.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 4 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R509d8 : fetch_word segs (at_ rb 0x509e0) = Some W_509d8.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 5 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R509dc : fetch_word segs (at_ rb 0x509e4) = Some W_509dc.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 6 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R509e0 : fetch_word segs (at_ rb 0x509e8) = Some W_509e0.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 7 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R509e4 : fetch_word segs (at_ rb 0x509ec) = Some W_509e4.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 8 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R509e8 : fetch_word segs (at_ rb 0x509f0) = Some W_509e8.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 9 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R509ec : fetch_word segs (at_ rb 0x509f4) = Some W_509ec.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 10 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R509f0 : fetch_word segs (at_ rb 0x509f8) = Some W_509f0.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 11 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R509f4 : fetch_word segs (at_ rb 0x509fc) = Some W_509f4.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 12 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R509f8 : fetch_word segs (at_ rb 0x50a00) = Some W_509f8.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 13 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R509fc : fetch_word segs (at_ rb 0x50a04) = Some W_509fc.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 14 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a00 : fetch_word segs (at_ rb 0x50a08) = Some W_50a00.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 15 _ HRF eq_refl). Qed.






   (* [comment removed for export] *)
  Lemma R50a20 : fetch_word segs (at_ rb 0x50a28) = Some W_50a20.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 23 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a24 : fetch_word segs (at_ rb 0x50a2c) = Some W_50a24.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 24 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a28 : fetch_word segs (at_ rb 0x50a30) = Some W_50a28.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 25 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a2c : fetch_word segs (at_ rb 0x50a34) = Some W_50a2c.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 26 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a30 : fetch_word segs (at_ rb 0x50a38) = Some W_50a30.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 27 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a34 : fetch_word segs (at_ rb 0x50a3c) = Some W_50a34.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 28 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a38 : fetch_word segs (at_ rb 0x50a40) = Some W_50a38.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 29 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a3c : fetch_word segs (at_ rb 0x50a44) = Some W_50a3c.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 30 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a40 : fetch_word segs (at_ rb 0x50a48) = Some W_50a40.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 31 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a44 : fetch_word segs (at_ rb 0x50a4c) = Some W_50a44.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 32 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a48 : fetch_word segs (at_ rb 0x50a50) = Some W_50a48.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 33 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a4c : fetch_word segs (at_ rb 0x50a54) = Some W_50a4c.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 34 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a50 : fetch_word segs (at_ rb 0x50a58) = Some W_50a50.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 35 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a54 : fetch_word segs (at_ rb 0x50a5c) = Some W_50a54.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 36 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a58 : fetch_word segs (at_ rb 0x50a60) = Some W_50a58.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 37 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a5c : fetch_word segs (at_ rb 0x50a64) = Some W_50a5c.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 38 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a60 : fetch_word segs (at_ rb 0x50a68) = Some W_50a60.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 39 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a64 : fetch_word segs (at_ rb 0x50a6c) = Some W_50a64.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 40 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a68 : fetch_word segs (at_ rb 0x50a70) = Some W_50a68.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 41 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a6c : fetch_word segs (at_ rb 0x50a74) = Some W_50a6c.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 42 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a70 : fetch_word segs (at_ rb 0x50a78) = Some W_50a70.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 43 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a74 : fetch_word segs (at_ rb 0x50a7c) = Some W_50a74.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 44 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a78 : fetch_word segs (at_ rb 0x50a80) = Some W_50a78.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 45 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a7c : fetch_word segs (at_ rb 0x50a84) = Some W_50a7c.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 46 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a80 : fetch_word segs (at_ rb 0x50a88) = Some W_50a80.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 47 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a84 : fetch_word segs (at_ rb 0x50a8c) = Some W_50a84.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 48 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a88 : fetch_word segs (at_ rb 0x50a90) = Some W_50a88.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 49 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a8c : fetch_word segs (at_ rb 0x50a94) = Some W_50a8c.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 50 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a90 : fetch_word segs (at_ rb 0x50a98) = Some W_50a90.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 51 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a94 : fetch_word segs (at_ rb 0x50a9c) = Some W_50a94.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 52 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a98 : fetch_word segs (at_ rb 0x50aa0) = Some W_50a98.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 53 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a9c : fetch_word segs (at_ rb 0x50aa4) = Some W_50a9c.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 54 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50aa0 : fetch_word segs (at_ rb 0x50aa8) = Some W_50aa0.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 55 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50aa4 : fetch_word segs (at_ rb 0x50aac) = Some W_50aa4.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 56 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50aa8 : fetch_word segs (at_ rb 0x50ab0) = Some W_50aa8.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 57 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50aac : fetch_word segs (at_ rb 0x50ab4) = Some W_50aac.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 58 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50ab0 : fetch_word segs (at_ rb 0x50ab8) = Some W_50ab0.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 59 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50ab4 : fetch_word segs (at_ rb 0x50abc) = Some W_50ab4.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 60 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50ab8 : fetch_word segs (at_ rb 0x50ac0) = Some W_50ab8.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 61 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50abc : fetch_word segs (at_ rb 0x50ac4) = Some W_50abc.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 62 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50ac0 : fetch_word segs (at_ rb 0x50ac8) = Some W_50ac0.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 63 _ HRF eq_refl). Qed.   (* [comment removed for export] *)

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
      exists r', msteps segs (mkst r (at_ rb 0x50a70) (ICM 0) rom) (mkst r' (at_ rb 0x50a70) (ICM 5) rom)
        /\ (getr r' 11 = at_ cache 488 /\ getr r' 13 = Z_to_bv 64 192 /\ getr r' 15 = Z_to_bv 64 18446744073709551606 /\ getr r' 16 = Z_to_bv 64 15 /\ getr r' 17 = Z_to_bv 64 1024 /\ getr r' 5 = Z_to_bv 64 16 /\ getr r' 6 = Z_to_bv 64 17 /\ getr r' 7 = Z_to_bv 64 512)
        /\ (forall x : reg, ~ In x [11; 13; 15; 16; 17; 5; 6; 7; 28; 29; 30] -> getr r' x = getr r x).
  Proof using HTW Gpc G1 c pc RB HRF.
    intros r Q11 Q13 Q15 Q16 Q17 Q5 Q6 Q7.
    destruct G1 as [G1a G1b]. destruct Gpc as (Gp1 & Gp2 & Gp3). pose proof (u64_range sp) as Hspr. pose proof (u64_range cache). pose proof (u64_range pc).
    wd_eexists. split; [|split].
    -
      (* [comment removed for export] *)
      ab_ft R50a68 D_50a68 ltac:(condz). an R50a6c D_50a6c. an R50a70 D_50a70. ab_tk R50a74 D_50a74 ltac:(condz).
      an R50a94 D_50a94. an R50a98 D_50a98. ab_ft R50a9c D_50a9c ltac:(condz). an R50aa0 D_50aa0. an R50aa4 D_50aa4.
      an R50a44 D_50a44. an R50a48 D_50a48. an R50a4c D_50a4c. an R50a50 D_50a50. an R50a54 D_50a54.
      fsw4 R50a58 D_50a58 (at_ cache 84). fsd8c R50a5c D_50a5c (at_ cache 88).
      change (wbytes (wbytes (ICM 0) _ _) _ _) with (ICM 1).
      an R50a60 D_50a60.
      ab_ft R50a64 D_50a64 ltac:(condz).
      (* [comment removed for export] *)
      ab_ft R50a68 D_50a68 ltac:(condz). an R50a6c D_50a6c. an R50a70 D_50a70. ab_tk R50a74 D_50a74 ltac:(condz).
      an R50a94 D_50a94. an R50a98 D_50a98. ab_ft R50a9c D_50a9c ltac:(condz). an R50aa0 D_50aa0. an R50aa4 D_50aa4.
      an R50a44 D_50a44. an R50a48 D_50a48. an R50a4c D_50a4c. an R50a50 D_50a50. an R50a54 D_50a54.
      fsw4 R50a58 D_50a58 (at_ cache 164). fsd8c R50a5c D_50a5c (at_ cache 168).
      change (wbytes (wbytes (ICM 1) _ _) _ _) with (ICM 2).
      an R50a60 D_50a60.
      ab_ft R50a64 D_50a64 ltac:(condz).
      (* [comment removed for export] *)
      ab_ft R50a68 D_50a68 ltac:(condz). an R50a6c D_50a6c. an R50a70 D_50a70. ab_tk R50a74 D_50a74 ltac:(condz).
      an R50a94 D_50a94. an R50a98 D_50a98. ab_ft R50a9c D_50a9c ltac:(condz). an R50aa0 D_50aa0. an R50aa4 D_50aa4.
      an R50a44 D_50a44. an R50a48 D_50a48. an R50a4c D_50a4c. an R50a50 D_50a50. an R50a54 D_50a54.
      fsw4 R50a58 D_50a58 (at_ cache 244). fsd8c R50a5c D_50a5c (at_ cache 248).
      change (wbytes (wbytes (ICM 2) _ _) _ _) with (ICM 3).
      an R50a60 D_50a60.
      ab_ft R50a64 D_50a64 ltac:(condz).
      (* [comment removed for export] *)
      ab_ft R50a68 D_50a68 ltac:(condz). an R50a6c D_50a6c. an R50a70 D_50a70. ab_tk R50a74 D_50a74 ltac:(condz).
      an R50a94 D_50a94. an R50a98 D_50a98. ab_ft R50a9c D_50a9c ltac:(condz). an R50aa0 D_50aa0. an R50aa4 D_50aa4.
      an R50a44 D_50a44. an R50a48 D_50a48. an R50a4c D_50a4c. an R50a50 D_50a50. an R50a54 D_50a54.
      fsw4 R50a58 D_50a58 (at_ cache 324). fsd8c R50a5c D_50a5c (at_ cache 328).
      change (wbytes (wbytes (ICM 3) _ _) _ _) with (ICM 4).
      an R50a60 D_50a60.
      ab_ft R50a64 D_50a64 ltac:(condz).
      (* [comment removed for export] *)
      ab_ft R50a68 D_50a68 ltac:(condz). an R50a6c D_50a6c. an R50a70 D_50a70. ab_tk R50a74 D_50a74 ltac:(condz).
      an R50a94 D_50a94. an R50a98 D_50a98. ab_tk R50a9c D_50a9c ltac:(condz).
      an R50a44 D_50a44. an R50a48 D_50a48. an R50a4c D_50a4c. an R50a50 D_50a50. an R50a54 D_50a54.
      fsw4 R50a58 D_50a58 (at_ cache 404). fsd8c R50a5c D_50a5c (at_ cache 408).
      change (wbytes (wbytes (ICM 4) _ _) _ _) with (ICM 5).
      an R50a60 D_50a60.
      ab_ft R50a64 D_50a64 ltac:(condz).
      wd_refl.
    - repeat split; gres; first [reflexivity | assumption].
    - intros x Hx. gres. icK Hx.
  Qed.

  Lemma ic_6_10 : forall r,
      getr r 11 = at_ cache 488 -> getr r 13 = Z_to_bv 64 192 -> getr r 15 = Z_to_bv 64 18446744073709551606 -> getr r 16 = Z_to_bv 64 15 -> getr r 17 = Z_to_bv 64 1024 -> getr r 5 = Z_to_bv 64 16 -> getr r 6 = Z_to_bv 64 17 -> getr r 7 = Z_to_bv 64 512 ->
      exists r', msteps segs (mkst r (at_ rb 0x50a70) (ICM 5) rom) (mkst r' (at_ rb 0x50a70) (ICM 10) rom)
        /\ (getr r' 11 = at_ cache 888 /\ getr r' 13 = Z_to_bv 64 352 /\ getr r' 15 = Z_to_bv 64 18446744073709551611 /\ getr r' 16 = Z_to_bv 64 15 /\ getr r' 17 = Z_to_bv 64 1024 /\ getr r' 5 = Z_to_bv 64 16 /\ getr r' 6 = Z_to_bv 64 17 /\ getr r' 7 = Z_to_bv 64 512)
        /\ (forall x : reg, ~ In x [11; 13; 15; 16; 17; 5; 6; 7; 28; 29; 30] -> getr r' x = getr r x).
  Proof using HTW Gpc G1 c pc RB HRF.
    intros r Q11 Q13 Q15 Q16 Q17 Q5 Q6 Q7.
    destruct G1 as [G1a G1b]. destruct Gpc as (Gp1 & Gp2 & Gp3). pose proof (u64_range sp) as Hspr. pose proof (u64_range cache). pose proof (u64_range pc).
    wd_eexists. split; [|split].
    -
      (* [comment removed for export] *)
      ab_ft R50a68 D_50a68 ltac:(condz). an R50a6c D_50a6c. an R50a70 D_50a70. ab_tk R50a74 D_50a74 ltac:(condz).
      an R50a94 D_50a94. an R50a98 D_50a98. ab_tk R50a9c D_50a9c ltac:(condz).
      an R50a44 D_50a44. an R50a48 D_50a48. an R50a4c D_50a4c. an R50a50 D_50a50. an R50a54 D_50a54.
      fsw4 R50a58 D_50a58 (at_ cache 484). fsd8c R50a5c D_50a5c (at_ cache 488).
      change (wbytes (wbytes (ICM 5) _ _) _ _) with (ICM 6).
      an R50a60 D_50a60.
      ab_ft R50a64 D_50a64 ltac:(condz).
      (* [comment removed for export] *)
      ab_ft R50a68 D_50a68 ltac:(condz). an R50a6c D_50a6c. an R50a70 D_50a70. ab_tk R50a74 D_50a74 ltac:(condz).
      an R50a94 D_50a94. an R50a98 D_50a98. ab_tk R50a9c D_50a9c ltac:(condz).
      an R50a44 D_50a44. an R50a48 D_50a48. an R50a4c D_50a4c. an R50a50 D_50a50. an R50a54 D_50a54.
      fsw4 R50a58 D_50a58 (at_ cache 564). fsd8c R50a5c D_50a5c (at_ cache 568).
      change (wbytes (wbytes (ICM 6) _ _) _ _) with (ICM 7).
      an R50a60 D_50a60.
      ab_ft R50a64 D_50a64 ltac:(condz).
      (* [comment removed for export] *)
      ab_ft R50a68 D_50a68 ltac:(condz). an R50a6c D_50a6c. an R50a70 D_50a70. ab_tk R50a74 D_50a74 ltac:(condz).
      an R50a94 D_50a94. an R50a98 D_50a98. ab_tk R50a9c D_50a9c ltac:(condz).
      an R50a44 D_50a44. an R50a48 D_50a48. an R50a4c D_50a4c. an R50a50 D_50a50. an R50a54 D_50a54.
      fsw4 R50a58 D_50a58 (at_ cache 644). fsd8c R50a5c D_50a5c (at_ cache 648).
      change (wbytes (wbytes (ICM 7) _ _) _ _) with (ICM 8).
      an R50a60 D_50a60.
      ab_ft R50a64 D_50a64 ltac:(condz).
      (* [comment removed for export] *)
      ab_ft R50a68 D_50a68 ltac:(condz). an R50a6c D_50a6c. an R50a70 D_50a70. ab_tk R50a74 D_50a74 ltac:(condz).
      an R50a94 D_50a94. an R50a98 D_50a98. ab_tk R50a9c D_50a9c ltac:(condz).
      an R50a44 D_50a44. an R50a48 D_50a48. an R50a4c D_50a4c. an R50a50 D_50a50. an R50a54 D_50a54.
      fsw4 R50a58 D_50a58 (at_ cache 724). fsd8c R50a5c D_50a5c (at_ cache 728).
      change (wbytes (wbytes (ICM 8) _ _) _ _) with (ICM 9).
      an R50a60 D_50a60.
      ab_ft R50a64 D_50a64 ltac:(condz).
      (* [comment removed for export] *)
      ab_ft R50a68 D_50a68 ltac:(condz). an R50a6c D_50a6c. an R50a70 D_50a70. ab_tk R50a74 D_50a74 ltac:(condz).
      an R50a94 D_50a94. an R50a98 D_50a98. ab_tk R50a9c D_50a9c ltac:(condz).
      an R50a44 D_50a44. an R50a48 D_50a48. an R50a4c D_50a4c. an R50a50 D_50a50. an R50a54 D_50a54.
      fsw4 R50a58 D_50a58 (at_ cache 804). fsd8c R50a5c D_50a5c (at_ cache 808).
      change (wbytes (wbytes (ICM 9) _ _) _ _) with (ICM 10).
      an R50a60 D_50a60.
      ab_ft R50a64 D_50a64 ltac:(condz).
      wd_refl.
    - repeat split; gres; first [reflexivity | assumption].
    - intros x Hx. gres. icK Hx.
  Qed.

  Lemma ic_11_15 : forall r,
      getr r 11 = at_ cache 888 -> getr r 13 = Z_to_bv 64 352 -> getr r 15 = Z_to_bv 64 18446744073709551611 -> getr r 16 = Z_to_bv 64 15 -> getr r 17 = Z_to_bv 64 1024 -> getr r 5 = Z_to_bv 64 16 -> getr r 6 = Z_to_bv 64 17 -> getr r 7 = Z_to_bv 64 512 ->
      exists r', msteps segs (mkst r (at_ rb 0x50a70) (ICM 10) rom) (mkst r' (at_ rb 0x50a70) (ICM 15) rom)
        /\ (getr r' 11 = at_ cache 1288 /\ getr r' 13 = Z_to_bv 64 512 /\ getr r' 15 = Z_to_bv 64 0 /\ getr r' 16 = Z_to_bv 64 15 /\ getr r' 17 = Z_to_bv 64 1024 /\ getr r' 5 = Z_to_bv 64 16 /\ getr r' 6 = Z_to_bv 64 17 /\ getr r' 7 = Z_to_bv 64 512)
        /\ (forall x : reg, ~ In x [11; 13; 15; 16; 17; 5; 6; 7; 28; 29; 30] -> getr r' x = getr r x).
  Proof using HTW Gpc G1 c pc RB HRF.
    intros r Q11 Q13 Q15 Q16 Q17 Q5 Q6 Q7.
    destruct G1 as [G1a G1b]. destruct Gpc as (Gp1 & Gp2 & Gp3). pose proof (u64_range sp) as Hspr. pose proof (u64_range cache). pose proof (u64_range pc).
    wd_eexists. split; [|split].
    -
      (* [comment removed for export] *)
      ab_ft R50a68 D_50a68 ltac:(condz). an R50a6c D_50a6c. an R50a70 D_50a70. ab_tk R50a74 D_50a74 ltac:(condz).
      an R50a94 D_50a94. an R50a98 D_50a98. ab_tk R50a9c D_50a9c ltac:(condz).
      an R50a44 D_50a44. an R50a48 D_50a48. an R50a4c D_50a4c. an R50a50 D_50a50. an R50a54 D_50a54.
      fsw4 R50a58 D_50a58 (at_ cache 884). fsd8c R50a5c D_50a5c (at_ cache 888).
      change (wbytes (wbytes (ICM 10) _ _) _ _) with (ICM 11).
      an R50a60 D_50a60.
      ab_ft R50a64 D_50a64 ltac:(condz).
      (* [comment removed for export] *)
      ab_ft R50a68 D_50a68 ltac:(condz). an R50a6c D_50a6c. an R50a70 D_50a70. ab_tk R50a74 D_50a74 ltac:(condz).
      an R50a94 D_50a94. an R50a98 D_50a98. ab_tk R50a9c D_50a9c ltac:(condz).
      an R50a44 D_50a44. an R50a48 D_50a48. an R50a4c D_50a4c. an R50a50 D_50a50. an R50a54 D_50a54.
      fsw4 R50a58 D_50a58 (at_ cache 964). fsd8c R50a5c D_50a5c (at_ cache 968).
      change (wbytes (wbytes (ICM 11) _ _) _ _) with (ICM 12).
      an R50a60 D_50a60.
      ab_ft R50a64 D_50a64 ltac:(condz).
      (* [comment removed for export] *)
      ab_ft R50a68 D_50a68 ltac:(condz). an R50a6c D_50a6c. an R50a70 D_50a70. ab_tk R50a74 D_50a74 ltac:(condz).
      an R50a94 D_50a94. an R50a98 D_50a98. ab_tk R50a9c D_50a9c ltac:(condz).
      an R50a44 D_50a44. an R50a48 D_50a48. an R50a4c D_50a4c. an R50a50 D_50a50. an R50a54 D_50a54.
      fsw4 R50a58 D_50a58 (at_ cache 1044). fsd8c R50a5c D_50a5c (at_ cache 1048).
      change (wbytes (wbytes (ICM 12) _ _) _ _) with (ICM 13).
      an R50a60 D_50a60.
      ab_ft R50a64 D_50a64 ltac:(condz).
      (* [comment removed for export] *)
      ab_ft R50a68 D_50a68 ltac:(condz). an R50a6c D_50a6c. an R50a70 D_50a70. ab_tk R50a74 D_50a74 ltac:(condz).
      an R50a94 D_50a94. an R50a98 D_50a98. ab_tk R50a9c D_50a9c ltac:(condz).
      an R50a44 D_50a44. an R50a48 D_50a48. an R50a4c D_50a4c. an R50a50 D_50a50. an R50a54 D_50a54.
      fsw4 R50a58 D_50a58 (at_ cache 1124). fsd8c R50a5c D_50a5c (at_ cache 1128).
      change (wbytes (wbytes (ICM 13) _ _) _ _) with (ICM 14).
      an R50a60 D_50a60.
      ab_ft R50a64 D_50a64 ltac:(condz).
      (* [comment removed for export] *)
      ab_ft R50a68 D_50a68 ltac:(condz). an R50a6c D_50a6c. an R50a70 D_50a70. ab_tk R50a74 D_50a74 ltac:(condz).
      an R50a94 D_50a94. an R50a98 D_50a98. ab_tk R50a9c D_50a9c ltac:(condz).
      an R50a44 D_50a44. an R50a48 D_50a48. an R50a4c D_50a4c. an R50a50 D_50a50. an R50a54 D_50a54.
      fsw4 R50a58 D_50a58 (at_ cache 1204). fsd8c R50a5c D_50a5c (at_ cache 1208).
      change (wbytes (wbytes (ICM 14) _ _) _ _) with (ICM 15).
      an R50a60 D_50a60.
      ab_ft R50a64 D_50a64 ltac:(condz).
      wd_refl.
    - repeat split; gres; first [reflexivity | assumption].
    - intros x Hx. gres. icK Hx.
  Qed.

  Lemma ic_16_19 : forall r,
      getr r 11 = at_ cache 1288 -> getr r 13 = Z_to_bv 64 512 -> getr r 15 = Z_to_bv 64 0 -> getr r 16 = Z_to_bv 64 15 -> getr r 17 = Z_to_bv 64 1024 -> getr r 5 = Z_to_bv 64 16 -> getr r 6 = Z_to_bv 64 17 -> getr r 7 = Z_to_bv 64 512 ->
      exists r', msteps segs (mkst r (at_ rb 0x50a70) (ICM 15) rom) (mkst r' (at_ rb 0x50a70) (ICM 19) rom)
        /\ (getr r' 11 = at_ cache 1608 /\ getr r' 13 = Z_to_bv 64 640 /\ getr r' 15 = Z_to_bv 64 4 /\ getr r' 16 = Z_to_bv 64 15 /\ getr r' 17 = Z_to_bv 64 1024 /\ getr r' 5 = Z_to_bv 64 16 /\ getr r' 6 = Z_to_bv 64 17 /\ getr r' 7 = Z_to_bv 64 512)
        /\ (forall x : reg, ~ In x [11; 13; 15; 16; 17; 5; 6; 7; 28; 29; 30] -> getr r' x = getr r x).
  Proof using HTW Gpc G1 c pc RB HRF.
    intros r Q11 Q13 Q15 Q16 Q17 Q5 Q6 Q7.
    destruct G1 as [G1a G1b]. destruct Gpc as (Gp1 & Gp2 & Gp3). pose proof (u64_range sp) as Hspr. pose proof (u64_range cache). pose proof (u64_range pc).
    wd_eexists. split; [|split].
    -
      (* [comment removed for export] *)
      ab_ft R50a68 D_50a68 ltac:(condz). an R50a6c D_50a6c. an R50a70 D_50a70. ab_tk R50a74 D_50a74 ltac:(condz).
      an R50a94 D_50a94. an R50a98 D_50a98. ab_tk R50a9c D_50a9c ltac:(condz).
      an R50a44 D_50a44. an R50a48 D_50a48. an R50a4c D_50a4c. an R50a50 D_50a50. an R50a54 D_50a54.
      fsw4 R50a58 D_50a58 (at_ cache 1284). fsd8c R50a5c D_50a5c (at_ cache 1288).
      change (wbytes (wbytes (ICM 15) _ _) _ _) with (ICM 16).
      an R50a60 D_50a60.
      ab_ft R50a64 D_50a64 ltac:(condz).
      (* [comment removed for export] *)
      ab_ft R50a68 D_50a68 ltac:(condz). an R50a6c D_50a6c. an R50a70 D_50a70. ab_ft R50a74 D_50a74 ltac:(condz).
      an R50a78 D_50a78. an R50a7c D_50a7c. an R50a80 D_50a80. an R50a84 D_50a84. an R50a88 D_50a88. an R50a8c D_50a8c. an R50a90 D_50a90.
      an R50a94 D_50a94. an R50a98 D_50a98. ab_tk R50a9c D_50a9c ltac:(condz).
      an R50a44 D_50a44. an R50a48 D_50a48. an R50a4c D_50a4c. an R50a50 D_50a50. an R50a54 D_50a54.
      fsw4 R50a58 D_50a58 (at_ cache 1364). fsd8c R50a5c D_50a5c (at_ cache 1368).
      change (wbytes (wbytes (ICM 16) _ _) _ _) with (ICM 17).
      an R50a60 D_50a60.
      ab_ft R50a64 D_50a64 ltac:(condz).
      (* [comment removed for export] *)
      ab_ft R50a68 D_50a68 ltac:(condz). an R50a6c D_50a6c. an R50a70 D_50a70. ab_ft R50a74 D_50a74 ltac:(condz).
      an R50a78 D_50a78. an R50a7c D_50a7c. an R50a80 D_50a80. an R50a84 D_50a84. an R50a88 D_50a88. an R50a8c D_50a8c. an R50a90 D_50a90.
      an R50a94 D_50a94. an R50a98 D_50a98. ab_tk R50a9c D_50a9c ltac:(condz).
      an R50a44 D_50a44. an R50a48 D_50a48. an R50a4c D_50a4c. an R50a50 D_50a50. an R50a54 D_50a54.
      fsw4 R50a58 D_50a58 (at_ cache 1444). fsd8c R50a5c D_50a5c (at_ cache 1448).
      change (wbytes (wbytes (ICM 17) _ _) _ _) with (ICM 18).
      an R50a60 D_50a60.
      ab_ft R50a64 D_50a64 ltac:(condz).
      (* [comment removed for export] *)
      ab_ft R50a68 D_50a68 ltac:(condz). an R50a6c D_50a6c. an R50a70 D_50a70. ab_ft R50a74 D_50a74 ltac:(condz).
      an R50a78 D_50a78. an R50a7c D_50a7c. an R50a80 D_50a80. an R50a84 D_50a84. an R50a88 D_50a88. an R50a8c D_50a8c. an R50a90 D_50a90.
      an R50a94 D_50a94. an R50a98 D_50a98. ab_tk R50a9c D_50a9c ltac:(condz).
      an R50a44 D_50a44. an R50a48 D_50a48. an R50a4c D_50a4c. an R50a50 D_50a50. an R50a54 D_50a54.
      fsw4 R50a58 D_50a58 (at_ cache 1524). fsd8c R50a5c D_50a5c (at_ cache 1528).
      change (wbytes (wbytes (ICM 18) _ _) _ _) with (ICM 19).
      an R50a60 D_50a60.
      ab_ft R50a64 D_50a64 ltac:(condz).
      wd_refl.
    - repeat split; gres; first [reflexivity | assumption].
    - intros x Hx. gres. icK Hx.
  Qed.

End RFI.
End FPGen1.
