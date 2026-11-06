(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.As_code_50024_51024 OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac tauto ::= OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac.wd_tauto.   (* [comment removed for export] *)
Module AsAllocM7g.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.As_code_50024_51024.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; xlia zchecker) else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= am_lia.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

(* [comment removed for export] *)
Lemma Z_to_bv8_mod : forall a b, (a mod 256 = b mod 256)%Z -> Z_to_bv 8 a = Z_to_bv 8 b.
Proof. intros a b E. apply bv_eq. rewrite !Z_to_bv_unsigned. (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap in G in change_no_check G' end). change (bv_modulus 8) with 256%Z. exact E. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma LE4_lw : forall z, (0 <= z < 2 ^ 32)%Z -> word_to_le_bytes 4 (v_lw (Z_to_bv 64 z)) = word_to_le_bytes 4 (Z_to_bv 64 z).
Proof.
  intros z Hz. (lazymatch goal with |- ?G => let G' := eval unfold word_to_le_bytes, v_lw in G in change_no_check G' end). rewrite (u_Z2bv z) by lia. rewrite Z_to_bv_unsigned.
  set (w := bv_wrap 64 (bv_swrap 32 z)).
  assert (Hw : w = z \/ w = (z + 2 ^ 64 - 2 ^ 32)%Z).
  { (lazymatch goal with |- ?G => let G' := eval unfold w, bv_swrap, bv_wrap in G in change_no_check G' end). change (bv_modulus 32) with 4294967296%Z. change (bv_half_modulus 32) with 2147483648%Z.
    change (bv_modulus 64) with 18446744073709551616%Z.
    destruct (Z_lt_le_dec z (2 ^ 31)) as [L|G].
    - left. rewrite (Z.mod_small (z + 2147483648)) by lia. rewrite Z.mod_small by lia. lia.
    - right. Z.div_mod_to_equations. nia. }
  (lazymatch goal with |- ?G => let G' := eval cbn [Z_to_le_bytes] in G in change_no_check G' end). rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 8)%Z with 256%Z.
  destruct Hw as [-> | ->]; [reflexivity|].
  f_equal; [apply Z_to_bv8_mod; Z.div_mod_to_equations; lia|].
  f_equal; [apply Z_to_bv8_mod; Z.div_mod_to_equations; lia|].
  f_equal; [apply Z_to_bv8_mod; Z.div_mod_to_equations; lia|].
  f_equal. apply Z_to_bv8_mod; Z.div_mod_to_equations; lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FPGen1.
Context {fx : FPState}.

Definition gf_words : list (option (bv 32)) :=
  [Some W_50ac4; Some W_50ac8; Some W_50acc; Some W_50ad0; Some W_50ad4; Some W_50ad8; Some W_50adc; Some W_50ae0;
   Some W_50ae4; Some W_50ae8; Some W_50aec; Some W_50af0; Some W_50af4; Some W_50af8; Some W_50afc; Some W_50b00;
   Some W_50b04; Some W_50b08; Some W_50b0c; Some W_50b10; Some W_50b14; Some W_50b18; Some W_50b1c; Some W_50b20;
   Some W_50b24; Some W_50b28; Some W_50b2c; Some W_50b30; Some W_50b34; Some W_50b38; Some W_50b3c; Some W_50b40;
   Some W_50b44; Some W_50b48; Some W_50b4c; Some W_50b50; Some W_50b54; Some W_50b58; Some W_50b5c; Some W_50b60;
   Some W_50b64; Some W_50b68; Some W_50b6c; Some W_50b70; Some W_50b74; Some W_50b78; Some W_50b7c; Some W_50b80;
   Some W_50b84; Some W_50b88; Some W_50b8c; Some W_50b90; Some W_50b94; Some W_50b98; Some W_50b9c; Some W_50ba0;
   Some W_50ba4; Some W_50ba8; Some W_50bac; Some W_50bb0; Some W_50bb4; Some W_50bb8; Some W_50bbc; Some W_50bc0;
   Some W_50bc4; Some W_50bc8; Some W_50bcc; Some W_50bd0; Some W_50bd4; Some W_50bd8; Some W_50bdc; Some W_50be0;
   Some W_50be4; Some W_50be8; Some W_50bec; Some W_50bf0; Some W_50bf4; Some W_50bf8; Some W_50bfc; Some W_50c00;
   Some W_50c04; Some W_50c08; Some W_50c0c; Some W_50c10; Some W_50c14; Some W_50c18; Some W_50c1c; Some W_50c20;
   Some W_50c24; Some W_50c28; Some W_50c2c; Some W_50c30; Some W_50c34; Some W_50c38; Some W_50c3c; Some W_50c40;
   Some W_50c44; Some W_50c48; Some W_50c4c; Some W_50c50; Some W_50c54; Some W_50c58; Some W_50c5c; Some W_50c60;
   Some W_50c64; Some W_50c68; None; Some W_50c70; Some W_50c74; Some W_50c78; None; Some W_50c80;
   Some W_50c84; Some W_50c88; Some W_50c8c; Some W_50c90; Some W_50c94; Some W_50c98; Some W_50c9c; Some W_50ca0;
   Some W_50ca4; Some W_50ca8; Some W_50cac; Some W_50cb0; Some W_50cb4; Some W_50cb8; Some W_50cbc; Some W_50cc0;
   Some W_50cc4; Some W_50cc8; Some W_50ccc; Some W_50cd0; Some W_50cd4; Some W_50cd8; Some W_50cdc; Some W_50ce0;
   Some W_50ce4; Some W_50ce8; Some W_50cec; Some W_50cf0; Some W_50cf4; Some W_50cf8; Some W_50cfc; Some W_50d00;
   Some W_50d04; Some W_50d08; Some W_50d0c; Some W_50d10; Some W_50d14; Some W_50d18; Some W_50d1c; Some W_50d20;
   Some W_50d24; Some W_50d28; Some W_50d2c; Some W_50d30; Some W_50d34; Some W_50d38; Some W_50d3c; Some W_50d40;
   Some W_50d44; Some W_50d48; Some W_50d4c; Some W_50d50; Some W_50d54; Some W_50d58; Some W_50d5c; Some W_50d60]%list.

(* [comment removed for export] *)
Definition rf_clob : list reg := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30].
(* [comment removed for export] *)
Definition gf_mid : list reg := [2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section GF.
  Variable segs : list Segment.
  Variable rb : word.
  Hypothesis HGF : code_ato segs rb 0x50acc gf_words.
  Hypothesis RB : (U rb mod 2 = 0)%Z /\ (U rb + 2 ^ 24 < 2 ^ 64)%Z.
  (* [comment removed for export] *)
  Variable gmsk : Z.
  Hypothesis GMSK : gauipc_ld segs rb 0x50c74 0x50c84 14 14 gmsk.
  Hypothesis Ggm : (AIMGLO <= gmsk /\ gmsk + 8 <= AIMGHI)%Z.

  Lemma G50ac4 : fetch_word segs (at_ rb 0x50acc) = Some W_50ac4.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 0 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50ac8 : fetch_word segs (at_ rb 0x50ad0) = Some W_50ac8.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 1 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50acc : fetch_word segs (at_ rb 0x50ad4) = Some W_50acc.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 2 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50ad0 : fetch_word segs (at_ rb 0x50ad8) = Some W_50ad0.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 3 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50ad4 : fetch_word segs (at_ rb 0x50adc) = Some W_50ad4.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 4 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50ad8 : fetch_word segs (at_ rb 0x50ae0) = Some W_50ad8.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 5 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50adc : fetch_word segs (at_ rb 0x50ae4) = Some W_50adc.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 6 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50ae0 : fetch_word segs (at_ rb 0x50ae8) = Some W_50ae0.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 7 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50ae4 : fetch_word segs (at_ rb 0x50aec) = Some W_50ae4.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 8 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50ae8 : fetch_word segs (at_ rb 0x50af0) = Some W_50ae8.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 9 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50aec : fetch_word segs (at_ rb 0x50af4) = Some W_50aec.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 10 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50af0 : fetch_word segs (at_ rb 0x50af8) = Some W_50af0.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 11 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50af4 : fetch_word segs (at_ rb 0x50afc) = Some W_50af4.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 12 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50af8 : fetch_word segs (at_ rb 0x50b00) = Some W_50af8.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 13 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50afc : fetch_word segs (at_ rb 0x50b04) = Some W_50afc.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 14 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50b00 : fetch_word segs (at_ rb 0x50b08) = Some W_50b00.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 15 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50b04 : fetch_word segs (at_ rb 0x50b0c) = Some W_50b04.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 16 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50b08 : fetch_word segs (at_ rb 0x50b10) = Some W_50b08.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 17 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50b0c : fetch_word segs (at_ rb 0x50b14) = Some W_50b0c.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 18 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50b10 : fetch_word segs (at_ rb 0x50b18) = Some W_50b10.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 19 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50b14 : fetch_word segs (at_ rb 0x50b1c) = Some W_50b14.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 20 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50b18 : fetch_word segs (at_ rb 0x50b20) = Some W_50b18.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 21 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50b1c : fetch_word segs (at_ rb 0x50b24) = Some W_50b1c.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 22 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50b20 : fetch_word segs (at_ rb 0x50b28) = Some W_50b20.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 23 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50b24 : fetch_word segs (at_ rb 0x50b2c) = Some W_50b24.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 24 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50b28 : fetch_word segs (at_ rb 0x50b30) = Some W_50b28.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 25 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50b2c : fetch_word segs (at_ rb 0x50b34) = Some W_50b2c.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 26 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50b30 : fetch_word segs (at_ rb 0x50b38) = Some W_50b30.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 27 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50b34 : fetch_word segs (at_ rb 0x50b3c) = Some W_50b34.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 28 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50b38 : fetch_word segs (at_ rb 0x50b40) = Some W_50b38.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 29 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50b3c : fetch_word segs (at_ rb 0x50b44) = Some W_50b3c.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 30 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50b40 : fetch_word segs (at_ rb 0x50b48) = Some W_50b40.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 31 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50b44 : fetch_word segs (at_ rb 0x50b4c) = Some W_50b44.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 32 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50b48 : fetch_word segs (at_ rb 0x50b50) = Some W_50b48.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 33 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50b4c : fetch_word segs (at_ rb 0x50b54) = Some W_50b4c.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 34 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50b50 : fetch_word segs (at_ rb 0x50b58) = Some W_50b50.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 35 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50b54 : fetch_word segs (at_ rb 0x50b5c) = Some W_50b54.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 36 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50b58 : fetch_word segs (at_ rb 0x50b60) = Some W_50b58.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 37 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50b5c : fetch_word segs (at_ rb 0x50b64) = Some W_50b5c.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 38 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50b60 : fetch_word segs (at_ rb 0x50b68) = Some W_50b60.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 39 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50b64 : fetch_word segs (at_ rb 0x50b6c) = Some W_50b64.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 40 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50b68 : fetch_word segs (at_ rb 0x50b70) = Some W_50b68.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 41 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50b6c : fetch_word segs (at_ rb 0x50b74) = Some W_50b6c.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 42 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50b70 : fetch_word segs (at_ rb 0x50b78) = Some W_50b70.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 43 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50b74 : fetch_word segs (at_ rb 0x50b7c) = Some W_50b74.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 44 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50b78 : fetch_word segs (at_ rb 0x50b80) = Some W_50b78.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 45 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50b7c : fetch_word segs (at_ rb 0x50b84) = Some W_50b7c.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 46 _ HGF eq_refl). Qed.




































   (* [comment removed for export] *)
  Lemma G50c14 : fetch_word segs (at_ rb 0x50c1c) = Some W_50c14.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 84 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50c18 : fetch_word segs (at_ rb 0x50c20) = Some W_50c18.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 85 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50c1c : fetch_word segs (at_ rb 0x50c24) = Some W_50c1c.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 86 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50c20 : fetch_word segs (at_ rb 0x50c28) = Some W_50c20.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 87 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50c24 : fetch_word segs (at_ rb 0x50c2c) = Some W_50c24.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 88 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50c28 : fetch_word segs (at_ rb 0x50c30) = Some W_50c28.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 89 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50c2c : fetch_word segs (at_ rb 0x50c34) = Some W_50c2c.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 90 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50c30 : fetch_word segs (at_ rb 0x50c38) = Some W_50c30.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 91 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50c34 : fetch_word segs (at_ rb 0x50c3c) = Some W_50c34.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 92 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50c38 : fetch_word segs (at_ rb 0x50c40) = Some W_50c38.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 93 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50c3c : fetch_word segs (at_ rb 0x50c44) = Some W_50c3c.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 94 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50c40 : fetch_word segs (at_ rb 0x50c48) = Some W_50c40.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 95 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50c44 : fetch_word segs (at_ rb 0x50c4c) = Some W_50c44.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 96 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50c48 : fetch_word segs (at_ rb 0x50c50) = Some W_50c48.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 97 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50c4c : fetch_word segs (at_ rb 0x50c54) = Some W_50c4c.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 98 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50c50 : fetch_word segs (at_ rb 0x50c58) = Some W_50c50.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 99 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50c54 : fetch_word segs (at_ rb 0x50c5c) = Some W_50c54.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 100 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50c58 : fetch_word segs (at_ rb 0x50c60) = Some W_50c58.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 101 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50c5c : fetch_word segs (at_ rb 0x50c64) = Some W_50c5c.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 102 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50c60 : fetch_word segs (at_ rb 0x50c68) = Some W_50c60.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 103 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50c64 : fetch_word segs (at_ rb 0x50c6c) = Some W_50c64.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 104 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50c68 : fetch_word segs (at_ rb 0x50c70) = Some W_50c68.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 105 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50c70 : fetch_word segs (at_ rb 0x50c78) = Some W_50c70.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 107 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50c74 : fetch_word segs (at_ rb 0x50c7c) = Some W_50c74.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 108 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50c78 : fetch_word segs (at_ rb 0x50c80) = Some W_50c78.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 109 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
(* [comment removed for export] *)
  Lemma G50c80 : fetch_word segs (at_ rb 0x50c88) = Some W_50c80.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 111 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50c84 : fetch_word segs (at_ rb 0x50c8c) = Some W_50c84.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 112 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50c88 : fetch_word segs (at_ rb 0x50c90) = Some W_50c88.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 113 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50c8c : fetch_word segs (at_ rb 0x50c94) = Some W_50c8c.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 114 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50c90 : fetch_word segs (at_ rb 0x50c98) = Some W_50c90.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 115 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50c94 : fetch_word segs (at_ rb 0x50c9c) = Some W_50c94.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 116 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50c98 : fetch_word segs (at_ rb 0x50ca0) = Some W_50c98.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 117 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50c9c : fetch_word segs (at_ rb 0x50ca4) = Some W_50c9c.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 118 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50ca0 : fetch_word segs (at_ rb 0x50ca8) = Some W_50ca0.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 119 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50ca4 : fetch_word segs (at_ rb 0x50cac) = Some W_50ca4.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 120 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50ca8 : fetch_word segs (at_ rb 0x50cb0) = Some W_50ca8.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 121 _ HGF eq_refl). Qed.
   (* [comment removed for export] *)
  Lemma G50cb0 : fetch_word segs (at_ rb 0x50cb8) = Some W_50cb0.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 123 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50cb4 : fetch_word segs (at_ rb 0x50cbc) = Some W_50cb4.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 124 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50cb8 : fetch_word segs (at_ rb 0x50cc0) = Some W_50cb8.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 125 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50cbc : fetch_word segs (at_ rb 0x50cc4) = Some W_50cbc.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 126 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50cc0 : fetch_word segs (at_ rb 0x50cc8) = Some W_50cc0.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 127 _ HGF eq_refl). Qed.







   (* [comment removed for export] *)
  Lemma G50ce4 : fetch_word segs (at_ rb 0x50cec) = Some W_50ce4.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 136 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50ce8 : fetch_word segs (at_ rb 0x50cf0) = Some W_50ce8.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 137 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50cec : fetch_word segs (at_ rb 0x50cf4) = Some W_50cec.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 138 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50cf0 : fetch_word segs (at_ rb 0x50cf8) = Some W_50cf0.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 139 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50cf4 : fetch_word segs (at_ rb 0x50cfc) = Some W_50cf4.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 140 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50cf8 : fetch_word segs (at_ rb 0x50d00) = Some W_50cf8.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 141 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50cfc : fetch_word segs (at_ rb 0x50d04) = Some W_50cfc.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 142 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50d00 : fetch_word segs (at_ rb 0x50d08) = Some W_50d00.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 143 _ HGF eq_refl). Qed.


   (* [comment removed for export] *)
  Lemma G50d10 : fetch_word segs (at_ rb 0x50d18) = Some W_50d10.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 147 _ HGF eq_refl). Qed.



   (* [comment removed for export] *)
  Lemma G50d24 : fetch_word segs (at_ rb 0x50d2c) = Some W_50d24.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 152 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50d28 : fetch_word segs (at_ rb 0x50d30) = Some W_50d28.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 153 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50d2c : fetch_word segs (at_ rb 0x50d34) = Some W_50d2c.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 154 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50d30 : fetch_word segs (at_ rb 0x50d38) = Some W_50d30.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 155 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50d34 : fetch_word segs (at_ rb 0x50d3c) = Some W_50d34.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 156 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50d38 : fetch_word segs (at_ rb 0x50d40) = Some W_50d38.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 157 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50d3c : fetch_word segs (at_ rb 0x50d44) = Some W_50d3c.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 158 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50d40 : fetch_word segs (at_ rb 0x50d48) = Some W_50d40.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 159 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50d44 : fetch_word segs (at_ rb 0x50d4c) = Some W_50d44.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 160 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50d48 : fetch_word segs (at_ rb 0x50d50) = Some W_50d48.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 161 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50d4c : fetch_word segs (at_ rb 0x50d54) = Some W_50d4c.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 162 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50d50 : fetch_word segs (at_ rb 0x50d58) = Some W_50d50.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 163 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50d54 : fetch_word segs (at_ rb 0x50d5c) = Some W_50d54.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 164 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50d58 : fetch_word segs (at_ rb 0x50d60) = Some W_50d58.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 165 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50d5c : fetch_word segs (at_ rb 0x50d64) = Some W_50d5c.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 166 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G50d60 : fetch_word segs (at_ rb 0x50d68) = Some W_50d60.  Proof using HGF. exact (code_ato_get segs rb 0x50acc gf_words 167 _ HGF eq_refl). Qed.   (* [comment removed for export] *)

  Variables (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ra sp alloc chp : word) (c m SPB nf : Z) (msk stv : word).
  #[local] Abbreviation RIz := (SPB + 2 ^ 37 + 128 * c)%Z.
  #[local] Abbreviation RI := (Z_to_bv 64 (SPB + 2 ^ 37 + 128 * c)).
  #[local] Abbreviation FABz := (SPB + c * 2 ^ 32 + 3758096384)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H10 : getr regs 10 = alloc.
  Hypothesis H12 : getr regs 12 = Z_to_bv 64 c.
  Hypothesis H13 : getr regs 13 = chp.
  Hypothesis H14 : getr regs 14 = Z_to_bv 64 m.
  Hypothesis Hc : (1 <= c <= 30)%Z.
  Hypothesis Hm : (1 <= m <= 8)%Z /\ (m <= nf)%Z /\ (nf <= 2 ^ 27)%Z.
  Hypothesis GSPB : (0 <= SPB)%Z /\ (SPB + 2 ^ 37 + 4096 < 2 ^ 47)%Z /\ (SPB mod 2 ^ 16 = 0)%Z /\ (0x10007fff8000 <= SPB)%Z.
  Hypothesis G1 : (SPB + 2 ^ 37 + 4096 + 128 <= U sp)%Z /\ (U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Galloc : (AIMGLO <= U alloc /\ U alloc + 56 <= AIMGHI)%Z.
  (* [comment removed for export] *)
  Hypothesis Gchp : (U chp mod 4 = 0)%Z /\ (U chp + 64 <= U sp - 128)%Z
                    /\ (U chp + 64 <= SPB \/ SPB + 2 ^ 37 + 4096 <= U chp)%Z /\ (AIMGHI <= U chp \/ U chp + 64 <= AIMGLO)%Z.
  Hypothesis Hstk : store_ok segs mem (at_ sp (-128)) 128 = true.
  (* [comment removed for export] *)
  Hypothesis Rspb : rdn segs mem (at_ alloc 32) 8 = Some (LE8 (Z_to_bv 64 SPB)).
  Hypothesis Rrib : rdn segs mem (at_ alloc 48) 8 = Some (LE8 (Z_to_bv 64 (SPB + 2 ^ 37))).
  Hypothesis Rmu : rdn segs mem RI 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis SOKmu : store_ok segs mem RI 8 = true.
  Hypothesis Rnf : rdn segs mem (at_ RI 16) 8 = Some (LE8 (Z_to_bv 64 nf)).
  Hypothesis SOKnf : store_ok segs mem (at_ RI 16) 8 = true.
  Hypothesis Rst : rdn segs mem (at_ RI 72) 8 = Some (LE8 stv).
  Hypothesis SOKst : store_ok segs mem (at_ RI 72) 8 = true.
  Hypothesis Rmsk : rdn segs mem (Z_to_bv 64 gmsk) 8 = Some (LE8 msk).
  Hypothesis SOKch : store_ok segs mem chp (Z.to_nat (4 * m)) = true.
  (* [comment removed for export] *)
  Variable faf : Z -> Z.
  Hypothesis Hfaf : forall j, (nf - m <= j < nf)%Z -> rdn segs mem (Z_to_bv 64 (FABz + 4 * j)) 4 = Some (LE4 (faf j)) /\ (0 <= faf j < 2 ^ 32)%Z.

  #[local] Abbreviation CLX := (fun r : reg => In r rf_clob).
  #[local] Abbreviation CLM := (fun r : reg => In r gf_mid).

  (* [comment removed for export] *)
  Definition gf_frame : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
      (at_ sp (-8)) (LE8 ra)) (at_ sp (-16)) (LE8 (getr regs 8))) (at_ sp (-24)) (LE8 (getr regs 9)))
      (at_ sp (-32)) (LE8 (getr regs 18))) (at_ sp (-40)) (LE8 (getr regs 19))) (at_ sp (-48)) (LE8 (getr regs 20)))
      (at_ sp (-56)) (LE8 (getr regs 21))) (at_ sp (-64)) (LE8 (getr regs 22))) (at_ sp (-72)) (LE8 (getr regs 23)))
      (at_ sp (-80)) (LE8 (getr regs 24))) (at_ sp (-88)) (LE8 (getr regs 25))) (at_ sp (-96)) (LE8 (getr regs 26)))
      (at_ sp (-104)) (LE8 (getr regs 27)).
  Lemma gf_frame_outside : forall x : word, (U x < U sp - 128 \/ U sp <= U x)%Z -> gf_frame x = mem x.
  Proof using G1 GSPB SPB chp rb.
    intros x Hx. pose proof (u64_range sp). destruct G1 as [G1a G1b]. (lazymatch goal with |- ?G => let G' := eval unfold gf_frame in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); try lia. reflexivity.
  Qed.
  Lemma gf_frame_grows : mem_grows mem gf_frame.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold gf_frame in G in change_no_check G' end). do 13 (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
  Lemma gf_frame_slots : forall (k : Z) (v : word),
    In (k, v) [(-8, ra); (-16, getr regs 8); (-24, getr regs 9); (-32, getr regs 18); (-40, getr regs 19); (-48, getr regs 20);
               (-56, getr regs 21); (-64, getr regs 22); (-72, getr regs 23); (-80, getr regs 24); (-88, getr regs 25);
               (-96, getr regs 26); (-104, getr regs 27)]%Z ->
    rdn segs gf_frame (at_ sp k) 8 = Some (LE8 v).
  Proof using G1 GSPB SPB chp rb.
    intros k v Hin. pose proof (u64_range sp). destruct G1 as [G1a G1b]. (lazymatch goal with |- ?G => let G' := eval unfold gf_frame in G in change_no_check G' end). cbn [In] in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; rd8_chain|]). destruct Hin.
  Qed.

  (* [comment removed for export] *)
  Definition gf_m2 : word -> option byte :=
    wbytes (wbytes gf_frame RI (LE8 (Z_to_bv 64 (2 ^ 60)))) (at_ RI 16) (LE8 (Z_to_bv 64 (nf - m))).
  Lemma gf_m2_outside : forall x : word,
    (U x < U sp - 128 \/ U sp <= U x)%Z -> (U x < RIz \/ RIz + 8 <= U x)%Z -> (U x < RIz + 16 \/ RIz + 24 <= U x)%Z -> gf_m2 x = mem x.
  Proof using Gchp G1 GSPB Hc chp rb.
    intros x Hx Hy Hz. pose proof (u64_range sp). destruct G1 as [G1a G1b]. destruct GSPB as (S1 & S2 & S3 & S4). (lazymatch goal with |- ?G => let G' := eval unfold gf_m2 in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; rewrite ?at_u; unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); try lia.
    apply gf_frame_outside. exact Hx.
  Qed.

  Ltac sokS Hs0 lo N :=
    repeat (eapply store_ok_mono; [apply wbytes_grows|]);
    eapply (store_ok_sub segs mem lo _ N); [rewrite ?at_u; lia | exact Hs0 | rewrite ?at_u; lia | rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia].
  Ltac fsd8 F D aa :=
    chain_step; [reflexivity
      | eapply step_sd_at with (a := aa);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
        | gres; rwH; reflexivity
        | sokS Hstk (at_ sp (-128)) 128%nat ]
      | step_simpl]; vn.
  Ltac vz := cbv delta [v_add v_addi v_mul v_slli v_srli v_sub v_and v_or] beta; rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia; unorm;
             first [reflexivity | f_equal; lia | apply bv_eq; wd_ulia].
  (* [comment removed for export] *)
  Ltac vaddi_at := repeat match goal with |- context [v_addi ?a ?k] => change (v_addi a k) with (at_ a k) end.
  (* [comment removed for export] *)
  Ltac fld8 F D vv R := chain_step; [reflexivity
      | eapply step_ld with (bs := LE8 vv) (v := vv);
        [exact F | reflexivity | exact D | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi, ?at_at; vaddi_at; zlit_at; R | apply bytes_le_to_Z_8]
      | step_simpl]; vn.

  (* [comment removed for export] *)
  Lemma gfA :
    exists r,
      msteps segs (mkst regs (at_ rb 0x50acc) mem rom) (mkst r (at_ rb 0x50c40) gf_m2 rom)
      /\ getr r 2 = at_ sp (-128) /\ getr r 8 = RI /\ getr r 19 = Z_to_bv 64 (2 ^ 61) /\ getr r 20 = Z_to_bv 64 (FABz + 4 * (nf - m))
      /\ getr r 11 = at_ chp (4 * m) /\ getr r 13 = chp /\ getr r 14 = Z_to_bv 64 m
      /\ regs_agree CLM regs r.
  Proof using SOKnf Rnf SOKmu Rmu Rrib Rspb Hstk Gchp Galloc G1 GSPB Hm Hc H14 H13 H12 H10 H2 H1 alloc HGF.
    destruct G1 as [G1a G1b]. destruct Hm as (Hm1 & Hm2 & Hm3). destruct GSPB as (S1 & S2 & S3 & S4). destruct Gchp as (C1 & C2 & C3 & C4). destruct Galloc as [A1 A2].
    pose proof (u64_range sp) as Hspr. pose proof (u64_range alloc). pose proof (u64_range chp).
    assert (RI8 : (RIz mod 8 = 0)%Z) by (clear - S3 Hc; Z.div_mod_to_equations; lia).
    wd_eexists. split.
    - an G50ac4 D_50ac4.                                   (* [comment removed for export] *)
      fsd8 G50ac8 D_50ac8 (at_ sp (-8)).                   (* [comment removed for export] *)
      fsd8 G50acc D_50acc (at_ sp (-16)).                  (* [comment removed for export] *)
      fsd8 G50ad0 D_50ad0 (at_ sp (-24)).                  (* [comment removed for export] *)
      fsd8 G50ad4 D_50ad4 (at_ sp (-32)).                  (* [comment removed for export] *)
      fsd8 G50ad8 D_50ad8 (at_ sp (-40)).                  (* [comment removed for export] *)
      fsd8 G50adc D_50adc (at_ sp (-48)).                  (* [comment removed for export] *)
      fsd8 G50ae0 D_50ae0 (at_ sp (-56)).                  (* [comment removed for export] *)
      fsd8 G50ae4 D_50ae4 (at_ sp (-64)).                  (* [comment removed for export] *)
      fsd8 G50ae8 D_50ae8 (at_ sp (-72)).                  (* [comment removed for export] *)
      fsd8 G50aec D_50aec (at_ sp (-80)).                  (* [comment removed for export] *)
      fsd8 G50af0 D_50af0 (at_ sp (-88)).                  (* [comment removed for export] *)
      fsd8 G50af4 D_50af4 (at_ sp (-96)).                  (* [comment removed for export] *)
      fsd8 G50af8 D_50af8 (at_ sp (-104)).                 (* [comment removed for export] *)
      change (wbytes _ _ _) with gf_frame.
      an G50afc D_50afc.                                   (* [comment removed for export] *)
      an G50b00 D_50b00.                                   (* [comment removed for export] *)
      an G50b04 D_50b04.                                   (* [comment removed for export] *)
      fld8 G50b08 D_50b08 (Z_to_bv 64 SPB) ltac:(rewrite <- Rspb; apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply gf_frame_outside; rewrite at_u in Hx by lia; cbn in Hx; lia]).   (* [comment removed for export] *)
      fld8 G50b0c D_50b0c (Z_to_bv 64 (SPB + 2 ^ 37)) ltac:(rewrite <- Rrib; apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply gf_frame_outside; rewrite at_u in Hx by lia; cbn in Hx; lia]).   (* [comment removed for export] *)
      av G50b10 D_50b10 (Z_to_bv 64 (128 * c)) ltac:(vz).          (* [comment removed for export] *)
      av G50b14 D_50b14 (Z_to_bv 64 (c * 2 ^ 32)) ltac:(vz).       (* [comment removed for export] *)
      an G50b18 D_50b18.                                   (* [comment removed for export] *)
      an G50b1c D_50b1c.                                   (* [comment removed for export] *)
      av G50b20 D_50b20 (Z_to_bv 64 (2 ^ 61)) ltac:(vz).           (* [comment removed for export] *)
      av G50b24 D_50b24 (Z_to_bv 64 3758096384) ltac:(vz).         (* [comment removed for export] *)
      av G50b28 D_50b28 (Z_to_bv 64 (2 ^ 40)) ltac:(vz).           (* [comment removed for export] *)
      av G50b2c D_50b2c (Z_to_bv 64 (c * 2 ^ 32 + 3758096384)) ltac:(vz).   (* [comment removed for export] *)
      av G50b30 D_50b30 (Z_to_bv 64 (2 ^ 40 + 1)) ltac:(vz).       (* [comment removed for export] *)
      av G50b34 D_50b34 (Z_to_bv 64 (2 ^ 60 + 2 ^ 20)) ltac:(vz).  (* [comment removed for export] *)
      av G50b38 D_50b38 constr:(RI) ltac:(vz).                      (* [comment removed for export] *)
      av G50b3c D_50b3c (Z_to_bv 64 FABz) ltac:(vz).       (* [comment removed for export] *)
      av G50b40 D_50b40 (Z_to_bv 64 (2 ^ 60 + 2 ^ 20 - 1)) ltac:(vz).   (* [comment removed for export] *)
      fld8 G50b44 D_50b44 (Z_to_bv 64 0) ltac:(rewrite <- Rmu; apply rdn_ext; [wd_ulia_c | intros x Hx; apply gf_frame_outside; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia]).   (* [comment removed for export] *)
      av G50b48 D_50b48 (Z_to_bv 64 (RIz + 8)) ltac:(vz).  (* [comment removed for export] *)
      av G50b4c D_50b4c (Z_to_bv 64 (2 ^ 60)) ltac:(vz).    (* [comment removed for export] *)
      an G50b50 D_50b50.                                     (* [comment removed for export] *)
      an G50b54 D_50b54.   (* [comment removed for export] *)
      an G50b58 D_50b58.   (* [comment removed for export] *)
      an G50b5c D_50b5c.           (* [comment removed for export] *)
      ab_ft G50b60 D_50b60 ltac:(condz).                    (* [comment removed for export] *)
      an G50b64 D_50b64.    (* [comment removed for export] *)
      an G50b68 D_50b68.    (* [comment removed for export] *)
      (* [comment removed for export] *)
      eapply msteps_trans.
      { eapply (cas_d_run segs _ (at_ rb 0x50b74) (at_ rb 0x50b78) (at_ rb 0x50b7c) (at_ rb 0x50b80) (at_ rb 0x50b84) gf_frame rom
                  _ _ _ _ _ _ _ _ 5 8 7 6 5 17 BC_NE _ _ (LE8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
                  G50b6c eq_refl D_50b6c G50b70 eq_refl D_50b70 G50b74 eq_refl D_50b74 G50b78 eq_refl D_50b78);
          rewrite ?at_addi; try reflexivity.
        all: lazymatch goal with
             | |- _ <> _ => intros X; discriminate X
             | |- (_ mod 8 = 0)%Z => gres; unorm; exact RI8
             | |- rdn _ _ _ _ = _ => gres; rewrite <- Rmu; apply rdn_ext; [wd_ulia_c | intros x Hx; apply gf_frame_outside; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia]
             | |- store_ok _ _ _ _ = true => gres; eapply store_ok_mono; [apply gf_frame_grows | exact SOKmu]
             | |- branch_taken _ _ _ = false => (lazymatch goal with |- ?G => let G' := eval cbn [branch_taken] in G in change_no_check G' end); gres; rewrite bv_eqb_refl; reflexivity
             | |- _ => apply bytes_le_to_Z_8
             end. }
      gres.
      ab_tk G50b7c D_50b7c ltac:(condz).                    (* [comment removed for export] *)
      fld8 G50c14 D_50c14 (Z_to_bv 64 nf) ltac:(rewrite wc_rdn_wbytes_out3; [ | rd8_side ];
                 rewrite <- Rnf; apply rdn_ext; [rewrite at_u by (wd_ulia); wd_ulia_c | intros x Hx; apply gf_frame_outside; rewrite at_u in Hx by (wd_ulia); revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia]).   (* [comment removed for export] *)
      ab_ft G50c18 D_50c18 ltac:(condz).                    (* [comment removed for export] *)
      av G50c1c D_50c1c (Z_to_bv 64 (nf - m)) ltac:(vz).    (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_sd_at with (a := at_ RI 16);
          [exact G50c20 | reflexivity | exact D_50c20
          | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
          | gres; rwH; reflexivity
          | eapply store_ok_mono; [eapply mem_grows_trans; [apply gf_frame_grows | apply wbytes_grows] | exact SOKnf] ]
        | step_simpl]; vn.                                   (* [comment removed for export] *)
      change (wbytes (wbytes gf_frame _ _) _ _) with gf_m2.
      ab_ft G50c24 D_50c24 ltac:(condz).                    (* [comment removed for export] *)
      av G50c28 D_50c28 (Z_to_bv 64 (4 * (nf - m))) ltac:(vz).   (* [comment removed for export] *)
      av G50c2c D_50c2c (Z_to_bv 64 (FABz + 4 * (nf - m))) ltac:(vz).   (* [comment removed for export] *)
      av G50c30 D_50c30 (Z_to_bv 64 (4 * m)) ltac:(vz).      (* [comment removed for export] *)
      av G50c34 D_50c34 (at_ chp (4 * m)) ltac:(rewrite v_add_at by lia; reflexivity).   (* [comment removed for export] *)
      wd_refl.
    - post. (lazymatch goal with |- ?G => let G' := eval unfold gf_mid in G in change_no_check G' end). ra_solve.
  Qed.

  (* [comment removed for export] *)
  Fixpoint gf_cp (i : nat) : word -> option byte :=
    match i with
    | O => gf_m2
    | S i' => wbytes (gf_cp i') (at_ chp (4 * Z.of_nat i')) (LE4 (faf (nf - m + Z.of_nat i')%Z))
    end.
  Lemma gf_cp_grows : forall i, mem_grows gf_m2 (gf_cp i).
  Proof using. induction i as [|i IH]; [apply mem_grows_refl|]. (lazymatch goal with |- ?G => let G' := eval cbn [gf_cp] in G in change_no_check G' end). eapply mem_grows_trans; [exact IH | apply wbytes_grows]. Qed.
  Lemma gf_m2_grows : mem_grows mem gf_m2.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold gf_m2 in G in change_no_check G' end). eapply mem_grows_trans; [apply gf_frame_grows|]. eapply mem_grows_trans; apply wbytes_grows. Qed.
  Lemma gf_cp_outside : forall i (x : word), (Z.of_nat i <= m)%Z -> (U x < U chp \/ U chp + 4 * Z.of_nat i <= U x)%Z -> gf_cp i x = gf_m2 x.
  Proof using Gchp G1 GSPB Hm rb.
    induction i as [|i IH]; intros x Hi Hx; [reflexivity|]. (lazymatch goal with |- ?G => let G' := eval cbn [gf_cp] in G in change_no_check G' end). pose proof (u64_range chp). destruct Gchp as (C1 & C2 & C3 & C4). pose proof (u64_range sp).
    rewrite wbytes_outside; [apply IH; lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
  Qed.

  Lemma gfL : forall (j i : nat) r,
      (Z.of_nat i + Z.of_nat j = m)%Z -> (1 <= Z.of_nat j)%Z ->
      getr r 13 = at_ chp (4 * Z.of_nat i) -> getr r 20 = Z_to_bv 64 (FABz + 4 * (nf - m) + 4 * Z.of_nat i) -> getr r 11 = at_ chp (4 * m) ->
      exists r',
        msteps segs (mkst r (at_ rb 0x50c40) (gf_cp i) rom) (mkst r' (at_ rb 0x50c54) (gf_cp (Z.to_nat m)) rom)
        /\ (forall x : reg, ~ In x [12; 13; 20] -> getr r' x = getr r x).
  Proof using G1 GSPB Galloc Gchp Ggm HGF Hc Hfaf Hm RB SOKch.
    induction j as [|j IH]; intros i r Hij Hj R13 R20 R11; [lia|].
    destruct G1 as [G1a G1b]. destruct Hm as (Hm1 & Hm2 & Hm3). destruct GSPB as (S1 & S2 & S3 & S4). destruct Gchp as (C1 & C2 & C3 & C4).
    pose proof (u64_range sp) as Hspr. pose proof (u64_range chp).
    destruct (Hfaf (nf - m + Z.of_nat i)%Z ltac:(lia)) as [Rf Bf].
    assert (RD : rdn segs (gf_cp i) (Z_to_bv 64 (FABz + 4 * (nf - m) + 4 * Z.of_nat i)) 4 = Some (LE4 (faf (nf - m + Z.of_nat i)%Z))).
    { rewrite <- Rf. replace (FABz + 4 * (nf - m + Z.of_nat i))%Z with (FABz + 4 * (nf - m) + 4 * Z.of_nat i)%Z by lia.
      apply rdn_ext; [wd_ulia_c|]. intros x Hx. revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx.
      rewrite gf_cp_outside by lia. apply gf_m2_outside; lia. }
    assert (SOK : store_ok segs (gf_cp i) (at_ chp (4 * Z.of_nat i)) 4 = true).
    { eapply store_ok_mono; [eapply mem_grows_trans; [apply gf_m2_grows | apply gf_cp_grows]|].
      eapply (store_ok_sub segs mem chp _ (Z.to_nat (4 * m))); [lia | exact SOKch | rewrite at_u; lia | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia]. }
    (* [comment removed for export] *)
    assert (BODY : exists r1, msteps segs (mkst r (at_ rb 0x50c40) (gf_cp i) rom) (mkst r1 (at_ rb 0x50c50) (gf_cp (S i)) rom)
              /\ getr r1 13 = at_ chp (4 * Z.of_nat (S i)) /\ getr r1 20 = Z_to_bv 64 (FABz + 4 * (nf - m) + 4 * Z.of_nat (S i)) /\ getr r1 11 = at_ chp (4 * m)
              /\ (forall x : reg, ~ In x [12; 13; 20] -> getr r1 x = getr r x)).
    { wd_eexists. split.
      - chain_step; [reflexivity
          | eapply step_lw with (bs := LE4 (faf (nf - m + Z.of_nat i)%Z)) (v := Z_to_bv 64 (faf (nf - m + Z.of_nat i)%Z));
            [exact G50c38 | reflexivity | exact D_50c38 | gres; rewrite R20; imm_norm; rewrite ?v_addi_0; exact RD | apply bytes4_small; lia]
          | step_simpl]; vn.                               (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_sw_at with (a := at_ chp (4 * Z.of_nat i));
            [exact G50c3c | reflexivity | exact D_50c3c
            | gres; rewrite R13; imm_norm; rewrite ?v_addi_0, ?at_addi, ?at_add_0_r; reflexivity
            | gres; reflexivity
            | exact SOK ]
          | step_simpl]; vn.                               (* [comment removed for export] *)
        rewrite (LE4_lw (faf (nf - m + Z.of_nat i)%Z)) by lia. change (wbytes (gf_cp i) _ _) with (gf_cp (S i)).
        an G50c40 D_50c40.                                 (* [comment removed for export] *)
        an G50c44 D_50c44.                                 (* [comment removed for export] *)
        wd_refl.
      - split; [gres; rewrite ?at_at; f_equal; lia|]. split; [gres; vaddi_at; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia|].
        split; [gres; first [exact R11 | rewrite R11; reflexivity]|].
        intros x Hx. gres. rewrite !getr_other; [reflexivity| | |]; intros E; apply Hx; rewrite <- E; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]. }
    destruct BODY as (r1 & RUN1 & Q13 & Q20 & Q11 & QK).
    destruct (Z.eq_dec (Z.of_nat j) 0) as [Zj|NZj].
    - (* [comment removed for export] *)
      exists r1. split.
      + eapply msteps_trans; [exact RUN1|].
        ab_ft G50c48 D_50c48 ltac:(condz).
        replace (Z.to_nat m) with (S i) by lia. wd_refl.
      + exact QK.
    - destruct (IH (S i) r1 ltac:(lia) ltac:(lia) Q13 Q20 Q11) as (r' & RUN' & QK').
      exists r'. split.
      + eapply msteps_trans; [exact RUN1|].
        ab_tk G50c48 D_50c48 ltac:(condz).
        exact RUN'.
      + intros x Hx. rewrite (QK' x Hx). exact (QK x Hx).
  Qed.

  (* [comment removed for export] *)
  Definition gf_m4 : word -> option byte := wbytes (gf_cp (Z.to_nat m)) (at_ RI 72) (LE8 (v_add stv (Z_to_bv 64 m))).
  Definition gf_m5 : word -> option byte := wbytes gf_m4 RI (LE8 (Z_to_bv 64 0)).

  Lemma gf_m4_low : forall x : word, (U x < RIz \/ RIz + 80 <= U x)%Z -> (U x < U chp \/ U chp + 4 * m <= U x)%Z -> (U x < U sp - 128 \/ U sp <= U x)%Z -> gf_m4 x = mem x.
  Proof using Gchp G1 GSPB Hm Hc rb.
    intros x H1x H2x H3x. destruct G1 as [G1a G1b]. destruct Hm as (Hm1 & Hm2 & Hm3). destruct GSPB as (S1 & S2 & S3 & S4). destruct Gchp as (C1 & C2 & C3 & C4).
    pose proof (u64_range sp). pose proof (u64_range chp). (lazymatch goal with |- ?G => let G' := eval unfold gf_m4 in G in change_no_check G' end).
    rewrite wbytes_outside; [| rewrite length_N_to_le_bytes, at_u by (wd_ulia); wd_ulia_c | rewrite length_N_to_le_bytes, at_u by (wd_ulia); wd_ulia_c].
    rewrite gf_cp_outside by lia. apply gf_m2_outside; lia.
  Qed.
  Lemma gf_m5_frame : forall x : word, (U sp - 128 <= U x < U sp)%Z -> gf_m5 x = gf_frame x.
  Proof using Gchp G1 GSPB Hm Hc rb.
    intros x Hx. destruct G1 as [G1a G1b]. destruct Hm as (Hm1 & Hm2 & Hm3). destruct GSPB as (S1 & S2 & S3 & S4). destruct Gchp as (C1 & C2 & C3 & C4).
    pose proof (u64_range sp). pose proof (u64_range chp). (lazymatch goal with |- ?G => let G' := eval unfold gf_m5, gf_m4 in G in change_no_check G' end).
    rewrite wbytes_outside; [| rewrite length_N_to_le_bytes; wd_ulia_c | rewrite length_N_to_le_bytes; wd_ulia_c].
    rewrite wbytes_outside; [| rewrite length_N_to_le_bytes, at_u by (wd_ulia); wd_ulia_c | rewrite length_N_to_le_bytes, at_u by (wd_ulia); wd_ulia_c].
    rewrite gf_cp_outside by lia. (lazymatch goal with |- ?G => let G' := eval unfold gf_m2 in G in change_no_check G' end).
    rewrite wbytes_outside; [| rewrite length_N_to_le_bytes, at_u by (wd_ulia); wd_ulia_c | rewrite length_N_to_le_bytes, at_u by (wd_ulia); wd_ulia_c].
    rewrite wbytes_outside; [reflexivity | rewrite length_N_to_le_bytes; wd_ulia_c | rewrite length_N_to_le_bytes; wd_ulia_c].
  Qed.
  Lemma gf_mu4 : rdn segs gf_m4 RI 8 = Some (LE8 (Z_to_bv 64 (2 ^ 60))).
  Proof using Gchp G1 GSPB Hm Hc rb.
    destruct G1 as [G1a G1b]. destruct Hm as (Hm1 & Hm2 & Hm3). destruct GSPB as (S1 & S2 & S3 & S4). destruct Gchp as (C1 & C2 & C3 & C4).
    pose proof (u64_range sp). pose proof (u64_range chp). (lazymatch goal with |- ?G => let G' := eval unfold gf_m4 in G in change_no_check G' end).
    rewrite wc_rdn_wbytes_out3; [ | rd8_side ].
    transitivity (rdn segs gf_m2 RI 8).
    { apply rdn_ext; [wd_ulia_c|]. intros x Hx. revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx. apply gf_cp_outside; lia. }
    (lazymatch goal with |- ?G => let G' := eval unfold gf_m2 in G in change_no_check G' end). rewrite wc_rdn_wbytes_out3; [ | rd8_side ]. apply rdn_wbytes_hit8. unorm. lia.
  Qed.

  Lemma gfB : forall r0,
      getr r0 2 = at_ sp (-128) -> getr r0 8 = RI -> getr r0 19 = Z_to_bv 64 (2 ^ 61) -> getr r0 14 = Z_to_bv 64 m ->
      regs_agree CLM regs r0 ->
      exists r',
        msteps segs (mkst r0 (at_ rb 0x50c54) (gf_cp (Z.to_nat m)) rom) (mkst r' ra gf_m5 rom)
        /\ getr r' 10 = Z_to_bv 64 1 /\ getr r' 2 = sp /\ regs_agree CLX regs r'.
  Proof using G1 GMSK GSPB Galloc Gchp Ggm H1 H10 H12 H13 H14 H2 HGF Hc Hm Hret RB Rmsk Rst SOKmu SOKst.
    intros r0 R2 R8 R19 R14 AG0.
    destruct G1 as [G1a G1b]. destruct Hm as (Hm1 & Hm2 & Hm3). destruct GSPB as (S1 & S2 & S3 & S4). destruct Gchp as (C1 & C2 & C3 & C4). destruct Galloc as [A1 A2]. destruct Ggm as [Gg1 Gg2].
    pose proof (u64_range sp) as Hspr. pose proof (u64_range chp). pose proof (u64_range stv).
    assert (RI8 : (RIz mod 8 = 0)%Z) by (clear - S3 Hc; Z.div_mod_to_equations; lia).
    destruct GMSK as (xm & GMa & GMb).
    assert (Rst3 : rdn segs (gf_cp (Z.to_nat m)) (at_ RI 72) 8 = Some (LE8 stv)).
    { rewrite <- Rst. apply rdn_ext; [rewrite at_u by (wd_ulia); wd_ulia_c|]. intros x Hx. rewrite at_u in Hx by (wd_ulia). revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx.
      rewrite gf_cp_outside by lia. apply gf_m2_outside; lia. }
    assert (Rmsk4 : rdn segs gf_m4 (Z_to_bv 64 gmsk) 8 = Some (LE8 msk)).
    { rewrite <- Rmsk. apply rdn_ext; [wd_ulia_c|]. intros x Hx. revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx. apply gf_m4_low; lia. }
    assert (FR5 : forall (k : Z) (v : word),
      In (k, v) [(-8, ra); (-16, getr regs 8); (-24, getr regs 9); (-32, getr regs 18); (-40, getr regs 19); (-48, getr regs 20);
                 (-56, getr regs 21); (-64, getr regs 22); (-72, getr regs 23); (-80, getr regs 24); (-88, getr regs 25);
                 (-96, getr regs 26); (-104, getr regs 27)]%Z ->
      rdn segs gf_m5 (at_ sp k) 8 = Some (LE8 v)).
    { intros k v Hin. rewrite <- (gf_frame_slots k v Hin).
      assert (Hk : (-128 <= k <= -8)%Z) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply gf_m5_frame. lia. }
    wd_eexists. split; [|split; [|split]].
    - fld8 G50c4c D_50c4c stv ltac:(exact Rst3).        (* [comment removed for export] *)
      an G50c50 D_50c50.                                   (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_sd_at with (a := at_ RI 72);
          [exact G50c54 | reflexivity | exact D_50c54
          | gres; rwH; imm_norm; vaddi_at; rewrite ?at_addi; first [reflexivity | f_equal; lia]
          | gres; rwH; reflexivity
          | eapply store_ok_mono; [eapply mem_grows_trans; [apply gf_m2_grows | apply gf_cp_grows] | exact SOKst] ]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      change (wbytes (gf_cp _) _ _) with gf_m4.
      an G50c58 D_50c58.                                   (* [comment removed for export] *)
      fld8 G50c5c D_50c5c (Z_to_bv 64 (2 ^ 60)) ltac:(rewrite <- (at_0 RI) at 1; rewrite ?at_0; exact gf_mu4).   (* [comment removed for export] *)
      an G50c60 D_50c60.                                   (* [comment removed for export] *)
      an G50c64 D_50c64.                                   (* [comment removed for export] *)
      an G50c68 D_50c68.                                   (* [comment removed for export] *)
      eapply msteps_trans; [apply GMa|]. zlit_at.          (* [comment removed for export] *)
      an G50c70 D_50c70.                                   (* [comment removed for export] *)
      an G50c74 D_50c74.                                   (* [comment removed for export] *)
      an G50c78 D_50c78.                                   (* [comment removed for export] *)
      eapply msteps_trans; [eapply GMb; [gres; reflexivity | exact Rmsk4]|]. zlit_at.   (* [comment removed for export] *)
      an G50c80 D_50c80.                                   (* [comment removed for export] *)
      an G50c84 D_50c84.                                   (* [comment removed for export] *)
      an G50c88 D_50c88.                                   (* [comment removed for export] *)
      an G50c8c D_50c8c.                                   (* [comment removed for export] *)
      an G50c90 D_50c90.                                   (* [comment removed for export] *)
      an G50c94 D_50c94.                                   (* [comment removed for export] *)
      an G50cb0 D_50cb0.                                   (* [comment removed for export] *)
      an G50cb4 D_50cb4.                                   (* [comment removed for export] *)
      ab_ft G50cb8 D_50cb8 ltac:(condz).                  (* [comment removed for export] *)
      an G50cbc D_50cbc.                                   (* [comment removed for export] *)
      ab_tk G50cc0 D_50cc0 ltac:(condz).                  (* [comment removed for export] *)
      an G50ce4 D_50ce4.                                   (* [comment removed for export] *)
      an G50ce8 D_50ce8.                                   (* [comment removed for export] *)
      an G50cec D_50cec.                                   (* [comment removed for export] *)
      an G50cf0 D_50cf0.                                   (* [comment removed for export] *)
      an G50cf4 D_50cf4.                                   (* [comment removed for export] *)
      an G50cf8 D_50cf8.                                   (* [comment removed for export] *)
      an G50cfc D_50cfc.                                   (* [comment removed for export] *)
      ab_tk G50d00 D_50d00 ltac:(condz).                  (* [comment removed for export] *)
      eapply msteps_trans.
      { eapply (cas_d_run segs _ (at_ rb 0x50ca0) (at_ rb 0x50ca4) (at_ rb 0x50ca8) (at_ rb 0x50cac) (at_ rb 0x50cb0) gf_m4 rom
                  _ _ _ _ _ _ _ _ 7 8 28 6 7 12 BC_NE _ _ (LE8 (Z_to_bv 64 (2 ^ 60))) (Z_to_bv 64 (2 ^ 60))
                  G50c98 eq_refl D_50c98 G50c9c eq_refl D_50c9c G50ca0 eq_refl D_50ca0 G50ca4 eq_refl D_50ca4);
          rewrite ?at_addi; try reflexivity.
        all: lazymatch goal with
             | |- _ <> _ => intros X; discriminate X
             | |- (_ mod 8 = 0)%Z => gres; rwH; unorm; exact RI8
             | |- rdn _ _ _ _ = _ => gres; rwH; exact gf_mu4
             | |- store_ok _ _ _ _ = true => gres; rwH; (lazymatch goal with |- ?G => let G' := eval unfold gf_m4 in G in change_no_check G' end); eapply store_ok_mono; [|exact SOKmu];
                                              eapply mem_grows_trans; [apply gf_m2_grows|]; eapply mem_grows_trans; [apply gf_cp_grows | apply wbytes_grows]
             | |- branch_taken _ _ _ = false => (lazymatch goal with |- ?G => let G' := eval cbn [branch_taken] in G in change_no_check G' end); gres; rewrite bv_eqb_refl; reflexivity
             | |- _ => apply bytes_le_to_Z_8
             end. }
      gres. rwH. change (wbytes gf_m4 _ _) with gf_m5.
      ab_tk G50ca8 D_50ca8 ltac:(condz).                  (* [comment removed for export] *)
      ab_tk G50d10 D_50d10 ltac:(condz).                  (* [comment removed for export] *)
      an G50d24 D_50d24.                                   (* [comment removed for export] *)
      Ltac cldF F D vv H := chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 vv) (v := vv);
          [exact F | reflexivity | exact D | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi, ?at_at; zlit_at; apply H; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])] | apply bytes_le_to_Z_8]
        | step_simpl]; vn.
      cldF G50d28 D_50d28 ra (FR5 (-8)%Z).                          (* [comment removed for export] *)
      cldF G50d2c D_50d2c (getr regs 8) (FR5 (-16)%Z).              (* [comment removed for export] *)
      cldF G50d30 D_50d30 (getr regs 9) (FR5 (-24)%Z).              (* [comment removed for export] *)
      cldF G50d34 D_50d34 (getr regs 18) (FR5 (-32)%Z).             (* [comment removed for export] *)
      cldF G50d38 D_50d38 (getr regs 19) (FR5 (-40)%Z).             (* [comment removed for export] *)
      cldF G50d3c D_50d3c (getr regs 20) (FR5 (-48)%Z).             (* [comment removed for export] *)
      cldF G50d40 D_50d40 (getr regs 21) (FR5 (-56)%Z).             (* [comment removed for export] *)
      cldF G50d44 D_50d44 (getr regs 22) (FR5 (-64)%Z).             (* [comment removed for export] *)
      cldF G50d48 D_50d48 (getr regs 23) (FR5 (-72)%Z).             (* [comment removed for export] *)
      cldF G50d4c D_50d4c (getr regs 24) (FR5 (-80)%Z).             (* [comment removed for export] *)
      cldF G50d50 D_50d50 (getr regs 25) (FR5 (-88)%Z).             (* [comment removed for export] *)
      cldF G50d54 D_50d54 (getr regs 26) (FR5 (-96)%Z).             (* [comment removed for export] *)
      cldF G50d58 D_50d58 (getr regs 27) (FR5 (-104)%Z).            (* [comment removed for export] *)
      an G50d5c D_50d5c.                                   (* [comment removed for export] *)
      aret G50d60 D_50d60 ra.                              (* [comment removed for export] *)
      wd_refl.
    - gres. reflexivity.
    - gres. rewrite ?at_at. first [reflexivity | apply bv_eq; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]].
    - apply (regs_agree_strengthen rf_clob gf_mid regs).
      + (lazymatch goal with |- ?G => let G' := eval unfold gf_mid in G in change_no_check G' end).
        repeat (first [ apply regs_agree_upd; [solve [in_list] |]
                      | apply regs_agree_upd_keep; [ | first [reflexivity | rwH; rewrite ?at_0; reflexivity | symmetry; assumption] | let X := fresh in intros X; discriminate X ] ]).
        exact AG0.
      + intros i Hi Hni. cbn [gf_mid In] in Hi.
        repeat (destruct Hi as [<-|Hi]; [gres; rwH; rewrite ?at_at, ?at_addi, ?at_0; first [reflexivity | symmetry; assumption | apply bv_eq; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | f_equal; lia | exfalso; apply Hni; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]] |]).
        destruct Hi.
  Qed.

  (* [comment removed for export] *)
  Theorem gf_run :
    exists r', msteps segs (mkst regs (at_ rb 0x50acc) mem rom) (mkst r' ra gf_m5 rom)
      /\ getr r' 10 = Z_to_bv 64 1 /\ getr r' 2 = sp /\ regs_agree CLX regs r'.
  Proof using G1 GMSK GSPB Galloc Gchp Ggm H1 H10 H12 H13 H14 H2 HGF Hc Hfaf Hm Hret Hstk RB Rmsk Rmu Rnf Rrib Rspb Rst SOKch SOKmu SOKnf SOKst.
    destruct Hm as (Hm1 & Hm2 & Hm3).
    destruct gfA as (r1 & RUN1 & P2 & P8 & P19 & P20 & P11 & P13 & P14 & AG1).
    destruct (gfL (Z.to_nat m) 0 r1 ltac:(lia) ltac:(lia) ltac:(rewrite P13; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat] in G in change_no_check G' end); rewrite Z.mul_0_r, at_0; reflexivity)
                ltac:(rewrite P20; f_equal; lia) P11) as (r2 & RUN2 & QK).
    assert (AG2 : regs_agree CLM regs r2).
    { intros x Hx. rewrite QK; [exact (AG1 x Hx)|]. intros Hin. apply Hx. (lazymatch goal with |- ?G => let G' := eval unfold gf_mid in G in change_no_check G' end). cbn [In] in Hin |- *. clear - Hin. am_tauto. }
    destruct (gfB r2 ltac:(rewrite QK by notin; exact P2) ltac:(rewrite QK by notin; exact P8) ltac:(rewrite QK by notin; exact P19)
                ltac:(rewrite QK by notin; exact P14) AG2) as (r3 & RUN3 & Q10 & Q2 & AG3).
    exists r3. split; [|exact (conj Q10 (conj Q2 AG3))].
    eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. exact RUN3.
  Qed.

  (* [comment removed for export] *)
  Lemma gf_m5_grows : mem_grows mem gf_m5.
  Proof using.
    (lazymatch goal with |- ?G => let G' := eval unfold gf_m5, gf_m4 in G in change_no_check G' end). eapply mem_grows_trans; [apply gf_m2_grows|]. eapply mem_grows_trans; [apply gf_cp_grows|].
    eapply mem_grows_trans; apply wbytes_grows.
  Qed.
  Lemma gf_m5_outside : forall x : word,
    (U x < U sp - 128 \/ U sp <= U x)%Z -> (U x < RIz \/ RIz + 8 <= U x)%Z -> (U x < RIz + 16 \/ RIz + 24 <= U x)%Z ->
    (U x < RIz + 72 \/ RIz + 80 <= U x)%Z -> (U x < U chp \/ U chp + 4 * m <= U x)%Z -> gf_m5 x = mem x.
  Proof using Gchp G1 GSPB Hm Hc rb.
    intros x F1 F2 F3 F4 F5. destruct G1 as [G1a G1b]. destruct Hm as (Hm1 & Hm2 & Hm3). destruct GSPB as (S1 & S2 & S3 & S4). destruct Gchp as (C1 & C2 & C3 & C4).
    pose proof (u64_range sp). pose proof (u64_range chp). (lazymatch goal with |- ?G => let G' := eval unfold gf_m5, gf_m4 in G in change_no_check G' end).
    rewrite wbytes_outside; [| rewrite length_N_to_le_bytes; wd_ulia_c | rewrite length_N_to_le_bytes; wd_ulia_c].
    rewrite wbytes_outside; [| rewrite length_N_to_le_bytes, at_u by (wd_ulia); wd_ulia_c | rewrite length_N_to_le_bytes, at_u by (wd_ulia); wd_ulia_c].
    rewrite gf_cp_outside by lia. apply gf_m2_outside; lia.
  Qed.





End GF.
End FPGen1.
End AsAllocM7g.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9z OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.glaze.binary_reflection.images.Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocM8g.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9z.RefEnframeArith.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.As_code_50024_51024.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation U := bv_unsigned.

Ltac vz := cbv delta [v_add v_addi v_mul v_slli v_srli v_sub v_and v_or] beta; rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia; unorm;
           first [reflexivity | f_equal; lia | apply bv_eq; wd_ulia].

Section FPGen.
Context {fx : FPState}.

Definition gfp_frame (mem : word -> option byte) (sp ra s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ sp (-8)) (LE8 ra))
    (at_ sp (-16)) (LE8 s0v))
    (at_ sp (-24)) (LE8 s1v))
    (at_ sp (-32)) (LE8 s2v))
    (at_ sp (-40)) (LE8 s3v))
    (at_ sp (-48)) (LE8 s4v))
    (at_ sp (-56)) (LE8 s5v))
    (at_ sp (-64)) (LE8 s6v))
    (at_ sp (-72)) (LE8 s7v))
    (at_ sp (-80)) (LE8 s8v))
    (at_ sp (-88)) (LE8 s9v))
    (at_ sp (-96)) (LE8 s10v))
    (at_ sp (-104)) (LE8 s11v).
Definition gfp_m1 (mem : word -> option byte) (sp ra s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word) (RIz : Z) : word -> option byte :=
  wbytes (gfp_frame mem sp ra s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v) (Z_to_bv 64 RIz) (LE8 (Z_to_bv 64 (2 ^ 60))).
#[local] Hint Unfold gfp_frame gfp_m1 : asfr.

(* [comment removed for export] *)
Definition gfp_regs (sp chp : word) (RIz SPB c n : Z) (r : bvmap 5 word) : Prop :=
  getr r 2 = at_ sp (-128) /\ getr r 8 = Z_to_bv 64 RIz /\ getr r 9 = Z_to_bv 64 0x103f18 /\ getr r 18 = Z_to_bv 64 (RIz + 8)
  /\ getr r 19 = Z_to_bv 64 (2 ^ 61) /\ getr r 20 = Z_to_bv 64 (SPB + c * 2 ^ 32 + 0xE0000000)
  /\ getr r 21 = chp /\ getr r 22 = Z_to_bv 64 n.

Section PRE.
  Variables (mem rom : word -> option byte) (sp ra s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v stats chp : word) (SPB c n nf : Z).
  Variable regs : bvmap 5 word.
  #[local] Abbreviation RIz := (SPB + 2 ^ 37 + 128 * c)%Z.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 0x103f18.
  Hypothesis H11 : getr regs 11 = stats.
  Hypothesis H12 : getr regs 12 = Z_to_bv 64 c.
  Hypothesis H13 : getr regs 13 = chp.
  Hypothesis H14 : getr regs 14 = Z_to_bv 64 n.
  Hypothesis H8 : getr regs 8 = s0v.   Hypothesis H9 : getr regs 9 = s1v.   Hypothesis H18 : getr regs 18 = s2v.
  Hypothesis H19 : getr regs 19 = s3v. Hypothesis H20 : getr regs 20 = s4v. Hypothesis H21 : getr regs 21 = s5v.
  Hypothesis H22 : getr regs 22 = s6v. Hypothesis H23 : getr regs 23 = s7v. Hypothesis H24 : getr regs 24 = s8v.
  Hypothesis H25 : getr regs 25 = s9v. Hypothesis H26 : getr regs 26 = s10v. Hypothesis H27 : getr regs 27 = s11v.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hc : (1 <= c <= 30)%Z.
  Hypothesis Hn : (0 <= nf < n /\ n <= 8)%Z.
  Hypothesis HSPB : (0 <= SPB /\ SPB + 2 ^ 37 + 4096 < 2 ^ 63 /\ SPB mod 8 = 0)%Z.
  Hypothesis HRI : (AIMGHI <= SPB /\ RIz + 128 <= U sp - 128)%Z.
  Hypothesis Hstk : store_ok ASEGS mem (at_ sp (-128)) 128 = true.
  Hypothesis C_sbeg : rdn ASEGS mem (Z_to_bv 64 (0x103f18 + 32)) 8 = Some (LE8 (Z_to_bv 64 SPB)).
  Hypothesis C_rib : rdn ASEGS mem (Z_to_bv 64 (0x103f18 + 48)) 8 = Some (LE8 (Z_to_bv 64 (SPB + 2 ^ 37))).
  Hypothesis R_mtx : rdn ASEGS mem (Z_to_bv 64 RIz) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis R_nf : rdn ASEGS mem (Z_to_bv 64 (RIz + 16)) 8 = Some (LE8 (Z_to_bv 64 nf)).
  Hypothesis SOK_mtx : store_ok ASEGS mem (Z_to_bv 64 RIz) 8 = true.

  #[local] Abbreviation MF := (gfp_frame mem sp ra s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v).
  #[local] Abbreviation M1 := (gfp_m1 mem sp ra s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v RIz).

  Lemma gfp_pre :
    exists r, msteps ASEGS (mkst regs (0x50acc : word) mem rom) (mkst r (0x50dd4 : word) M1 rom)
      /\ gfp_regs sp chp RIz SPB c n r /\ getr r 1 = Z_to_bv 64 0x50d88
      /\ getr r 10 = Z_to_bv 64 0x103f18 /\ getr r 11 = stats /\ getr r 12 = Z_to_bv 64 c /\ getr r 13 = Z_to_bv 64 RIz
      /\ getr r 14 = Z_to_bv 64 (n - nf)
      /\ regs_agree (fun i : reg => In i [1; 2; 5; 6; 7; 8; 9; 10; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 28]) regs r.
  Proof using SOK_mtx R_nf R_mtx C_rib C_sbeg Hstk HRI HSPB Hn Hc Hsp H27 H26 H25 H24 H23 H22 H21 H20 H19 H18 H9 H8 H14 H13 H12 H11 H10 H2 H1.
    (lazymatch goal with |- ?G => let G' := eval unfold gfp_regs in G in change_no_check G' end). pose proof (u64_range sp) as Hspr. destruct HSPB as (S1 & S2 & S3). destruct HRI as [RI1 RI2]. destruct Hn as [N1 N2].
    assert (RI8 : (RIz mod 8 = 0)%Z) by (clear - S3 Hc; Z.div_mod_to_equations; lia).
    wd_eexists. split.
    - an F_50ac4 D_50ac4.                              (* [comment removed for export] *)
      fsd F_50ac8 D_50ac8 (at_ sp (-8)).               (* [comment removed for export] *)
      fsd F_50acc D_50acc (at_ sp (-16)).              (* [comment removed for export] *)
      fsd F_50ad0 D_50ad0 (at_ sp (-24)).              (* [comment removed for export] *)
      fsd F_50ad4 D_50ad4 (at_ sp (-32)).              (* [comment removed for export] *)
      fsd F_50ad8 D_50ad8 (at_ sp (-40)).              (* [comment removed for export] *)
      fsd F_50adc D_50adc (at_ sp (-48)).              (* [comment removed for export] *)
      fsd F_50ae0 D_50ae0 (at_ sp (-56)).              (* [comment removed for export] *)
      fsd F_50ae4 D_50ae4 (at_ sp (-64)).              (* [comment removed for export] *)
      fsd F_50ae8 D_50ae8 (at_ sp (-72)).              (* [comment removed for export] *)
      fsd F_50aec D_50aec (at_ sp (-80)).              (* [comment removed for export] *)
      fsd F_50af0 D_50af0 (at_ sp (-88)).              (* [comment removed for export] *)
      fsd F_50af4 D_50af4 (at_ sp (-96)).              (* [comment removed for export] *)
      fsd F_50af8 D_50af8 (at_ sp (-104)).             (* [comment removed for export] *)
      change (wbytes _ _ _) with MF.
      an F_50afc D_50afc.                              (* [comment removed for export] *)
      an F_50b00 D_50b00.                              (* [comment removed for export] *)
      an F_50b04 D_50b04.                              (* [comment removed for export] *)
      cld8 F_50b08 D_50b08 (Z_to_bv 64 SPB) C_sbeg.    (* [comment removed for export] *)
      cld8 F_50b0c D_50b0c (Z_to_bv 64 (SPB + 2 ^ 37)) C_rib.   (* [comment removed for export] *)
      av F_50b10 D_50b10 (Z_to_bv 64 (128 * c)) ltac:(vz).   (* [comment removed for export] *)
      av F_50b14 D_50b14 (Z_to_bv 64 (c * 2 ^ 32)) ltac:(vz).   (* [comment removed for export] *)
      an F_50b18 D_50b18.                              (* [comment removed for export] *)
      an F_50b1c D_50b1c.                              (* [comment removed for export] *)
      av F_50b20 D_50b20 (Z_to_bv 64 (2 ^ 61)) ltac:(vz).   (* [comment removed for export] *)
      av F_50b24 D_50b24 (Z_to_bv 64 0xE0000000) ltac:(vz).   (* [comment removed for export] *)
      av F_50b28 D_50b28 (Z_to_bv 64 (2 ^ 40)) ltac:(vz).   (* [comment removed for export] *)
      av F_50b2c D_50b2c (Z_to_bv 64 (c * 2 ^ 32 + 0xE0000000)) ltac:(vz).   (* [comment removed for export] *)
      av F_50b30 D_50b30 (Z_to_bv 64 (2 ^ 40 + 1)) ltac:(vz).   (* [comment removed for export] *)
      av F_50b34 D_50b34 (Z_to_bv 64 (2 ^ 60 + 2 ^ 20)) ltac:(vz).   (* [comment removed for export] *)
      av F_50b38 D_50b38 (Z_to_bv 64 RIz) ltac:(vz).   (* [comment removed for export] *)
      av F_50b3c D_50b3c (Z_to_bv 64 (SPB + c * 2 ^ 32 + 0xE0000000)) ltac:(vz).   (* [comment removed for export] *)
      av F_50b40 D_50b40 (Z_to_bv 64 (2 ^ 60 + 2 ^ 20 - 1)) ltac:(vz).   (* [comment removed for export] *)
      cld8 F_50b44 D_50b44 (Z_to_bv 64 0) R_mtx.       (* [comment removed for export] *)
      av F_50b48 D_50b48 (Z_to_bv 64 (RIz + 8)) ltac:(vz).   (* [comment removed for export] *)
      av F_50b4c D_50b4c (Z_to_bv 64 (2 ^ 60)) ltac:(vz).   (* [comment removed for export] *)
      an F_50b50 D_50b50.                              (* [comment removed for export] *)
      an F_50b54 D_50b54.                              (* [comment removed for export] *)
      an F_50b58 D_50b58.                              (* [comment removed for export] *)
      an F_50b5c D_50b5c.                              (* [comment removed for export] *)
      ab_ft F_50b60 D_50b60 ltac:(condz).              (* [comment removed for export] *)
      an F_50b64 D_50b64.                              (* [comment removed for export] *)
      an F_50b68 D_50b68.                              (* [comment removed for export] *)
      (* [comment removed for export] *)
      eapply msteps_trans.
      { eapply (cas_d_run ASEGS _ (0x50b74 : word) (0x50b78 : word) (0x50b7c : word) (0x50b80 : word) (0x50b84 : word) MF rom
                  _ _ _ _ _ _ _ _ 5 8 7 6 5 17 BC_NE _ _ (LE8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
                  F_50b6c eq_refl D_50b6c F_50b70 eq_refl D_50b70 F_50b74 eq_refl D_50b74 F_50b78 eq_refl D_50b78).
        all: lazymatch goal with
             | |- v_addi _ _ = _ => first [reflexivity | apply bv_eq; vm_compute; reflexivity]
             | |- _ <> _ => intros X; discriminate X
             | |- (_ mod 8 = 0)%Z => gres; rwH; unorm; exact RI8
             | |- rdn _ _ _ _ = _ => gres; rwH; rd_peel; exact R_mtx
             | |- store_ok _ _ _ _ = true => gres; rwH; any_ok
             | |- branch_taken _ _ _ = false => (lazymatch goal with |- ?G => let G' := eval cbn [branch_taken] in G in change_no_check G' end); gres; rewrite bv_eqb_refl; reflexivity
             | |- _ => apply bytes_le_to_Z_8
             end. }
      gres. rwH.
      change (wbytes MF _ _) with M1.
      ab_tk F_50b7c D_50b7c ltac:(condz).              (* [comment removed for export] *)
      cld8 F_50c14 D_50c14 (Z_to_bv 64 nf) R_nf.       (* [comment removed for export] *)
      ab_tk F_50c18 D_50c18 ltac:(condz).              (* [comment removed for export] *)
      an F_50d64 D_50d64.                              (* [comment removed for export] *)
      an F_50d68 D_50d68.                              (* [comment removed for export] *)
      an F_50d6c D_50d6c.                              (* [comment removed for export] *)
      av F_50d70 D_50d70 (Z_to_bv 64 (n - nf)) ltac:(vz).   (* [comment removed for export] *)
      an F_50d74 D_50d74.                              (* [comment removed for export] *)
      an F_50d78 D_50d78.                              (* [comment removed for export] *)
      an F_50d7c D_50d7c.                              (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.
End PRE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section TAIL.
  Variables (M rom : word -> option byte) (sp ra s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v msk : word) (RIz res : Z).
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis HRI : (AIMGHI <= RIz /\ RIz + 128 <= U sp - 128 /\ RIz mod 8 = 0)%Z.
  Hypothesis Hres : (0 <= res <= 1)%Z.
  Hypothesis R_mtx : rdn ASEGS M (Z_to_bv 64 RIz) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 60))).
  Hypothesis R_msk : rdn ASEGS M (Z_to_bv 64 0x10470) 8 = Some (LE8 msk).
  Hypothesis SOK_mtx : store_ok ASEGS M (Z_to_bv 64 RIz) 8 = true.
  Hypothesis S_ra : rdn ASEGS M (at_ sp (-8)) 8 = Some (LE8 ra).
  Hypothesis S_s0 : rdn ASEGS M (at_ sp (-16)) 8 = Some (LE8 s0v).
  Hypothesis S_s1 : rdn ASEGS M (at_ sp (-24)) 8 = Some (LE8 s1v).
  Hypothesis S_s2 : rdn ASEGS M (at_ sp (-32)) 8 = Some (LE8 s2v).
  Hypothesis S_s3 : rdn ASEGS M (at_ sp (-40)) 8 = Some (LE8 s3v).
  Hypothesis S_s4 : rdn ASEGS M (at_ sp (-48)) 8 = Some (LE8 s4v).
  Hypothesis S_s5 : rdn ASEGS M (at_ sp (-56)) 8 = Some (LE8 s5v).
  Hypothesis S_s6 : rdn ASEGS M (at_ sp (-64)) 8 = Some (LE8 s6v).
  Hypothesis S_s7 : rdn ASEGS M (at_ sp (-72)) 8 = Some (LE8 s7v).
  Hypothesis S_s8 : rdn ASEGS M (at_ sp (-80)) 8 = Some (LE8 s8v).
  Hypothesis S_s9 : rdn ASEGS M (at_ sp (-88)) 8 = Some (LE8 s9v).
  Hypothesis S_s10 : rdn ASEGS M (at_ sp (-96)) 8 = Some (LE8 s10v).
  Hypothesis S_s11 : rdn ASEGS M (at_ sp (-104)) 8 = Some (LE8 s11v).

  Definition gfp_post (regs r : bvmap 5 word) : Prop :=
    getr r 10 = Z_to_bv 64 res /\ getr r 2 = sp /\ getr r 1 = ra
    /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v /\ getr r 20 = s4v /\ getr r 21 = s5v /\ getr r 22 = s6v
    /\ getr r 23 = s7v /\ getr r 24 = s8v /\ getr r 25 = s9v /\ getr r 26 = s10v /\ getr r 27 = s11v
    /\ regs_agree (fun i : reg => In i [1; 2; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28]) regs r.

  Lemma gfp_tail : forall regs : bvmap 5 word,
    getr regs 2 = at_ sp (-128) -> getr regs 8 = Z_to_bv 64 RIz -> getr regs 9 = Z_to_bv 64 res -> getr regs 19 = Z_to_bv 64 (2 ^ 61) ->
    exists r, msteps ASEGS (mkst regs (0x50c64 : word) M rom) (mkst r ra (wbytes M (Z_to_bv 64 RIz) (LE8 (Z_to_bv 64 0))) rom)
      /\ gfp_post regs r.
  Proof using S_s11 S_s10 S_s9 S_s8 S_s7 S_s6 S_s5 S_s4 S_s3 S_s2 S_s1 S_s0 S_ra SOK_mtx R_msk R_mtx HRI Hret Hsp msk.
    intros regs H2 H8 H9 H19. (lazymatch goal with |- ?G => let G' := eval unfold gfp_post in G in change_no_check G' end). pose proof (u64_range sp) as Hspr. destruct HRI as (RI1 & RI2 & RI8).
    wd_eexists. split.
    - cld8 F_50c5c D_50c5c (Z_to_bv 64 (2 ^ 60)) R_mtx.   (* [comment removed for export] *)
      an F_50c60 D_50c60.                              (* [comment removed for export] *)
      an F_50c64 D_50c64.                              (* [comment removed for export] *)
      an F_50c68 D_50c68.                              (* [comment removed for export] *)
      an F_50c6c D_50c6c.                              (* [comment removed for export] *)
      an F_50c70 D_50c70.                              (* [comment removed for export] *)
      an F_50c74 D_50c74.                              (* [comment removed for export] *)
      an F_50c78 D_50c78.                              (* [comment removed for export] *)
      cld8 F_50c7c D_50c7c msk R_msk.                  (* [comment removed for export] *)
      an F_50c80 D_50c80.                              (* [comment removed for export] *)
      an F_50c84 D_50c84.                              (* [comment removed for export] *)
      an F_50c88 D_50c88.                              (* [comment removed for export] *)
      an F_50c8c D_50c8c.                              (* [comment removed for export] *)
      an F_50c90 D_50c90.                              (* [comment removed for export] *)
      an F_50c94 D_50c94.                              (* [comment removed for export] *)
      an F_50cb0 D_50cb0.                              (* [comment removed for export] *)
      an F_50cb4 D_50cb4.                              (* [comment removed for export] *)
      ab_ft F_50cb8 D_50cb8 ltac:(condz).              (* [comment removed for export] *)
      an F_50cbc D_50cbc.                              (* [comment removed for export] *)
      ab_tk F_50cc0 D_50cc0 ltac:(condz).              (* [comment removed for export] *)
      an F_50ce4 D_50ce4.                              (* [comment removed for export] *)
      an F_50ce8 D_50ce8.                              (* [comment removed for export] *)
      an F_50cec D_50cec.                              (* [comment removed for export] *)
      an F_50cf0 D_50cf0.                              (* [comment removed for export] *)
      an F_50cf4 D_50cf4.                              (* [comment removed for export] *)
      an F_50cf8 D_50cf8.                              (* [comment removed for export] *)
      an F_50cfc D_50cfc.                              (* [comment removed for export] *)
      ab_tk F_50d00 D_50d00 ltac:(condz).              (* [comment removed for export] *)
      eapply msteps_trans.
      { eapply (cas_d_run ASEGS _ (0x50ca0 : word) (0x50ca4 : word) (0x50ca8 : word) (0x50cac : word) (0x50cb0 : word) M rom
                  _ _ _ _ _ _ _ _ 7 8 28 6 7 12 BC_NE _ _ (LE8 (Z_to_bv 64 (2 ^ 60))) (Z_to_bv 64 (2 ^ 60))
                  F_50c98 eq_refl D_50c98 F_50c9c eq_refl D_50c9c F_50ca0 eq_refl D_50ca0 F_50ca4 eq_refl D_50ca4).
        all: lazymatch goal with
             | |- v_addi _ _ = _ => first [reflexivity | apply bv_eq; vm_compute; reflexivity]
             | |- _ <> _ => intros X; discriminate X
             | |- (_ mod 8 = 0)%Z => gres; rwH; unorm; exact RI8
             | |- rdn _ _ _ _ = _ => gres; rwH; exact R_mtx
             | |- store_ok _ _ _ _ = true => gres; rwH; exact SOK_mtx
             | |- branch_taken _ _ _ = false => (lazymatch goal with |- ?G => let G' := eval cbn [branch_taken] in G in change_no_check G' end); gres; rewrite bv_eqb_refl; reflexivity
             | |- _ => apply bytes_le_to_Z_8
             end. }
      gres. rwH.
      ab_tk F_50ca8 D_50ca8 ltac:(condz).              (* [comment removed for export] *)
      ab_tk F_50d10 D_50d10 ltac:(condz).              (* [comment removed for export] *)
      an F_50d24 D_50d24.                              (* [comment removed for export] *)
      cld8 F_50d28 D_50d28 ra S_ra.                    (* [comment removed for export] *)
      cld8 F_50d2c D_50d2c s0v S_s0.                   (* [comment removed for export] *)
      cld8 F_50d30 D_50d30 s1v S_s1.                   (* [comment removed for export] *)
      cld8 F_50d34 D_50d34 s2v S_s2.                   (* [comment removed for export] *)
      cld8 F_50d38 D_50d38 s3v S_s3.                   (* [comment removed for export] *)
      cld8 F_50d3c D_50d3c s4v S_s4.                   (* [comment removed for export] *)
      cld8 F_50d40 D_50d40 s5v S_s5.                   (* [comment removed for export] *)
      cld8 F_50d44 D_50d44 s6v S_s6.                   (* [comment removed for export] *)
      cld8 F_50d48 D_50d48 s7v S_s7.                   (* [comment removed for export] *)
      cld8 F_50d4c D_50d4c s8v S_s8.                   (* [comment removed for export] *)
      cld8 F_50d50 D_50d50 s9v S_s9.                   (* [comment removed for export] *)
      cld8 F_50d54 D_50d54 s10v S_s10.                 (* [comment removed for export] *)
      cld8 F_50d58 D_50d58 s11v S_s11.                 (* [comment removed for export] *)
      an F_50d5c D_50d5c.                              (* [comment removed for export] *)
      aret F_50d60 D_50d60 ra.                         (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.

  (* [comment removed for export] *)
  Lemma gfp_fail : forall regs : bvmap 5 word, res = 0%Z ->
    getr regs 2 = at_ sp (-128) -> getr regs 8 = Z_to_bv 64 RIz -> getr regs 19 = Z_to_bv 64 (2 ^ 61) -> getr regs 10 = Z_to_bv 64 0 ->
    exists r, msteps ASEGS (mkst regs (0x50d88 : word) M rom) (mkst r ra (wbytes M (Z_to_bv 64 RIz) (LE8 (Z_to_bv 64 0))) rom)
      /\ gfp_post regs r.
  Proof using S_s11 S_s10 S_s9 S_s8 S_s7 S_s6 S_s5 S_s4 S_s3 S_s2 S_s1 S_s0 S_ra SOK_mtx R_msk R_mtx Hres HRI Hret Hsp msk.
    intros regs Eres H2 H8 H19 H10. pose proof (u64_range sp) as Hspr.
    assert (HEAD : exists r1, msteps ASEGS (mkst regs (0x50d88 : word) M rom) (mkst r1 (0x50c64 : word) M rom)
              /\ getr r1 2 = at_ sp (-128) /\ getr r1 8 = Z_to_bv 64 RIz /\ getr r1 9 = Z_to_bv 64 res /\ getr r1 19 = Z_to_bv 64 (2 ^ 61)
              /\ regs_agree (fun i : reg => In i [9; 10]) regs r1).
    { wd_eexists. split.
      - ab_tk F_50d80 D_50d80 ltac:(condz).            (* [comment removed for export] *)
        an F_50da4 D_50da4.                            (* [comment removed for export] *)
        an F_50da8 D_50da8.                            (* [comment removed for export] *)
        an F_50dac D_50dac.                            (* [comment removed for export] *)
        wd_refl.
      - rewrite Eres. post. ra_solve. }
    destruct HEAD as (r1 & RUN1 & A2 & A8 & A9 & A19 & AG1).
    destruct (gfp_tail r1 A2 A8 A9 A19) as (r2 & RUN2 & P2).
    exists r2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2]|].
    unfold gfp_post in *. destruct P2 as (B10 & B2 & B1 & B8 & B9 & B18 & B19 & B20 & B21 & B22 & B23 & B24 & B25 & B26 & B27 & AG2).
    repeat (split; [assumption|]).
    intros x Hx. rewrite (AG2 x Hx). apply AG1. intros Hin. apply Hx. cbn [In] in *. tauto.
  Qed.
End TAIL.
End FPGen.
End AsAllocM8g.
Module AsAllocM8h.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9z.RefEnframeArith.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac AsAllocM7g AsAllocM8g OSSVerify.Proofs.glaze.binary_reflection.lib.As_code_50024_51024.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

Section FPGen.
Context {fx : FPState}.

(* [comment removed for export] *)
Fixpoint gh_cp (M2 : word -> option byte) (chp : word) (faf : Z -> Z) (lo : Z) (i : nat) : word -> option byte :=
  match i with
  | O => M2
  | S i' => wbytes (gh_cp M2 chp faf lo i') (at_ chp (4 * Z.of_nat i')) (LE4 (faf (lo + Z.of_nat i')%Z))
  end.
Lemma gh_cp_grows : forall M2 chp faf lo i, mem_grows M2 (gh_cp M2 chp faf lo i).
Proof using. induction i as [|i IH]; [apply mem_grows_refl|]. (lazymatch goal with |- ?G => let G' := eval cbn [gh_cp] in G in change_no_check G' end). eapply mem_grows_trans; [exact IH | apply wbytes_grows]. Qed.
Lemma gh_cp_outside : forall M2 chp faf lo i (x : word), (U chp + 4 * Z.of_nat i < 2 ^ 64)%Z ->
  (U x < U chp \/ U chp + 4 * Z.of_nat i <= U x)%Z -> gh_cp M2 chp faf lo i x = M2 x.
Proof using.
  induction i as [|i IH]; intros x Hn Hx; [reflexivity|]. (lazymatch goal with |- ?G => let G' := eval cbn [gh_cp] in G in change_no_check G' end). pose proof (u64_range chp).
  destruct Hx as [Hx|Hx].
  - rewrite wbytes_below; [apply IH; lia | rewrite length_N_to_le_bytes, at_u by lia; lia | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]].
  - rewrite wbytes_above; [apply IH; lia | rewrite length_N_to_le_bytes, at_u by lia; lia].
Qed.

Definition gh_m2 (MP : word -> option byte) (RIz nf2 n : Z) : word -> option byte :=
  wbytes MP (Z_to_bv 64 (RIz + 16)) (LE8 (Z_to_bv 64 (nf2 - n))).
Definition gh_m4 (MP : word -> option byte) (chp stv : word) (faf : Z -> Z) (RIz nf2 n : Z) : word -> option byte :=
  wbytes (gh_cp (gh_m2 MP RIz nf2 n) chp faf (nf2 - n) (Z.to_nat n)) (Z_to_bv 64 (RIz + 72)) (LE8 (v_add stv (Z_to_bv 64 n))).
Definition gh_m5 (MP : word -> option byte) (chp stv : word) (faf : Z -> Z) (RIz nf2 n : Z) : word -> option byte :=
  wbytes (gh_m4 MP chp stv faf RIz nf2 n) (Z_to_bv 64 RIz) (LE8 (Z_to_bv 64 0)).

Section OK.
  Variables (MP rom : word -> option byte) (sp ra s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v chp stv msk : word)
            (SPB c n nf2 : Z) (faf : Z -> Z).
  #[local] Abbreviation RIz := (SPB + 2 ^ 37 + 128 * c)%Z.
  #[local] Abbreviation FAB := (SPB + c * 2 ^ 32 + 0xE0000000)%Z.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis Hc : (1 <= c <= 30)%Z.
  Hypothesis Hn : (1 <= n <= 8 /\ n <= nf2 /\ nf2 <= 2 ^ 27)%Z.
  Hypothesis HSPB : (0 <= SPB /\ SPB + 2 ^ 37 + 4096 < 2 ^ 63 /\ SPB mod 8 = 0)%Z.
  Hypothesis HRI : (AIMGHI <= SPB /\ RIz + 128 <= U sp - 128)%Z.
  (* [comment removed for export] *)
  Hypothesis Hchp : ((U chp + 4 * n <= SPB \/ SPB + 2 ^ 37 + 4096 <= U chp) /\ U chp + 4 * n <= U sp - 128 /\ (AIMGHI <= U chp \/ U chp + 4 * n <= AIMGLO))%Z.
  Hypothesis R_nf : rdn ASEGS MP (Z_to_bv 64 (RIz + 16)) 8 = Some (LE8 (Z_to_bv 64 nf2)).
  Hypothesis R_st : rdn ASEGS MP (Z_to_bv 64 (RIz + 72)) 8 = Some (LE8 stv).
  Hypothesis R_mtx : rdn ASEGS MP (Z_to_bv 64 RIz) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 60))).
  Hypothesis R_msk : rdn ASEGS MP (Z_to_bv 64 0x10470) 8 = Some (LE8 msk).
  Hypothesis SOK_RI : store_ok ASEGS MP (Z_to_bv 64 RIz) 128 = true.
  Hypothesis SOK_ch : store_ok ASEGS MP chp (Z.to_nat (4 * n)) = true.
  Hypothesis Hfaf : forall j, (nf2 - n <= j < nf2)%Z -> rdn ASEGS MP (Z_to_bv 64 (FAB + 4 * j)) 4 = Some (LE4 (faf j)) /\ (0 <= faf j < 2 ^ 32)%Z.

  #[local] Abbreviation M2 := (gh_m2 MP RIz nf2 n).
  #[local] Abbreviation CP := (gh_cp (gh_m2 MP RIz nf2 n) chp faf (nf2 - n)).

  Lemma gh_m2_outside : forall x : word, (U x < RIz + 16 \/ RIz + 24 <= U x)%Z -> M2 x = MP x.
  Proof using HRI HSPB Hn Hc Hsp sp.
    intros x Hx. destruct HSPB as (S1 & S2 & S3). (lazymatch goal with |- ?G => let G' := eval unfold gh_m2 in G in change_no_check G' end).
    destruct Hx as [Hx|Hx]; [apply wbytes_below | apply wbytes_above]; wd_lenlit; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma gh_head : forall regs : bvmap 5 word, gfp_regs sp chp RIz SPB c n regs -> getr regs 10 = Z_to_bv 64 1 ->
    exists r, msteps ASEGS (mkst regs (0x50d88 : word) MP rom) (mkst r (0x50c40 : word) M2 rom)
      /\ getr r 2 = at_ sp (-128) /\ getr r 8 = Z_to_bv 64 RIz /\ getr r 19 = Z_to_bv 64 (2 ^ 61)
      /\ getr r 13 = chp /\ getr r 20 = Z_to_bv 64 (FAB + 4 * (nf2 - n)) /\ getr r 11 = at_ chp (4 * n) /\ getr r 14 = Z_to_bv 64 n
      /\ regs_agree (fun i : reg => In i [10; 11; 13; 14; 15; 20]) regs r.
  Proof using SOK_RI R_nf Hchp HRI HSPB Hn Hc Hsp.
    intros regs HR H10. destruct HR as (R2 & R8 & R9 & R18 & R19 & R20 & R21 & R22).
    pose proof (u64_range sp) as Hspr. pose proof (u64_range chp) as Hchr. destruct HSPB as (S1 & S2 & S3). destruct HRI as [RI1 RI2]. destruct Hn as (N1 & N2 & N3).
    wd_eexists. split.
    - ab_ft F_50d80 D_50d80 ltac:(condz).              (* [comment removed for export] *)
      cld8 F_50d84 D_50d84 (Z_to_bv 64 nf2) R_nf.      (* [comment removed for export] *)
      an F_50d88 D_50d88.                              (* [comment removed for export] *)
      ab_ft F_50d8c D_50d8c ltac:(condz).              (* [comment removed for export] *)
      an F_50d90 D_50d90.                              (* [comment removed for export] *)
      av F_50d94 D_50d94 (Z_to_bv 64 (nf2 - n)) ltac:(vz).   (* [comment removed for export] *)
      fsd F_50d98 D_50d98 (Z_to_bv 64 (RIz + 16)).     (* [comment removed for export] *)
      change (wbytes MP _ _) with M2.
      an F_50d9c D_50d9c.                              (* [comment removed for export] *)
      an F_50da0 D_50da0.                              (* [comment removed for export] *)
      av F_50c28 D_50c28 (Z_to_bv 64 (4 * (nf2 - n))) ltac:(vz).   (* [comment removed for export] *)
      av F_50c2c D_50c2c (Z_to_bv 64 (FAB + 4 * (nf2 - n))) ltac:(vz).   (* [comment removed for export] *)
      av F_50c30 D_50c30 (Z_to_bv 64 (4 * n)) ltac:(vz).   (* [comment removed for export] *)
      av F_50c34 D_50c34 (at_ chp (4 * n)) ltac:(rewrite v_add_at by lia; reflexivity).   (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.

  (* [comment removed for export] *)
  Lemma gh_loop : forall (j i : nat) (r : bvmap 5 word),
      (Z.of_nat i + Z.of_nat j = n)%Z -> (1 <= Z.of_nat j)%Z ->
      getr r 13 = at_ chp (4 * Z.of_nat i) -> getr r 20 = Z_to_bv 64 (FAB + 4 * (nf2 - n) + 4 * Z.of_nat i) -> getr r 11 = at_ chp (4 * n) ->
      exists r',
        msteps ASEGS (mkst r (0x50c40 : word) (CP i) rom) (mkst r' (0x50c54 : word) (CP (Z.to_nat n)) rom)
        /\ (forall x : reg, ~ In x [12; 13; 20] -> getr r' x = getr r x).
  Proof using Hfaf SOK_ch Hchp HRI HSPB Hn Hc Hsp sp.
    induction j as [|j IH]; intros i r Hij Hj R13 R20 R11; [lia|].
    pose proof (u64_range sp) as Hspr. pose proof (u64_range chp) as Hchr.
    destruct HSPB as (S1 & S2 & S3). destruct HRI as [RI1 RI2]. destruct Hn as (N1 & N2 & N3). destruct Hchp as (C1 & C2 & _).
    destruct (Hfaf (nf2 - n + Z.of_nat i)%Z ltac:(lia)) as [Rf Bf].
    assert (RD : rdn ASEGS (CP i) (Z_to_bv 64 (FAB + 4 * (nf2 - n) + 4 * Z.of_nat i)) 4 = Some (LE4 (faf (nf2 - n + Z.of_nat i)%Z))).
    { rewrite <- Rf. replace (FAB + 4 * (nf2 - n + Z.of_nat i))%Z with (FAB + 4 * (nf2 - n) + 4 * Z.of_nat i)%Z by lia.
      apply rdn_ext; [first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite u_Z2bv in Hx by lia. cbn in Hx.
      rewrite gh_cp_outside by lia. apply gh_m2_outside. lia. }
    assert (SOK : store_ok ASEGS (CP i) (at_ chp (4 * Z.of_nat i)) 4 = true).
    { eapply store_ok_mono; [eapply mem_grows_trans; [apply wbytes_grows | apply gh_cp_grows]|].
      eapply (store_ok_sub ASEGS MP chp _ (Z.to_nat (4 * n))); [lia | exact SOK_ch | rewrite at_u; lia | rewrite at_u by lia; rewrite Z2Nat.id by lia; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia]. }
    assert (BODY : exists r1, msteps ASEGS (mkst r (0x50c40 : word) (CP i) rom) (mkst r1 (0x50c50 : word) (CP (S i)) rom)
              /\ getr r1 13 = at_ chp (4 * Z.of_nat (S i)) /\ getr r1 20 = Z_to_bv 64 (FAB + 4 * (nf2 - n) + 4 * Z.of_nat (S i)) /\ getr r1 11 = at_ chp (4 * n)
              /\ (forall x : reg, ~ In x [12; 13; 20] -> getr r1 x = getr r x)).
    { wd_eexists. split.
      - chain_step; [reflexivity
          | eapply step_lw with (bs := LE4 (faf (nf2 - n + Z.of_nat i)%Z)) (v := Z_to_bv 64 (faf (nf2 - n + Z.of_nat i)%Z));
            [exact F_50c38 | reflexivity | exact D_50c38 | gres; rewrite ?R20; imm_norm; rewrite ?v_addi_0; exact RD | apply bytes4_small; lia]
          | step_simpl]; vn.                               (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_sw_at with (a := at_ chp (4 * Z.of_nat i));
            [exact F_50c3c | reflexivity | exact D_50c3c
            | gres; rewrite ?R13; imm_norm; rewrite ?v_addi_0, ?at_addi, ?at_add_0_r; reflexivity
            | gres; reflexivity
            | exact SOK ]
          | step_simpl]; vn.                               (* [comment removed for export] *)
        rewrite (LE4_lw (faf (nf2 - n + Z.of_nat i)%Z)) by lia.
        change (wbytes (CP i) _ _) with (CP (S i)).
        an F_50c40 D_50c40.                                (* [comment removed for export] *)
        an F_50c44 D_50c44.                                (* [comment removed for export] *)
        wd_refl.
      - split; [gres; rewrite ?R13, ?at_addi, ?at_at; f_equal; lia|].
        split; [gres; rewrite ?R20; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_addi, at_ in G in change_no_check G' end); wd_ulia|].
        split; [gres; first [exact R11 | rewrite R11; reflexivity]|].
        intros x Hx. gres. rewrite !getr_other; try reflexivity; intros E; apply Hx; rewrite <- E; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto. }
    destruct BODY as (r1 & RUN1 & Q13 & Q20 & Q11 & QK).
    destruct (Z.eq_dec (Z.of_nat j) 0) as [Zj|NZj].
    - exists r1. split.
      + eapply msteps_trans; [exact RUN1|].
        ab_ft F_50c48 D_50c48 ltac:(rewrite ?Q13, ?Q11; condz).   (* [comment removed for export] *)
        replace (Z.to_nat n) with (S i) by lia. wd_refl.
      + exact QK.
    - destruct (IH (S i) r1 ltac:(lia) ltac:(lia) Q13 Q20 Q11) as (r' & RUN' & QK').
      exists r'. split.
      + eapply msteps_trans; [exact RUN1|].
        ab_tk F_50c48 D_50c48 ltac:(rewrite ?Q13, ?Q11; condz).   (* [comment removed for export] *)
        exact RUN'.
      + intros x Hx. rewrite (QK' x Hx). exact (QK x Hx).
  Qed.

  #[local] Abbreviation M4 := (gh_m4 MP chp stv faf RIz nf2 n).

  Lemma gh_cpn_outside : forall x : word, (U x < U chp \/ U chp + 4 * n <= U x)%Z -> (U x < RIz + 16 \/ RIz + 24 <= U x)%Z ->
    CP (Z.to_nat n) x = MP x.
  Proof using Hchp HRI HSPB Hn Hc Hsp sp.
    intros x Hx Hy. pose proof (u64_range chp). destruct Hn as (N1 & N2 & N3). destruct Hchp as (C1 & C2 & _). pose proof (u64_range sp).
    rewrite gh_cp_outside; [apply gh_m2_outside; exact Hy | rewrite Z2Nat.id by lia; lia | rewrite Z2Nat.id by lia; exact Hx].
  Qed.
  Lemma gh_m4_outside : forall x : word, (U x < U chp \/ U chp + 4 * n <= U x)%Z -> (U x < RIz + 16 \/ RIz + 24 <= U x)%Z ->
    (U x < RIz + 72 \/ RIz + 80 <= U x)%Z -> M4 x = MP x.
  Proof using Hchp HRI HSPB Hn Hc Hsp sp.
    intros x Hx Hy Hz. destruct HSPB as (S1 & S2 & S3). (lazymatch goal with |- ?G => let G' := eval unfold gh_m4 in G in change_no_check G' end).
    destruct Hz as [Hz|Hz]; [rewrite wbytes_below | rewrite wbytes_above]; wd_lenlit; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; try lia;
      apply gh_cpn_outside; assumption.
  Qed.
  Lemma gh_m4_grows : mem_grows MP M4.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold gh_m4 in G in change_no_check G' end). eapply mem_grows_trans; [|apply wbytes_grows]. eapply mem_grows_trans; [apply wbytes_grows | apply gh_cp_grows]. Qed.

  (* [comment removed for export] *)
  Lemma gh_stats : forall regs : bvmap 5 word,
    getr regs 8 = Z_to_bv 64 RIz -> getr regs 14 = Z_to_bv 64 n ->
    exists r, msteps ASEGS (mkst regs (0x50c54 : word) (CP (Z.to_nat n)) rom) (mkst r (0x50c64 : word) M4 rom)
      /\ getr r 9 = Z_to_bv 64 1 /\ regs_agree (fun i : reg => In i [9; 11]) regs r.
  Proof using SOK_RI R_st Hchp HRI HSPB Hn Hc Hsp sp.
    intros regs H8 H14. pose proof (u64_range sp) as Hspr. pose proof (u64_range chp) as Hchr.
    destruct HSPB as (S1 & S2 & S3). destruct HRI as [RI1 RI2]. destruct Hn as (N1 & N2 & N3). destruct Hchp as (C1 & C2 & _).
    assert (Rst3 : rdn ASEGS (CP (Z.to_nat n)) (Z_to_bv 64 (RIz + 72)) 8 = Some (LE8 stv)).
    { rewrite <- R_st. apply rdn_ext; [first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite u_Z2bv in Hx by lia. cbn in Hx.
      apply gh_cpn_outside; lia. }
    assert (SOK3 : store_ok ASEGS (CP (Z.to_nat n)) (Z_to_bv 64 (RIz + 72)) 8 = true).
    { eapply store_ok_mono; [eapply mem_grows_trans; [apply wbytes_grows | apply gh_cp_grows]|].
      eapply (store_ok_sub ASEGS MP (Z_to_bv 64 RIz) _ 128); [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | exact SOK_RI | first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite !u_Z2bv by lia; lia ] | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite !u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. }
    wd_eexists. split.
    - chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 stv) (v := stv);
          [exact F_50c4c | reflexivity | exact D_50c4c | gres; rwH; imm_norm; (lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; exact Rst3 | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                               (* [comment removed for export] *)
      an F_50c50 D_50c50.                                (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_sd_at with (a := Z_to_bv 64 (RIz + 72));
          [exact F_50c54 | reflexivity | exact D_50c54
          | gres; rwH; imm_norm; (lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; reflexivity
          | gres; rwH; reflexivity
          | exact SOK3 ]
        | step_simpl]; vn.                               (* [comment removed for export] *)
      change (wbytes (CP (Z.to_nat n)) _ _) with M4.
      an F_50c58 D_50c58.                                (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.

  (* [comment removed for export] *)
  Hypothesis S_ra : rdn ASEGS MP (at_ sp (-8)) 8 = Some (LE8 ra).
  Hypothesis S_s0 : rdn ASEGS MP (at_ sp (-16)) 8 = Some (LE8 s0v).
  Hypothesis S_s1 : rdn ASEGS MP (at_ sp (-24)) 8 = Some (LE8 s1v).
  Hypothesis S_s2 : rdn ASEGS MP (at_ sp (-32)) 8 = Some (LE8 s2v).
  Hypothesis S_s3 : rdn ASEGS MP (at_ sp (-40)) 8 = Some (LE8 s3v).
  Hypothesis S_s4 : rdn ASEGS MP (at_ sp (-48)) 8 = Some (LE8 s4v).
  Hypothesis S_s5 : rdn ASEGS MP (at_ sp (-56)) 8 = Some (LE8 s5v).
  Hypothesis S_s6 : rdn ASEGS MP (at_ sp (-64)) 8 = Some (LE8 s6v).
  Hypothesis S_s7 : rdn ASEGS MP (at_ sp (-72)) 8 = Some (LE8 s7v).
  Hypothesis S_s8 : rdn ASEGS MP (at_ sp (-80)) 8 = Some (LE8 s8v).
  Hypothesis S_s9 : rdn ASEGS MP (at_ sp (-88)) 8 = Some (LE8 s9v).
  Hypothesis S_s10 : rdn ASEGS MP (at_ sp (-96)) 8 = Some (LE8 s10v).
  Hypothesis S_s11 : rdn ASEGS MP (at_ sp (-104)) 8 = Some (LE8 s11v).

  Theorem gfp_ok : forall regs : bvmap 5 word, gfp_regs sp chp RIz SPB c n regs -> getr regs 10 = Z_to_bv 64 1 ->
    exists r, msteps ASEGS (mkst regs (0x50d88 : word) MP rom) (mkst r ra (gh_m5 MP chp stv faf RIz nf2 n) rom)
      /\ gfp_post sp ra s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v 1 regs r.
  Proof using S_s11 S_s10 S_s9 S_s8 S_s7 S_s6 S_s5 S_s4 S_s3 S_s2 S_s1 S_s0 S_ra Hfaf SOK_ch SOK_RI R_msk R_mtx R_st R_nf Hchp HRI HSPB Hn Hc Hret Hsp msk.
    intros regs HR H10. pose proof (u64_range sp) as Hspr. pose proof (u64_range chp) as Hchr.
    destruct HSPB as (S1 & S2 & S3). destruct HRI as [RI1 RI2]. destruct Hn as (N1 & N2 & N3). destruct Hchp as (C1 & C2 & _).
    destruct (gh_head regs HR H10) as (r1 & RUN1 & A2 & A8 & A19 & A13 & A20 & A11 & A14 & AG1).
    destruct (gh_loop (Z.to_nat n) 0%nat r1 ltac:(rewrite Z2Nat.id by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) ltac:(rewrite Z2Nat.id by lia; lia)
                ltac:(rewrite A13; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat] in G in change_no_check G' end); rewrite Z.mul_0_r, at_0; reflexivity)
                ltac:(rewrite A20; f_equal; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) A11) as (r2 & RUN2 & K2).
    assert (NI : forall x : reg, In x [2%bv; 8%bv; 14%bv; 19%bv] -> ~ In x [12%bv; 13%bv; 20%bv] : Prop).
    { intros x Hin Hx. cbn [In] in Hin, Hx.
      destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; destruct Hx as [E|[E|[E|[]]]]; discriminate E. }
    destruct (gh_stats r2 ltac:(rewrite K2 by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto); exact A8) ltac:(rewrite K2 by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto); exact A14))
      as (r3 & RUN3 & B9 & AG3).
    (* [comment removed for export] *)
    assert (TR : forall (a : word) (k : nat) bs, (U a + Z.of_nat k <= 2 ^ 64)%Z ->
               (U a + Z.of_nat k <= U chp \/ U chp + 4 * n <= U a)%Z -> (U a + Z.of_nat k <= RIz + 16 \/ RIz + 24 <= U a)%Z ->
               (U a + Z.of_nat k <= RIz + 72 \/ RIz + 80 <= U a)%Z ->
               rdn ASEGS MP a k = Some bs -> rdn ASEGS M4 a k = Some bs).
    { intros a k bs Hk X1 X2 X3 R. rewrite <- R. apply rdn_ext; [exact Hk|]. intros x Hx. apply gh_m4_outside; lia. }
    Ltac trs TR H := apply TR; [first [rewrite at_u by lia | rewrite u_Z2bv by lia]; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia
                               | first [rewrite at_u by lia | rewrite u_Z2bv by lia]; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia
                               | first [rewrite at_u by lia | rewrite u_Z2bv by lia]; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia
                               | first [rewrite at_u by lia | rewrite u_Z2bv by lia]; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia
                               | exact H].
    assert (RI8 : (RIz mod 8 = 0)%Z) by (clear - S3 Hc; Z.div_mod_to_equations; lia).
    destruct (gfp_tail M4 rom sp ra s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v msk RIz 1 Hsp Hret
                ltac:(lia) ltac:(trs TR R_mtx) ltac:(trs TR R_msk)
                ltac:(eapply store_ok_mono; [apply gh_m4_grows|];
                      eapply (store_ok_sub ASEGS MP (Z_to_bv 64 RIz) _ 128); [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | exact SOK_RI | first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite !u_Z2bv by lia; lia ] | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite !u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]])
                ltac:(trs TR S_ra) ltac:(trs TR S_s0) ltac:(trs TR S_s1) ltac:(trs TR S_s2) ltac:(trs TR S_s3) ltac:(trs TR S_s4)
                ltac:(trs TR S_s5) ltac:(trs TR S_s6) ltac:(trs TR S_s7) ltac:(trs TR S_s8) ltac:(trs TR S_s9) ltac:(trs TR S_s10) ltac:(trs TR S_s11)
                r3
                ltac:(rewrite (AG3 2%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros [E|[E|[]]]; discriminate E); rewrite K2 by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto); exact A2)
                ltac:(rewrite (AG3 8%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros [E|[E|[]]]; discriminate E); rewrite K2 by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto); exact A8)
                B9
                ltac:(rewrite (AG3 19%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros [E|[E|[]]]; discriminate E); rewrite K2 by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto); exact A19))
      as (r4 & RUN4 & P4).
    exists r4. split.
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|]. exact RUN4.
    - unfold gfp_post in *. destruct P4 as (B10 & B2 & B1 & B8 & B9' & B18 & B19 & B20 & B21 & B22 & B23 & B24 & B25 & B26 & B27 & AG4).
      repeat (split; [assumption|]).
      intros x Hx. rewrite (AG4 x Hx).
      rewrite (AG3 x) by (intros Hin; apply Hx; clear - Hin; cbn [In] in *; tauto).
      rewrite K2 by (intros Hin; apply Hx; clear - Hin; cbn [In] in *; tauto).
      apply AG1. intros Hin; apply Hx; clear - Hin; cbn [In] in *; tauto.
  Qed.
End OK.
End FPGen.
End AsAllocM8h.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM7i OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2.AsAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA.AsAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM7i.AsAllocM7 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b.AsAllocM8m AsAllocM8g AsAllocM8h.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation U := bv_unsigned.


Definition r1_mem (M : word -> option byte) (spR raR s0R s1R g_ra g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 : word) (RIz : Z) : word -> option byte :=
  gfp_m1 (wbytes (wbytes (wbytes M (at_ spR (-8)) (LE8 raR)) (at_ spR (-16)) (LE8 s0R)) (at_ spR (-24)) (LE8 s1R))
         (at_ spR (-32)) g_ra g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 RIz.

Section R1MEM.
  Variables (segs : list Segment) (M : word -> option byte) (spR raR s0R s1R g_ra g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 : word) (RIz : Z).
  Hypothesis Hsp : 4096 <= U spR /\ U spR < 2 ^ 63.
  Hypothesis HRI : 0 <= RIz /\ RIz + 8 <= U spR - 160.
  #[local] Abbreviation M1 := (r1_mem M spR raR s0R s1R g_ra g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 RIz).
  #[local] Abbreviation MR := (wbytes (wbytes (wbytes M (at_ spR (-8)) (LE8 raR)) (at_ spR (-16)) (LE8 s0R)) (at_ spR (-24)) (LE8 s1R)).
  #[local] Abbreviation spG := (at_ spR (-32)).

  Lemma r1_frame_outside : forall x : word, (U x < U spR - 160 \/ U spR - 32 <= U x) ->
    gfp_frame MR spG g_ra g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 x = MR x.
  Proof using Hsp.
    intros x Hx. destruct Hsp as [S1 S2]. (lazymatch goal with |- ?G => let G' := eval unfold gfp_frame in G in change_no_check G' end).
    repeat (rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite length_N_to_le_bytes, !at_u by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ]); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia
                                               | rewrite length_N_to_le_bytes, !at_u by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ]); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
    reflexivity.
  Qed.
  Lemma r1_mem_outside : forall x : word, (U x < U spR - 160 \/ U spR <= U x) -> (U x < RIz \/ RIz + 8 <= U x) -> M1 x = M x.
  Proof using HRI Hsp.
    intros x X1 X2. destruct Hsp as [S1 S2]. destruct HRI as [R0 R1]. (lazymatch goal with |- ?G => let G' := eval unfold r1_mem, gfp_m1 in G in change_no_check G' end).
    rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite length_N_to_le_bytes, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
    rewrite r1_frame_outside by lia.
    repeat (rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
    reflexivity.
  Qed.
  Lemma r1_mem_grows : mem_grows M M1.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold r1_mem, gfp_m1, gfp_frame in G in change_no_check G' end). repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
  Lemma r1_mem_mrestrict : forall Hd : word -> bool, hid_off Hd (U spR - 160) 160 -> hid_off Hd RIz 8 ->
    r1_mem (mrestrict Hd M) spR raR s0R s1R g_ra g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 RIz = mrestrict Hd M1.
  Proof using HRI Hsp.
    intros Hd O1 O2. destruct Hsp as [S1 S2]. destruct HRI as [R0 R1]. (lazymatch goal with |- ?G => let G' := eval unfold r1_mem, gfp_m1, gfp_frame in G in change_no_check G' end).
    rewrite !wbytes_mrestrict; [reflexivity | ..];
      wd_lenlit; rewrite ?length_N_to_le_bytes, ?u_Z2bv, ?at_u by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ]); (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end);
      first [lia | intros x Hx; apply O1; lia | intros x Hx; apply O2; lia].
  Qed.
  Lemma r1_mem_lock : rdn segs M1 (Z_to_bv 64 RIz) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 60))).
  Proof using HRI Hsp. destruct HRI as [R0 R1]. destruct Hsp as [S1 S2]. (lazymatch goal with |- ?G => let G' := eval unfold r1_mem, gfp_m1 in G in change_no_check G' end). apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia. Qed.
  Lemma r1_mem_gslots : forall (k : Z) (v : word),
    In (k, v) [(-8, g_ra); (-16, g0); (-24, g1); (-32, g2); (-40, g3); (-48, g4); (-56, g5); (-64, g6); (-72, g7); (-80, g8); (-88, g9); (-96, g10); (-104, g11)] ->
    rdn segs M1 (at_ spG k) 8 = Some (LE8 v).
  Proof using HRI Hsp.
    intros k v Hin. destruct Hsp as [S1 S2]. destruct HRI as [R0 R1].
    assert (K : -104 <= k <= -8) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
    (lazymatch goal with |- ?G => let G' := eval unfold r1_mem, gfp_m1 in G in change_no_check G' end).
    rewrite rdn_wbytes_out; [ | rewrite length_N_to_le_bytes, u_Z2bv, !at_u by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ]); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia
                              | rewrite !at_u by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ]); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
    (lazymatch goal with |- ?G => let G' := eval unfold gfp_frame in G in change_no_check G' end). cbn [In] in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; rd8_chain|]). destruct Hin.
  Qed.
  Lemma r1_mem_rslots : forall (k : Z) (v : word), In (k, v) [(-8, raR); (-16, s0R); (-24, s1R)] -> rdn segs M1 (at_ spR k) 8 = Some (LE8 v).
  Proof using HRI Hsp.
    intros k v Hin. destruct Hsp as [S1 S2]. destruct HRI as [R0 R1].
    assert (K : -24 <= k <= -8) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
    rewrite (rdn_ext segs 8 M1 MR (at_ spR k)); [ | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | ].
    - cbn [In] in Hin. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; rd8_chain|]). destruct Hin.
    - intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. (lazymatch goal with |- ?G => let G' := eval unfold r1_mem, gfp_m1 in G in change_no_check G' end).
      rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite length_N_to_le_bytes, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      apply r1_frame_outside. lia.
  Qed.
End R1MEM.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
Definition r2_mem (MP : word -> option byte) (pc stv : word) (faf : Z -> Z) (RIz nf2 n : Z) : word -> option byte :=
  wbytes (gh_m5 MP (at_ pc 16) stv faf RIz nf2 n) pc (LE4 n).

Lemma gh_cp_mrestrict : forall (Hd : word -> bool) M2 (chp : word) faf lo i, U chp + 4 * Z.of_nat i < 2 ^ 64 ->
  hid_off Hd (U chp) (4 * Z.of_nat i) -> gh_cp (mrestrict Hd M2) chp faf lo i = mrestrict Hd (gh_cp M2 chp faf lo i).
Proof.
  induction i as [|i IH]; intros Hn Hh; [reflexivity|]. (lazymatch goal with |- ?G => let G' := eval cbn [gh_cp] in G in change_no_check G' end). pose proof (u64_range chp).
  rewrite IH by (first [lia | eapply hid_off_sub; [exact Hh | lia | lia]]).
  apply wbytes_mrestrict; rewrite length_N_to_le_bytes, at_u by lia; [lia | eapply hid_off_sub; [exact Hh | lia | lia]].
Qed.
Lemma gh_cp_entry : forall segs M2 (chp : word) faf lo (n i : nat), (i < n)%nat -> U chp + 4 * Z.of_nat n < 2 ^ 64 ->
  rdn segs (gh_cp M2 chp faf lo n) (at_ chp (4 * Z.of_nat i)) 4 = Some (LE4 (faf (lo + Z.of_nat i))).
Proof.
  intros segs M2 chp faf lo n. induction n as [|n IH]; intros i Hi Hn; [lia|]. (lazymatch goal with |- ?G => let G' := eval cbn [gh_cp] in G in change_no_check G' end). pose proof (u64_range chp).
  destruct (Nat.eq_dec i n) as [->|NE].
  - apply rdn_wbytes_hit4. rewrite at_u by lia. lia.
  - rewrite rdn_wbytes_out; [apply IH; lia | rewrite length_N_to_le_bytes, !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]
                            | rewrite length_N_to_le_bytes, at_u by lia; lia].
Qed.

Section R2MEM.
  Variables (segs : list Segment) (MP : word -> option byte) (pc stv : word) (faf : Z -> Z) (RIz nf2 n : Z).
  Hypothesis Hn : 1 <= n <= 8.
  Hypothesis Hpc : 0 <= U pc /\ U pc + 80 < 2 ^ 63.
  Hypothesis HRI : 0 <= RIz /\ RIz + 128 < 2 ^ 63.
  Hypothesis HD : U pc + 80 <= RIz \/ RIz + 128 <= U pc.
  #[local] Abbreviation M2 := (r2_mem MP pc stv faf RIz nf2 n).

  Lemma r2_mem_outside : forall x : word, (U x < U pc \/ U pc + 4 <= U x) -> (U x < U pc + 16 \/ U pc + 16 + 4 * n <= U x) ->
    (U x < RIz \/ RIz + 8 <= U x) -> (U x < RIz + 16 \/ RIz + 24 <= U x) -> (U x < RIz + 72 \/ RIz + 80 <= U x) -> M2 x = MP x.
  Proof using HD HRI Hpc Hn.
    intros x X1 X2 X3 X4 X5. destruct Hpc as [P0 P1]. destruct HRI as [R0 R1]. (lazymatch goal with |- ?G => let G' := eval unfold r2_mem, gh_m5, gh_m4, gh_m2 in G in change_no_check G' end).
    rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
    rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite length_N_to_le_bytes, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
    rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite length_N_to_le_bytes, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
    rewrite gh_cp_outside; [ | rewrite at_u by lia; rewrite Z2Nat.id by lia; lia | rewrite at_u by lia; rewrite Z2Nat.id by lia; lia].
    apply MemsetLibF.MemSplit.wbytes_outside; [rewrite length_N_to_le_bytes, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
  Qed.
  Lemma r2_mem_grows : mem_grows MP M2.
  Proof using.
    (lazymatch goal with |- ?G => let G' := eval unfold r2_mem, gh_m5, gh_m4, gh_m2 in G in change_no_check G' end). do 3 (eapply mem_grows_trans; [| apply wbytes_grows]).
    eapply mem_grows_trans; [apply wbytes_grows | apply gh_cp_grows].
  Qed.
  Lemma r2_mem_mrestrict : forall Hd : word -> bool, hid_off Hd (U pc) 80 -> hid_off Hd RIz 128 ->
    r2_mem (mrestrict Hd MP) pc stv faf RIz nf2 n = mrestrict Hd M2.
  Proof using HRI Hpc Hn.
    intros Hd O1 O2. destruct Hpc as [P0 P1]. destruct HRI as [R0 R1]. (lazymatch goal with |- ?G => let G' := eval unfold r2_mem, gh_m5, gh_m4, gh_m2 in G in change_no_check G' end).
    rewrite (wbytes_mrestrict Hd _ MP (Z_to_bv 64 (RIz + 16))) by (rewrite length_N_to_le_bytes, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [lia | eapply hid_off_sub; [exact O2 | lia | lia]]).
    rewrite gh_cp_mrestrict by (rewrite at_u by lia; rewrite Z2Nat.id by lia; first [lia | eapply hid_off_sub; [exact O1 | lia | lia]]).
    rewrite !wbytes_mrestrict; [reflexivity | ..]; wd_lenlit; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end);
      first [lia | eapply hid_off_sub; [exact O2 | lia | lia] | eapply hid_off_sub; [exact O1 | lia | lia]].
  Qed.
  Lemma r2_mem_rd : 
    rdn segs M2 pc 4 = Some (LE4 n)
    /\ rdn segs M2 (Z_to_bv 64 RIz) 8 = Some (LE8 (Z_to_bv 64 0))
    /\ rdn segs M2 (Z_to_bv 64 (RIz + 16)) 8 = Some (LE8 (Z_to_bv 64 (nf2 - n)))
    /\ (forall i : nat, Z.of_nat i < n -> rdn segs M2 (at_ pc (16 + 4 * Z.of_nat i)) 4 = Some (LE4 (faf (nf2 - n + Z.of_nat i)))).
  Proof using HD HRI Hpc Hn.
    destruct Hpc as [P0 P1]. destruct HRI as [R0 R1]. (lazymatch goal with |- ?G => let G' := eval unfold r2_mem, gh_m5, gh_m4, gh_m2 in G in change_no_check G' end).
    Ltac peel2 := rewrite rdn_wbytes_out; [ | rewrite length_N_to_le_bytes, ?u_Z2bv, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite ?u_Z2bv, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia
                                            | rewrite length_N_to_le_bytes, ?u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
    split; [|split; [|split]].
    - apply rdn_wbytes_hit4. lia.
    - peel2. apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia.
    - peel2. peel2. peel2.
      rewrite (rdn_ext segs 8 _ (wbytes MP (Z_to_bv 64 (RIz + 16)) (LE8 (Z_to_bv 64 (nf2 - n)))) (Z_to_bv 64 (RIz + 16)));
        [apply rdn_wbytes_hit8; first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] |].
      intros x Hx. rewrite u_Z2bv in Hx by lia. cbn in Hx. apply gh_cp_outside; rewrite at_u by lia; rewrite Z2Nat.id by lia; lia.
    - intros i Hi. peel2. peel2. peel2.
      replace (at_ pc (16 + 4 * Z.of_nat i)) with (at_ (at_ pc 16) (4 * Z.of_nat i)) by (apply bv_eq; rewrite !at_u by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ]); lia).
      apply gh_cp_entry; [lia | rewrite at_u by lia; rewrite Z2Nat.id by lia; lia].
  Qed.
End R2MEM.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition r10_mem (regs : bvmap 5 word) (M : word -> option byte) (spR raR cache g_ra g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 : word) (RIz : Z) : word -> option byte :=
  gfp_m1 (ic_mem regs M raR spR cache 31) (at_ spR (-32)) g_ra g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 RIz.

Lemma ic_mem_mrestrict : forall (Hd : word -> bool) regs M (raR spR cache : word) (k : nat), 32 <= U spR -> U spR < 2 ^ 63 -> U cache + 4096 < 2 ^ 63 -> (Z.of_nat k <= 31) ->
  hid_off Hd (U spR - 32) 32 -> hid_off Hd (U cache) 2560 ->
  ic_mem regs (mrestrict Hd M) raR spR cache k = mrestrict Hd (ic_mem regs M raR spR cache k).
Proof.
  intros Hd regs M raR spR cache k S0 S1 C1. induction k as [|k IH]; intros Hk O1 O2.
  - (lazymatch goal with |- ?G => let G' := eval cbn [ic_mem] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold rf_m1 in G in change_no_check G' end). rewrite !wbytes_mrestrict; [reflexivity | ..];
      wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); first [lia | eapply hid_off_sub; [exact O1 | lia | lia]].
  - (lazymatch goal with |- ?G => let G' := eval cbn [ic_mem] in G in change_no_check G' end). rewrite IH by (first [lia | assumption]). pose proof (u64_range cache).
    rewrite !wbytes_mrestrict; [reflexivity | ..];
      wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [length Pos.to_nat] in G in change_no_check G' end); first [lia | eapply hid_off_sub; [exact O2 | lia | lia]].
Qed.

(* [comment removed for export] *)
Lemma ic_mem_outside_p : forall regs M (raR spR cache : word) (k : nat) (x : word), U cache + 4096 < 2 ^ 63 -> (Z.of_nat k <= 31) ->
  (forall i : Z, 1 <= i <= Z.of_nat k -> (U x < U cache + 80 * i + 4 \/ U cache + 80 * i + 16 <= U x)) ->
  ic_mem regs M raR spR cache k x = rf_m1 regs M raR spR x.
Proof.
  intros regs M raR spR cache k x C1. induction k as [|k IH]; intros Hk Hx; [reflexivity|]. (lazymatch goal with |- ?G => let G' := eval cbn [ic_mem] in G in change_no_check G' end). pose proof (u64_range cache).
  pose proof (Hx (Z.of_nat (S k)) ltac:(lia)) as Hk1.
  rewrite MemsetLibF.MemSplit.wbytes_outside; [| rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
  rewrite MemsetLibF.MemSplit.wbytes_outside; [| rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
  apply IH; [lia|]. intros i Hi. apply Hx. lia.
Qed.
Lemma ic_mem_mc_p : forall segs regs M (raR spR cache : word) (k : nat) c0, U cache + 4096 < 2 ^ 63 -> 1 <= c0 <= Z.of_nat k -> Z.of_nat k <= 31 ->
  rdn segs (ic_mem regs M raR spR cache k) (at_ cache (80 * c0 + 4)) 4 = Some (LE4 (icmc c0)).
Proof.
  intros segs regs M raR spR cache k c0 C1. revert c0. induction k as [|k IH]; intros c0 Hc Hk; [lia|]. (lazymatch goal with |- ?G => let G' := eval cbn [ic_mem] in G in change_no_check G' end). pose proof (u64_range cache).
  rewrite rdn_wbytes_out; [ | rewrite length_N_to_le_bytes, !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ].
  destruct (Z.eq_dec c0 (Z.of_nat (S k))) as [->|NE].
  - apply rdn_wbytes_hit4. rewrite at_u by lia. lia.
  - rewrite rdn_wbytes_out; [ | rewrite length_N_to_le_bytes, !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ].
    apply IH; lia.
Qed.
Lemma ic_mem_cs_p : forall segs regs M (raR spR cache : word) (k : nat) c0, U cache + 4096 < 2 ^ 63 -> 1 <= c0 <= Z.of_nat k -> Z.of_nat k <= 31 ->
  rdn segs (ic_mem regs M raR spR cache k) (at_ cache (80 * c0 + 8)) 8 = Some (LE8 (Z_to_bv 64 (iccs c0))).
Proof.
  intros segs regs M raR spR cache k c0 C1. revert c0. induction k as [|k IH]; intros c0 Hc Hk; [lia|]. (lazymatch goal with |- ?G => let G' := eval cbn [ic_mem] in G in change_no_check G' end). pose proof (u64_range cache).
  destruct (Z.eq_dec c0 (Z.of_nat (S k))) as [->|NE].
  - apply rdn_wbytes_hit8. rewrite at_u by lia. lia.
  - rewrite rdn_wbytes_out; [ | rewrite length_N_to_le_bytes, !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ].
    rewrite rdn_wbytes_out; [ | rewrite length_N_to_le_bytes, !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ].
    apply IH; lia.
Qed.

Section R10MEM.
  Variables (segs : list Segment) (regs : bvmap 5 word) (M : word -> option byte) (spR raR cache g_ra g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 : word) (RIz : Z).
  Hypothesis Hsp : 2 ^ 32 + 4096 <= U spR /\ U spR + 16 <= 2 ^ 47.
  Hypothesis HRI : 0 <= RIz /\ RIz + 8 <= U spR - 160.
  Hypothesis Hcache : 0 <= U cache /\ U cache + 2640 <= U spR - 160.
  Hypothesis HD : U cache + 2640 <= RIz \/ RIz + 8 <= U cache.
  #[local] Abbreviation M1 := (r10_mem regs M spR raR cache g_ra g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 RIz).
  #[local] Abbreviation MI := (ic_mem regs M raR spR cache 31).
  #[local] Abbreviation spG := (at_ spR (-32)).

  Lemma r10_frame_outside : forall x : word, (U x < U spR - 160 \/ U spR - 32 <= U x) ->
    gfp_frame MI spG g_ra g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 x = MI x.
  Proof using Hsp.
    intros x Hx. destruct Hsp as [S1 S2]. (lazymatch goal with |- ?G => let G' := eval unfold gfp_frame in G in change_no_check G' end).
    repeat (rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite length_N_to_le_bytes, !at_u by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ]); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia
                                               | rewrite length_N_to_le_bytes, !at_u by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ]); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
    reflexivity.
  Qed.
  Lemma r10_mem_above : forall x : word, (U x < U spR - 160 \/ U spR - 32 <= U x) -> (U x < RIz \/ RIz + 8 <= U x) -> M1 x = MI x.
  Proof using HRI Hsp.
    intros x X1 X2. destruct Hsp as [S1 S2]. destruct HRI as [R0 R1]. (lazymatch goal with |- ?G => let G' := eval unfold r10_mem, gfp_m1 in G in change_no_check G' end).
    rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite length_N_to_le_bytes, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
    apply r10_frame_outside. exact X1.
  Qed.
  Lemma r10_mem_grows : mem_grows M M1.
  Proof using.
    (lazymatch goal with |- ?G => let G' := eval unfold r10_mem, gfp_m1, gfp_frame in G in change_no_check G' end). do 14 (eapply mem_grows_trans; [|apply wbytes_grows]). apply ic_mem_grows.
  Qed.
  Lemma r10_mem_mrestrict : forall Hd : word -> bool, hid_off Hd (U spR - 160) 160 -> hid_off Hd RIz 8 -> hid_off Hd (U cache) 2560 ->
    r10_mem regs (mrestrict Hd M) spR raR cache g_ra g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 RIz = mrestrict Hd M1.
  Proof using Hcache HRI Hsp.
    intros Hd O1 O2 O3. destruct Hsp as [S1 S2]. destruct HRI as [R0 R1]. destruct Hcache as [C0 C1]. (lazymatch goal with |- ?G => let G' := eval unfold r10_mem in G in change_no_check G' end).
    rewrite ic_mem_mrestrict by (first [lia | eapply hid_off_sub; [exact O1 | lia | lia] | exact O3]).
    (lazymatch goal with |- ?G => let G' := eval unfold gfp_m1, gfp_frame in G in change_no_check G' end).
    rewrite !wbytes_mrestrict; [reflexivity | ..];
      wd_lenlit; rewrite ?length_N_to_le_bytes, ?u_Z2bv, ?at_u by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ]); (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end);
      first [lia | intros x Hx; apply O1; lia | intros x Hx; apply O2; lia].
  Qed.
  Lemma r10_mem_lock : rdn segs M1 (Z_to_bv 64 RIz) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 60))).
  Proof using HRI Hsp. destruct HRI as [R0 R1]. destruct Hsp as [S1 S2]. (lazymatch goal with |- ?G => let G' := eval unfold r10_mem, gfp_m1 in G in change_no_check G' end). apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia. Qed.
  Lemma r10_mem_gslots : forall (k : Z) (v : word),
    In (k, v) [(-8, g_ra); (-16, g0); (-24, g1); (-32, g2); (-40, g3); (-48, g4); (-56, g5); (-64, g6); (-72, g7); (-80, g8); (-88, g9); (-96, g10); (-104, g11)] ->
    rdn segs M1 (at_ spG k) 8 = Some (LE8 v).
  Proof using Hcache HRI Hsp.
    intros k v Hin. destruct Hsp as [S1 S2]. destruct HRI as [R0 R1].
    assert (K : -104 <= k <= -8) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
    (lazymatch goal with |- ?G => let G' := eval unfold r10_mem, gfp_m1 in G in change_no_check G' end).
    rewrite rdn_wbytes_out; [ | rewrite length_N_to_le_bytes, u_Z2bv, !at_u by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ]); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia
                              | rewrite !at_u by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ]); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
    (lazymatch goal with |- ?G => let G' := eval unfold gfp_frame in G in change_no_check G' end). cbn [In] in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; rd8_chain|]). destruct Hin.
  Qed.
  Lemma r10_mem_outside : forall x : word, (U x < U spR - 160 \/ U spR <= U x) -> (U x < RIz \/ RIz + 8 <= U x) ->
    (forall i : Z, 1 <= i <= 31 -> (U x < U cache + 80 * i + 4 \/ U cache + 80 * i + 16 <= U x)) -> M1 x = M x.
  Proof using Hcache HRI Hsp.
    intros x X1 X2 X3. destruct Hsp as [S1 S2]. destruct Hcache as [C0 C1]. rewrite r10_mem_above by (first [lia | exact X2]).
    rewrite ic_mem_outside_p by (first [lia | exact X3]). (lazymatch goal with |- ?G => let G' := eval unfold rf_m1 in G in change_no_check G' end).
    repeat (rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
    reflexivity.
  Qed.
  Lemma r10_mem_rslots : forall (k : Z) (v : word), In (k, v) [(-8, raR); (-16, getr regs 8); (-24, getr regs 9)] -> rdn segs M1 (at_ spR k) 8 = Some (LE8 v).
  Proof using Hcache HRI Hsp.
    intros k v Hin. destruct Hsp as [S1 S2]. destruct HRI as [R0 R1]. destruct Hcache as [C0 C1].
    assert (K : -24 <= k <= -8) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
    rewrite (rdn_ext segs 8 M1 (rf_m1 regs M raR spR) (at_ spR k)); [ | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | ].
    - (lazymatch goal with |- ?G => let G' := eval unfold rf_m1 in G in change_no_check G' end). cbn [In] in Hin. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; rd8_chain|]). destruct Hin.
    - intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. rewrite r10_mem_above by lia. apply ic_mem_outside_p; [lia | lia |]. intros i Hi. lia.
  Qed.
  Lemma r10_mem_cells : forall i, 1 <= i <= 31 ->
    rdn segs M1 (at_ cache (80 * i + 4)) 4 = Some (LE4 (icmc i)) /\ rdn segs M1 (at_ cache (80 * i + 8)) 8 = Some (LE8 (Z_to_bv 64 (iccs i))).
  Proof using HD Hcache HRI Hsp.
    intros i Hi. destruct Hsp as [S1 S2]. destruct HRI as [R0 R1]. destruct Hcache as [C0 C1]. split.
    - rewrite (rdn_ext segs 4 M1 MI (at_ cache (80 * i + 4))); [apply ic_mem_mc_p; lia | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] |].
      intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply r10_mem_above; lia.
    - rewrite (rdn_ext segs 8 M1 MI (at_ cache (80 * i + 8))); [apply ic_mem_cs_p; lia | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] |].
      intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply r10_mem_above; lia.
  Qed.
End R10MEM.
