(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_50a9c_51a9c. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_50a9c_51a9c.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

Section FPGen1.
Context {fx : FPState}.

Definition cb_words : list (option (bv 32)) :=
  [Some W_50cec; Some W_50cf0; Some W_50cf4; Some W_50cf8; Some W_50cfc; Some W_50d00; Some W_50d04; Some W_50d08;
   Some W_50d0c; Some W_50d10; Some W_50d14; None; None; Some W_50d20; None; None; Some W_50d2c; Some W_50d30;
   Some W_50d34; Some W_50d38; Some W_50d3c; Some W_50d40; Some W_50d44; Some W_50d48; Some W_50d4c; Some W_50d50;
   Some W_50d54; Some W_50d58; Some W_50d5c; Some W_50d60; Some W_50d64; Some W_50d68; Some W_50d6c; Some W_50d70;
   Some W_50d74; Some W_50d78; Some W_50d7c; Some W_50d80; Some W_50d84; Some W_50d88; Some W_50d8c; Some W_50d90;
   Some W_50d94; Some W_50d98; Some W_50d9c; Some W_50da0; Some W_50da4; Some W_50da8; Some W_50dac; Some W_50db0;
   Some W_50db4; Some W_50db8; Some W_50dbc; Some W_50dc0; Some W_50dc4; Some W_50dc8; Some W_50dcc; Some W_50dd0;
   Some W_50dd4; Some W_50dd8; Some W_50ddc; Some W_50de0; Some W_50de4; Some W_50de8; Some W_50dec; Some W_50df0;
   Some W_50df4; Some W_50df8; Some W_50dfc; Some W_50e00; Some W_50e04; Some W_50e08; Some W_50e0c; Some W_50e10;
   Some W_50e14; Some W_50e18; Some W_50e1c; Some W_50e20; Some W_50e24; Some W_50e28; Some W_50e2c; Some W_50e30;
   Some W_50e34; Some W_50e38; Some W_50e3c; Some W_50e40; Some W_50e44; Some W_50e48; Some W_50e4c; Some W_50e50;
   Some W_50e54; Some W_50e58; Some W_50e5c; Some W_50e60; Some W_50e64; Some W_50e68; Some W_50e6c; Some W_50e70;
   Some W_50e74; Some W_50e78; Some W_50e7c; Some W_50e80; Some W_50e84; Some W_50e88; Some W_50e8c; Some W_50e90;
   Some W_50e94; Some W_50e98; Some W_50e9c; Some W_50ea0; Some W_50ea4; Some W_50ea8; Some W_50eac; Some W_50eb0;
   Some W_50eb4; Some W_50eb8; Some W_50ebc; Some W_50ec0; Some W_50ec4; Some W_50ec8; Some W_50ecc; Some W_50ed0;
   Some W_50ed4; Some W_50ed8; Some W_50edc; Some W_50ee0; Some W_50ee4; Some W_50ee8; Some W_50eec; Some W_50ef0;
   Some W_50ef4; Some W_50ef8; Some W_50efc; Some W_50f00; Some W_50f04; Some W_50f08; Some W_50f0c]%list.

(* [comment removed for export] *)
Definition cid_hi (s : word) : word :=
  let a2_1 := (v_srli s (1)) in (* [comment removed for export] *)
  let a5_1 := (Z_to_bv 64 1431654400) in (* [comment removed for export] *)
  let a6_1 := (Z_to_bv 64 858992640) in (* [comment removed for export] *)
  let a7_1 := (Z_to_bv 64 252645376) in (* [comment removed for export] *)
  let t0_1 := (Z_to_bv 64 16842752) in (* [comment removed for export] *)
  let a2_2 := (v_or s a2_1) in (* [comment removed for export] *)
  let a5_2 := (v_addiw a5_1 (1365)) in (* [comment removed for export] *)
  let a6_2 := (v_addiw a6_1 (819)) in (* [comment removed for export] *)
  let a7_2 := (v_addiw a7_1 (-241)) in (* [comment removed for export] *)
  let t0_2 := (v_addiw t0_1 (257)) in (* [comment removed for export] *)
  let t1_1 := (v_srli a2_2 (2)) in (* [comment removed for export] *)
  let a2_3 := (v_or a2_2 t1_1) in (* [comment removed for export] *)
  let t1_2 := (v_slli a5_2 (32)) in (* [comment removed for export] *)
  let a5_3 := (v_add a5_2 t1_2) in (* [comment removed for export] *)
  let t1_3 := (v_slli a6_2 (32)) in (* [comment removed for export] *)
  let a6_3 := (v_add a6_2 t1_3) in (* [comment removed for export] *)
  let t1_4 := (v_slli a7_2 (32)) in (* [comment removed for export] *)
  let a7_3 := (v_add a7_2 t1_4) in (* [comment removed for export] *)
  let t1_5 := (v_slli t0_2 (32)) in (* [comment removed for export] *)
  let t0_3 := (v_add t0_2 t1_5) in (* [comment removed for export] *)
  let t1_6 := (v_srli a2_3 (4)) in (* [comment removed for export] *)
  let a2_4 := (v_or a2_3 t1_6) in (* [comment removed for export] *)
  let t1_7 := (v_srli a2_4 (8)) in (* [comment removed for export] *)
  let a2_5 := (v_or a2_4 t1_7) in (* [comment removed for export] *)
  let t1_8 := (v_srli a2_5 (16)) in (* [comment removed for export] *)
  let a2_6 := (v_or a2_5 t1_8) in (* [comment removed for export] *)
  let t1_9 := (v_srli a2_6 (32)) in (* [comment removed for export] *)
  let a2_7 := (v_or a2_6 t1_9) in (* [comment removed for export] *)
  let a2_8 := (v_xori a2_7 (-1)) in (* [comment removed for export] *)
  let t1_10 := (v_srli a2_8 (1)) in (* [comment removed for export] *)
  let a5_4 := (v_and t1_10 a5_3) in (* [comment removed for export] *)
  let a2_9 := (v_sub a2_8 a5_4) in (* [comment removed for export] *)
  let a5_5 := (v_and a2_9 a6_3) in (* [comment removed for export] *)
  let a2_10 := (v_srli a2_9 (2)) in (* [comment removed for export] *)
  let a2_11 := (v_and a2_10 a6_3) in (* [comment removed for export] *)
  let a2_12 := (v_add a5_5 a2_11) in (* [comment removed for export] *)
  let a5_6 := (v_srli a2_12 (4)) in (* [comment removed for export] *)
  let a2_13 := (v_add a2_12 a5_6) in (* [comment removed for export] *)
  let a5_7 := (Z_to_bv 64 62) in (* [comment removed for export] *)
  let a2_14 := (v_and a2_13 a7_3) in (* [comment removed for export] *)
  let a6_4 := (Z_to_bv 64 18446744073709551615) in (* [comment removed for export] *)
  let a2_15 := (v_mul a2_14 t0_3) in (* [comment removed for export] *)
  let a2_16 := (v_srli a2_15 (56)) in (* [comment removed for export] *)
  let a5_8 := (v_subw a5_7 a2_16) in (* [comment removed for export] *)
  let a2_17 := (v_slli a2_16 (1)) in (* [comment removed for export] *)
  let a7_4 := (v_srl s a5_8) in (* [comment removed for export] *)
  let a5_9 := (v_sllw a6_4 a5_8) in (* [comment removed for export] *)
  let a2_18 := (v_xori a2_17 (126)) in (* [comment removed for export] *)
  let a6_5 := (v_andi a7_4 (1)) in (* [comment removed for export] *)
  let a5_10 := (v_xori a5_9 (-1)) in (* [comment removed for export] *)
  let a4_1 := (v_and s a5_10) in (* [comment removed for export] *)
  let a2_19 := (v_or a2_18 a6_5) in (* [comment removed for export] *)
  let a4_2 := (v_sltu (Z_to_bv 64 0) a4_1) in (* [comment removed for export] *)
  let a2_20 := (v_add a2_19 a4_2) in (* [comment removed for export] *)
  let s0_1 := (v_addi a2_20 (-2)) in (* [comment removed for export] *)
  s0_1.

(* [comment removed for export] *)
Definition cidv_a2_1 (s : word) : word := (v_srli s (1)). (* [comment removed for export] *)
Definition cidv_a5_1 (s : word) : word := (Z_to_bv 64 1431654400). (* [comment removed for export] *)
Definition cidv_a6_1 (s : word) : word := (Z_to_bv 64 858992640). (* [comment removed for export] *)
Definition cidv_a7_1 (s : word) : word := (Z_to_bv 64 252645376). (* [comment removed for export] *)
Definition cidv_t0_1 (s : word) : word := (Z_to_bv 64 16842752). (* [comment removed for export] *)
Definition cidv_a2_2 (s : word) : word := (v_or s (cidv_a2_1 s)). (* [comment removed for export] *)
Definition cidv_a5_2 (s : word) : word := (v_addiw (cidv_a5_1 s) (1365)). (* [comment removed for export] *)
Definition cidv_a6_2 (s : word) : word := (v_addiw (cidv_a6_1 s) (819)). (* [comment removed for export] *)
Definition cidv_a7_2 (s : word) : word := (v_addiw (cidv_a7_1 s) (-241)). (* [comment removed for export] *)
Definition cidv_t0_2 (s : word) : word := (v_addiw (cidv_t0_1 s) (257)). (* [comment removed for export] *)
Definition cidv_t1_1 (s : word) : word := (v_srli (cidv_a2_2 s) (2)). (* [comment removed for export] *)
Definition cidv_a2_3 (s : word) : word := (v_or (cidv_a2_2 s) (cidv_t1_1 s)). (* [comment removed for export] *)
Definition cidv_t1_2 (s : word) : word := (v_slli (cidv_a5_2 s) (32)). (* [comment removed for export] *)
Definition cidv_a5_3 (s : word) : word := (v_add (cidv_a5_2 s) (cidv_t1_2 s)). (* [comment removed for export] *)
Definition cidv_t1_3 (s : word) : word := (v_slli (cidv_a6_2 s) (32)). (* [comment removed for export] *)
Definition cidv_a6_3 (s : word) : word := (v_add (cidv_a6_2 s) (cidv_t1_3 s)). (* [comment removed for export] *)
Definition cidv_t1_4 (s : word) : word := (v_slli (cidv_a7_2 s) (32)). (* [comment removed for export] *)
Definition cidv_a7_3 (s : word) : word := (v_add (cidv_a7_2 s) (cidv_t1_4 s)). (* [comment removed for export] *)
Definition cidv_t1_5 (s : word) : word := (v_slli (cidv_t0_2 s) (32)). (* [comment removed for export] *)
Definition cidv_t0_3 (s : word) : word := (v_add (cidv_t0_2 s) (cidv_t1_5 s)). (* [comment removed for export] *)
Definition cidv_t1_6 (s : word) : word := (v_srli (cidv_a2_3 s) (4)). (* [comment removed for export] *)
Definition cidv_a2_4 (s : word) : word := (v_or (cidv_a2_3 s) (cidv_t1_6 s)). (* [comment removed for export] *)
Definition cidv_t1_7 (s : word) : word := (v_srli (cidv_a2_4 s) (8)). (* [comment removed for export] *)
Definition cidv_a2_5 (s : word) : word := (v_or (cidv_a2_4 s) (cidv_t1_7 s)). (* [comment removed for export] *)
Definition cidv_t1_8 (s : word) : word := (v_srli (cidv_a2_5 s) (16)). (* [comment removed for export] *)
Definition cidv_a2_6 (s : word) : word := (v_or (cidv_a2_5 s) (cidv_t1_8 s)). (* [comment removed for export] *)
Definition cidv_t1_9 (s : word) : word := (v_srli (cidv_a2_6 s) (32)). (* [comment removed for export] *)
Definition cidv_a2_7 (s : word) : word := (v_or (cidv_a2_6 s) (cidv_t1_9 s)). (* [comment removed for export] *)
Definition cidv_a2_8 (s : word) : word := (v_xori (cidv_a2_7 s) (-1)). (* [comment removed for export] *)
Definition cidv_t1_10 (s : word) : word := (v_srli (cidv_a2_8 s) (1)). (* [comment removed for export] *)
Definition cidv_a5_4 (s : word) : word := (v_and (cidv_t1_10 s) (cidv_a5_3 s)). (* [comment removed for export] *)
Definition cidv_a2_9 (s : word) : word := (v_sub (cidv_a2_8 s) (cidv_a5_4 s)). (* [comment removed for export] *)
Definition cidv_a5_5 (s : word) : word := (v_and (cidv_a2_9 s) (cidv_a6_3 s)). (* [comment removed for export] *)
Definition cidv_a2_10 (s : word) : word := (v_srli (cidv_a2_9 s) (2)). (* [comment removed for export] *)
Definition cidv_a2_11 (s : word) : word := (v_and (cidv_a2_10 s) (cidv_a6_3 s)). (* [comment removed for export] *)
Definition cidv_a2_12 (s : word) : word := (v_add (cidv_a5_5 s) (cidv_a2_11 s)). (* [comment removed for export] *)
Definition cidv_a5_6 (s : word) : word := (v_srli (cidv_a2_12 s) (4)). (* [comment removed for export] *)
Definition cidv_a2_13 (s : word) : word := (v_add (cidv_a2_12 s) (cidv_a5_6 s)). (* [comment removed for export] *)
Definition cidv_a5_7 (s : word) : word := (Z_to_bv 64 62). (* [comment removed for export] *)
Definition cidv_a2_14 (s : word) : word := (v_and (cidv_a2_13 s) (cidv_a7_3 s)). (* [comment removed for export] *)
Definition cidv_a6_4 (s : word) : word := (Z_to_bv 64 18446744073709551615). (* [comment removed for export] *)
Definition cidv_a2_15 (s : word) : word := (v_mul (cidv_a2_14 s) (cidv_t0_3 s)). (* [comment removed for export] *)
Definition cidv_a2_16 (s : word) : word := (v_srli (cidv_a2_15 s) (56)). (* [comment removed for export] *)
Definition cidv_a5_8 (s : word) : word := (v_subw (cidv_a5_7 s) (cidv_a2_16 s)). (* [comment removed for export] *)
Definition cidv_a2_17 (s : word) : word := (v_slli (cidv_a2_16 s) (1)). (* [comment removed for export] *)
Definition cidv_a7_4 (s : word) : word := (v_srl s (cidv_a5_8 s)). (* [comment removed for export] *)
Definition cidv_a5_9 (s : word) : word := (v_sllw (cidv_a6_4 s) (cidv_a5_8 s)). (* [comment removed for export] *)
Definition cidv_a2_18 (s : word) : word := (v_xori (cidv_a2_17 s) (126)). (* [comment removed for export] *)
Definition cidv_a6_5 (s : word) : word := (v_andi (cidv_a7_4 s) (1)). (* [comment removed for export] *)
Definition cidv_a5_10 (s : word) : word := (v_xori (cidv_a5_9 s) (-1)). (* [comment removed for export] *)
Definition cidv_a4_1 (s : word) : word := (v_and s (cidv_a5_10 s)). (* [comment removed for export] *)
Definition cidv_a2_19 (s : word) : word := (v_or (cidv_a2_18 s) (cidv_a6_5 s)). (* [comment removed for export] *)
Definition cidv_a4_2 (s : word) : word := (v_sltu (Z_to_bv 64 0) (cidv_a4_1 s)). (* [comment removed for export] *)
Definition cidv_a2_20 (s : word) : word := (v_add (cidv_a2_19 s) (cidv_a4_2 s)). (* [comment removed for export] *)
Definition cidv_s0_1 (s : word) : word := (v_addi (cidv_a2_20 s) (-2)). (* [comment removed for export] *)
Lemma cid_hi_cidv : forall s, cid_hi s = cidv_s0_1 s.
Proof. reflexivity. Qed.


Fixpoint cid_check (k : nat) (s : Z) : bool :=
  match k with
  | O => true
  | S k' => andb (Z.eqb (bv_unsigned (cid_hi (Z_to_bv 64 s))) (class_of s)) (cid_check k' (s + 8)%Z)
  end.
Lemma cid_check_ok : forall k s0, cid_check k s0 = true ->
  forall s, (s0 <= s < s0 + 8 * Z.of_nat k)%Z -> ((s - s0) mod 8 = 0)%Z -> bv_unsigned (cid_hi (Z_to_bv 64 s)) = class_of s.
Proof using.
  induction k as [|k IH]; intros s0 Hc s Hs Hm; [cbn [Z.of_nat] in Hs; lia|].
  cbn [cid_check] in Hc. apply andb_prop in Hc. destruct Hc as [H1 H2].
  destruct (Z.eq_dec s s0) as [->|NE]; [apply Z.eqb_eq; exact H1|].
  apply (IH (s0 + 8)%Z H2); [rewrite Nat2Z.inj_succ in Hs|].
  - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
  - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
Definition wd_zw (z : Z) : Z := Z.land z 18446744073709551615.
Definition wd_sw32 (z : Z) : Z := (Z.land (z + 2147483648) 4294967295 - 2147483648)%Z.
Lemma wd_uzw : forall z, bv_unsigned (Z_to_bv 64 z) = wd_zw z.
Proof. intros z. rewrite Z_to_bv_unsigned. (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap, bv_modulus, wd_zw in G in change_no_check G' end). change (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z.
  change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma wd_sw32_ok : forall z, bv_swrap 32 z = wd_sw32 z.
Proof. intros z. (lazymatch goal with |- ?G => let G' := eval unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus, wd_sw32 in G in change_no_check G' end). change (2 ^ Z.of_N 32 / 2)%Z with 2147483648%Z.
  change (2 ^ Z.of_N 32)%Z with (2 ^ 32)%Z. change 4294967295%Z with (Z.ones 32). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma wd_mod64 : forall z, (z mod 64 = Z.land z 63)%Z.
Proof. intros z. change 63%Z with (Z.ones 6). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma wd_mod32 : forall z, (z mod 32 = Z.land z 31)%Z.
Proof. intros z. change 31%Z with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma wd_let_sim : forall (v : word) (w : Z) (P : word -> word) (Q : Z -> Z),
  (forall a b, bv_unsigned a = b -> bv_unsigned (P a) = Q b) -> bv_unsigned v = w -> bv_unsigned (let a := v in P a) = (let b := w in Q b).
Proof. intros v w P Q H1 H2. exact (H1 v w H2). Qed.
Ltac wd_let_walk :=
  repeat (lazymatch goal with
          | |- bv_unsigned (let x := ?v in @?P x) = (let y := ?w in @?Q y) =>
              refine (wd_let_sim v w P Q _ _); [ let a := fresh "a" in let b := fresh "b" in let H := fresh "H" in intros a b H; cbv beta | ]
          end).
Ltac wd_cz_op :=
  subst;
  lazymatch goal with
  | |- bv_unsigned (v_sltu _ _) = _ =>
      (lazymatch goal with |- ?G => let G' := eval unfold v_sltu, c_ltu, bv_ltu in G in change_no_check G' end); change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; destruct (0 <? _)%Z; reflexivity
  | _ => (lazymatch goal with |- ?G => let G' := eval unfold v_srli, v_or, v_addiw, v_slli, v_add, v_xori, v_and, v_sub, v_mul, v_subw, v_srl, v_sllw, v_andi, v_addi in G in change_no_check G' end);
         rewrite wd_uzw; rewrite ?wd_sw32_ok, ?wd_mod32, ?wd_mod64; reflexivity
  end.
Definition czhi (s : Z) : Z :=
  let a2_1 := (wd_zw (Z.shiftr s 1))%Z in
  let a5_1 := (wd_zw 1431654400)%Z in
  let a6_1 := (wd_zw 858992640)%Z in
  let a7_1 := (wd_zw 252645376)%Z in
  let t0_1 := (wd_zw 16842752)%Z in
  let a2_2 := (wd_zw (Z.lor s a2_1))%Z in
  let a5_2 := (wd_zw (wd_sw32 (a5_1 + 1365)))%Z in
  let a6_2 := (wd_zw (wd_sw32 (a6_1 + 819)))%Z in
  let a7_2 := (wd_zw (wd_sw32 (a7_1 + (-241))))%Z in
  let t0_2 := (wd_zw (wd_sw32 (t0_1 + 257)))%Z in
  let t1_1 := (wd_zw (Z.shiftr a2_2 2))%Z in
  let a2_3 := (wd_zw (Z.lor a2_2 t1_1))%Z in
  let t1_2 := (wd_zw (Z.shiftl a5_2 32))%Z in
  let a5_3 := (wd_zw (a5_2 + t1_2))%Z in
  let t1_3 := (wd_zw (Z.shiftl a6_2 32))%Z in
  let a6_3 := (wd_zw (a6_2 + t1_3))%Z in
  let t1_4 := (wd_zw (Z.shiftl a7_2 32))%Z in
  let a7_3 := (wd_zw (a7_2 + t1_4))%Z in
  let t1_5 := (wd_zw (Z.shiftl t0_2 32))%Z in
  let t0_3 := (wd_zw (t0_2 + t1_5))%Z in
  let t1_6 := (wd_zw (Z.shiftr a2_3 4))%Z in
  let a2_4 := (wd_zw (Z.lor a2_3 t1_6))%Z in
  let t1_7 := (wd_zw (Z.shiftr a2_4 8))%Z in
  let a2_5 := (wd_zw (Z.lor a2_4 t1_7))%Z in
  let t1_8 := (wd_zw (Z.shiftr a2_5 16))%Z in
  let a2_6 := (wd_zw (Z.lor a2_5 t1_8))%Z in
  let t1_9 := (wd_zw (Z.shiftr a2_6 32))%Z in
  let a2_7 := (wd_zw (Z.lor a2_6 t1_9))%Z in
  let a2_8 := (wd_zw (Z.lxor a2_7 18446744073709551615))%Z in
  let t1_10 := (wd_zw (Z.shiftr a2_8 1))%Z in
  let a5_4 := (wd_zw (Z.land t1_10 a5_3))%Z in
  let a2_9 := (wd_zw (a2_8 - a5_4))%Z in
  let a5_5 := (wd_zw (Z.land a2_9 a6_3))%Z in
  let a2_10 := (wd_zw (Z.shiftr a2_9 2))%Z in
  let a2_11 := (wd_zw (Z.land a2_10 a6_3))%Z in
  let a2_12 := (wd_zw (a5_5 + a2_11))%Z in
  let a5_6 := (wd_zw (Z.shiftr a2_12 4))%Z in
  let a2_13 := (wd_zw (a2_12 + a5_6))%Z in
  let a5_7 := (wd_zw 62)%Z in
  let a2_14 := (wd_zw (Z.land a2_13 a7_3))%Z in
  let a6_4 := (wd_zw 18446744073709551615)%Z in
  let a2_15 := (wd_zw (a2_14 * t0_3))%Z in
  let a2_16 := (wd_zw (Z.shiftr a2_15 56))%Z in
  let a5_8 := (wd_zw (wd_sw32 (a5_7 - a2_16)))%Z in
  let a2_17 := (wd_zw (Z.shiftl a2_16 1))%Z in
  let a7_4 := (wd_zw (Z.shiftr s (Z.land a5_8 63)))%Z in
  let a5_9 := (wd_zw (wd_sw32 (Z.shiftl a6_4 (Z.land a5_8 31))))%Z in
  let a2_18 := (wd_zw (Z.lxor a2_17 126))%Z in
  let a6_5 := (wd_zw (Z.land a7_4 1))%Z in
  let a5_10 := (wd_zw (Z.lxor a5_9 18446744073709551615))%Z in
  let a4_1 := (wd_zw (Z.land s a5_10))%Z in
  let a2_19 := (wd_zw (Z.lor a2_18 a6_5))%Z in
  let a4_2 := (if 0 <? a4_1 then 1 else 0)%Z in
  let a2_20 := (wd_zw (a2_19 + a4_2))%Z in
  let s0_1 := (wd_zw (a2_20 + (-2)))%Z in
  s0_1.
Lemma czhi_ok : forall x, bv_unsigned (cid_hi x) = czhi (bv_unsigned x).
Proof. intros x. cbv beta delta [cid_hi czhi]. wd_let_walk. all: first [ assumption | wd_cz_op ]. Qed.
Fixpoint cid_check_z (k : nat) (s : Z) : bool :=
  match k with
  | O => true
  | S k' => andb (Z.eqb (czhi s) (class_of s)) (cid_check_z k' (s + 8)%Z)
  end.
Lemma cid_check_z_ok : forall k s, (0 <= s)%Z -> (s + 8 * Z.of_nat k <= 2 ^ 64)%Z -> cid_check_z k s = cid_check k s.
Proof.
  induction k as [|k IH]; intros s H1 H2; [reflexivity|]. rewrite Nat2Z.inj_succ in H2. (lazymatch goal with |- ?G => let G' := eval cbn [cid_check_z cid_check] in G in change_no_check G' end).
  rewrite czhi_ok, (u_Z2bv s) by lia. rewrite IH by lia. reflexivity.
Qed.
Local Set Warnings "-abstract-large-number".
Lemma cid_check_all : cid_check 8128 520 = true.
Proof using. rewrite <- (cid_check_z_ok 8128 520) by (apply Z.leb_le; vm_compute; reflexivity). vm_cast_no_check (@eq_refl bool true). Qed.
Lemma class_of_range_hi : forall s, (512 < s)%Z -> (17 <= class_of s <= 30)%Z.
Proof using. intros s Hs. (lazymatch goal with |- ?G => let G' := eval unfold class_of in G in change_no_check G' end). destruct (Z.leb_spec s 512); [lia|]. repeat (destruct (Z.leb _ _)); lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma cid_hi_ok : forall s, (512 < s <= 65536)%Z -> (s mod 8 = 0)%Z -> cid_hi (Z_to_bv 64 s) = Z_to_bv 64 (class_of s).
Proof using.
  intros s Hs Hm. pose proof (class_of_range_hi s ltac:(lia)). apply bv_eq. rewrite (cid_check_ok 8128 520 cid_check_all s).
  - symmetry. apply u_Z2bv; lia.
  - change (520 + 8 * Z.of_nat 8128)%Z with 65544%Z. lia.
  - lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition cb_clob : list reg := [5; 6; 10; 11; 12; 14; 15; 16; 17].

Section CB.
  Variable segs : list Segment.
  Variable rb : word.
  Hypothesis HCB : code_ato segs rb 0x50cec cb_words.
  Hypothesis RB : (U rb mod 2 = 0)%Z /\ (U rb + 2 ^ 24 < 2 ^ 64)%Z.

  Lemma I6c568 : fetch_word segs (at_ rb 0x50cec) = Some W_50cec.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 0 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c56c : fetch_word segs (at_ rb 0x50cf0) = Some W_50cf0.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 1 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c570 : fetch_word segs (at_ rb 0x50cf4) = Some W_50cf4.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 2 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c574 : fetch_word segs (at_ rb 0x50cf8) = Some W_50cf8.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 3 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c578 : fetch_word segs (at_ rb 0x50cfc) = Some W_50cfc.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 4 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c57c : fetch_word segs (at_ rb 0x50d00) = Some W_50d00.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 5 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c580 : fetch_word segs (at_ rb 0x50d04) = Some W_50d04.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 6 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c584 : fetch_word segs (at_ rb 0x50d08) = Some W_50d08.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 7 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c588 : fetch_word segs (at_ rb 0x50d0c) = Some W_50d0c.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 8 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c58c : fetch_word segs (at_ rb 0x50d10) = Some W_50d10.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 9 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c590 : fetch_word segs (at_ rb 0x50d14) = Some W_50d14.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 10 _ HCB eq_refl). Qed.



   (* [comment removed for export] *)
  Lemma I6c5b4 : fetch_word segs (at_ rb 0x50d38) = Some W_50d38.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 19 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c5b8 : fetch_word segs (at_ rb 0x50d3c) = Some W_50d3c.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 20 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c5bc : fetch_word segs (at_ rb 0x50d40) = Some W_50d40.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 21 _ HCB eq_refl). Qed.






   (* [comment removed for export] *)
  Lemma I6c5dc : fetch_word segs (at_ rb 0x50d60) = Some W_50d60.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 29 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c5e0 : fetch_word segs (at_ rb 0x50d64) = Some W_50d64.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 30 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c5e4 : fetch_word segs (at_ rb 0x50d68) = Some W_50d68.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 31 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c5e8 : fetch_word segs (at_ rb 0x50d6c) = Some W_50d6c.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 32 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c5ec : fetch_word segs (at_ rb 0x50d70) = Some W_50d70.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 33 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c5f0 : fetch_word segs (at_ rb 0x50d74) = Some W_50d74.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 34 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c5f4 : fetch_word segs (at_ rb 0x50d78) = Some W_50d78.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 35 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c5f8 : fetch_word segs (at_ rb 0x50d7c) = Some W_50d7c.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 36 _ HCB eq_refl). Qed.








   (* [comment removed for export] *)
  Lemma I6c620 : fetch_word segs (at_ rb 0x50da4) = Some W_50da4.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 46 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c624 : fetch_word segs (at_ rb 0x50da8) = Some W_50da8.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 47 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c628 : fetch_word segs (at_ rb 0x50dac) = Some W_50dac.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 48 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c62c : fetch_word segs (at_ rb 0x50db0) = Some W_50db0.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 49 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c630 : fetch_word segs (at_ rb 0x50db4) = Some W_50db4.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 50 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c634 : fetch_word segs (at_ rb 0x50db8) = Some W_50db8.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 51 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c638 : fetch_word segs (at_ rb 0x50dbc) = Some W_50dbc.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 52 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c63c : fetch_word segs (at_ rb 0x50dc0) = Some W_50dc0.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 53 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c640 : fetch_word segs (at_ rb 0x50dc4) = Some W_50dc4.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 54 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c644 : fetch_word segs (at_ rb 0x50dc8) = Some W_50dc8.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 55 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c648 : fetch_word segs (at_ rb 0x50dcc) = Some W_50dcc.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 56 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c64c : fetch_word segs (at_ rb 0x50dd0) = Some W_50dd0.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 57 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c650 : fetch_word segs (at_ rb 0x50dd4) = Some W_50dd4.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 58 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c654 : fetch_word segs (at_ rb 0x50dd8) = Some W_50dd8.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 59 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c658 : fetch_word segs (at_ rb 0x50ddc) = Some W_50ddc.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 60 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c65c : fetch_word segs (at_ rb 0x50de0) = Some W_50de0.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 61 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c660 : fetch_word segs (at_ rb 0x50de4) = Some W_50de4.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 62 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c664 : fetch_word segs (at_ rb 0x50de8) = Some W_50de8.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 63 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c668 : fetch_word segs (at_ rb 0x50dec) = Some W_50dec.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 64 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c66c : fetch_word segs (at_ rb 0x50df0) = Some W_50df0.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 65 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c670 : fetch_word segs (at_ rb 0x50df4) = Some W_50df4.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 66 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c674 : fetch_word segs (at_ rb 0x50df8) = Some W_50df8.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 67 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c678 : fetch_word segs (at_ rb 0x50dfc) = Some W_50dfc.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 68 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c67c : fetch_word segs (at_ rb 0x50e00) = Some W_50e00.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 69 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c680 : fetch_word segs (at_ rb 0x50e04) = Some W_50e04.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 70 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c684 : fetch_word segs (at_ rb 0x50e08) = Some W_50e08.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 71 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c688 : fetch_word segs (at_ rb 0x50e0c) = Some W_50e0c.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 72 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c68c : fetch_word segs (at_ rb 0x50e10) = Some W_50e10.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 73 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c690 : fetch_word segs (at_ rb 0x50e14) = Some W_50e14.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 74 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c694 : fetch_word segs (at_ rb 0x50e18) = Some W_50e18.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 75 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c698 : fetch_word segs (at_ rb 0x50e1c) = Some W_50e1c.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 76 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c69c : fetch_word segs (at_ rb 0x50e20) = Some W_50e20.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 77 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c6a0 : fetch_word segs (at_ rb 0x50e24) = Some W_50e24.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 78 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c6a4 : fetch_word segs (at_ rb 0x50e28) = Some W_50e28.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 79 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c6a8 : fetch_word segs (at_ rb 0x50e2c) = Some W_50e2c.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 80 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c6ac : fetch_word segs (at_ rb 0x50e30) = Some W_50e30.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 81 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c6b0 : fetch_word segs (at_ rb 0x50e34) = Some W_50e34.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 82 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c6b4 : fetch_word segs (at_ rb 0x50e38) = Some W_50e38.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 83 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c6b8 : fetch_word segs (at_ rb 0x50e3c) = Some W_50e3c.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 84 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c6bc : fetch_word segs (at_ rb 0x50e40) = Some W_50e40.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 85 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c6c0 : fetch_word segs (at_ rb 0x50e44) = Some W_50e44.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 86 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c6c4 : fetch_word segs (at_ rb 0x50e48) = Some W_50e48.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 87 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c6c8 : fetch_word segs (at_ rb 0x50e4c) = Some W_50e4c.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 88 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c6cc : fetch_word segs (at_ rb 0x50e50) = Some W_50e50.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 89 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c6d0 : fetch_word segs (at_ rb 0x50e54) = Some W_50e54.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 90 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c6d4 : fetch_word segs (at_ rb 0x50e58) = Some W_50e58.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 91 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c6d8 : fetch_word segs (at_ rb 0x50e5c) = Some W_50e5c.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 92 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c6dc : fetch_word segs (at_ rb 0x50e60) = Some W_50e60.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 93 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c6e0 : fetch_word segs (at_ rb 0x50e64) = Some W_50e64.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 94 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c6e4 : fetch_word segs (at_ rb 0x50e68) = Some W_50e68.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 95 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c6e8 : fetch_word segs (at_ rb 0x50e6c) = Some W_50e6c.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 96 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c6ec : fetch_word segs (at_ rb 0x50e70) = Some W_50e70.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 97 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c6f0 : fetch_word segs (at_ rb 0x50e74) = Some W_50e74.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 98 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c6f4 : fetch_word segs (at_ rb 0x50e78) = Some W_50e78.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 99 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c6f8 : fetch_word segs (at_ rb 0x50e7c) = Some W_50e7c.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 100 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c6fc : fetch_word segs (at_ rb 0x50e80) = Some W_50e80.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 101 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c700 : fetch_word segs (at_ rb 0x50e84) = Some W_50e84.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 102 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c704 : fetch_word segs (at_ rb 0x50e88) = Some W_50e88.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 103 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c708 : fetch_word segs (at_ rb 0x50e8c) = Some W_50e8c.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 104 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c70c : fetch_word segs (at_ rb 0x50e90) = Some W_50e90.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 105 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c710 : fetch_word segs (at_ rb 0x50e94) = Some W_50e94.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 106 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c714 : fetch_word segs (at_ rb 0x50e98) = Some W_50e98.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 107 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c718 : fetch_word segs (at_ rb 0x50e9c) = Some W_50e9c.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 108 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c71c : fetch_word segs (at_ rb 0x50ea0) = Some W_50ea0.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 109 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c720 : fetch_word segs (at_ rb 0x50ea4) = Some W_50ea4.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 110 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c724 : fetch_word segs (at_ rb 0x50ea8) = Some W_50ea8.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 111 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c728 : fetch_word segs (at_ rb 0x50eac) = Some W_50eac.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 112 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c72c : fetch_word segs (at_ rb 0x50eb0) = Some W_50eb0.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 113 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c730 : fetch_word segs (at_ rb 0x50eb4) = Some W_50eb4.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 114 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c734 : fetch_word segs (at_ rb 0x50eb8) = Some W_50eb8.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 115 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c738 : fetch_word segs (at_ rb 0x50ebc) = Some W_50ebc.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 116 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c73c : fetch_word segs (at_ rb 0x50ec0) = Some W_50ec0.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 117 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c740 : fetch_word segs (at_ rb 0x50ec4) = Some W_50ec4.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 118 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c744 : fetch_word segs (at_ rb 0x50ec8) = Some W_50ec8.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 119 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c748 : fetch_word segs (at_ rb 0x50ecc) = Some W_50ecc.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 120 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c74c : fetch_word segs (at_ rb 0x50ed0) = Some W_50ed0.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 121 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c750 : fetch_word segs (at_ rb 0x50ed4) = Some W_50ed4.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 122 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c754 : fetch_word segs (at_ rb 0x50ed8) = Some W_50ed8.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 123 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c758 : fetch_word segs (at_ rb 0x50edc) = Some W_50edc.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 124 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c75c : fetch_word segs (at_ rb 0x50ee0) = Some W_50ee0.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 125 _ HCB eq_refl). Qed.


   (* [comment removed for export] *)
  Lemma I6c76c : fetch_word segs (at_ rb 0x50ef0) = Some W_50ef0.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 129 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c770 : fetch_word segs (at_ rb 0x50ef4) = Some W_50ef4.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 130 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c774 : fetch_word segs (at_ rb 0x50ef8) = Some W_50ef8.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 131 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c778 : fetch_word segs (at_ rb 0x50efc) = Some W_50efc.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 132 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c77c : fetch_word segs (at_ rb 0x50f00) = Some W_50f00.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 133 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c780 : fetch_word segs (at_ rb 0x50f04) = Some W_50f04.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 134 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c784 : fetch_word segs (at_ rb 0x50f08) = Some W_50f08.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 135 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6c788 : fetch_word segs (at_ rb 0x50f0c) = Some W_50f0c.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 136 _ HCB eq_refl). Qed.   (* [comment removed for export] *)


  Variables (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ra sp cache inst : word) (s : Z).
  Hypothesis Hret : ret_ok ra.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H10 : getr regs 10 = inst.
  Hypothesis H11 : getr regs 11 = cache.
  Hypothesis H12 : getr regs 12 = Z_to_bv 64 s.
  Hypothesis H13 : getr regs 13 = Z_to_bv 64 8.
  Hypothesis Hs : (24 <= s <= 65536)%Z /\ (s mod 8 = 0)%Z.
  Hypothesis Hstk : store_ok segs mem (at_ sp (-48)) 48 = true.
  Hypothesis G1 : (2 ^ 32 + 48 <= U sp)%Z /\ (U sp + 16 <= 2 ^ 47)%Z.

  #[local] Abbreviation CLX := (fun r => In r (2 :: 8 :: cb_clob)).


  (* [comment removed for export] *)
  Definition cb_m1 : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
      (at_ sp (-8)) (LE8 ra)) (at_ sp (-16)) (LE8 (getr regs 8))) (at_ sp (-24)) (LE8 (getr regs 9)))
      (at_ sp (-32)) (LE8 (getr regs 18))) (at_ sp (-40)) (LE8 (getr regs 19))) (at_ sp (-48)) (LE8 (getr regs 20)).
  Lemma cb_m1_outside : forall x : word, (U x < U sp - 48 \/ U sp <= U x)%Z -> cb_m1 x = mem x.
  Proof using G1 s rb.
    intros x Hx. pose proof (u64_range sp). destruct G1 as [G1a G1b]. (lazymatch goal with |- ?G => let G' := eval unfold cb_m1 in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); try lia. reflexivity.
  Qed.
  Lemma cb_m1_grows : mem_grows mem cb_m1.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold cb_m1 in G in change_no_check G' end). do 6 (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
  Lemma cb_m1_slots : forall (k : Z) (v : word),
    In (k, v) [(-8, ra); (-16, getr regs 8); (-24, getr regs 9); (-32, getr regs 18); (-40, getr regs 19); (-48, getr regs 20)]%Z ->
    rdn segs cb_m1 (at_ sp k) 8 = Some (LE8 v).
  Proof using G1 s rb.
    intros k v Hin. pose proof (u64_range sp). destruct G1 as [G1a G1b]. (lazymatch goal with |- ?G => let G' := eval unfold cb_m1 in G in change_no_check G' end). cbn [In] in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; rd8_chain|]). destruct Hin.
  Qed.

  Ltac sokS Hs0 lo N :=
    repeat (eapply store_ok_mono; [apply wbytes_grows|]);
    eapply (store_ok_sub segs mem lo _ N); [rewrite at_u; lia | exact Hs0 | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia].
  Ltac fsd8 F D aa :=
    chain_step; [reflexivity
      | eapply step_sd_at with (a := aa);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
        | gres; rwH; reflexivity
        | sokS Hstk (at_ sp (-48)) 48%nat ]
      | step_simpl]; vn.
  (* [comment removed for export] *)
  Ltac vz := cbv delta [v_add v_addi v_mul v_slli v_srli v_sub] beta; rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia; unorm;
             first [reflexivity | f_equal; lia | apply bv_eq; wd_ulia].

  (* [comment removed for export] *)
  Lemma cbP :
    exists r,
      msteps segs (mkst regs (at_ rb 0x50cec) mem rom) (mkst r (at_ rb 0x50d70) cb_m1 rom)
      /\ getr r 2 = at_ sp (-48) /\ getr r 10 = inst /\ getr r 11 = cache /\ getr r 12 = Z_to_bv 64 512 /\ getr r 13 = Z_to_bv 64 8
      /\ getr r 14 = Z_to_bv 64 s /\ getr r 15 = Z_to_bv 64 65536
      /\ regs_agree CLX regs r.
  Proof using G1 Hstk Hs H13 H12 H11 H10 H2 H1 HCB.
    destruct G1 as [G1a G1b]. destruct Hs as [Hs1 Hs2]. pose proof (u64_range sp) as Hspr.
    wd_eexists. split.
    - an I6c568 D_50cec.                                   (* [comment removed for export] *)
      fsd8 I6c56c D_50cf0 (at_ sp (-8)).                   (* [comment removed for export] *)
      fsd8 I6c570 D_50cf4 (at_ sp (-16)).                  (* [comment removed for export] *)
      fsd8 I6c574 D_50cf8 (at_ sp (-24)).                  (* [comment removed for export] *)
      fsd8 I6c578 D_50cfc (at_ sp (-32)).                  (* [comment removed for export] *)
      fsd8 I6c57c D_50d00 (at_ sp (-40)).                  (* [comment removed for export] *)
      fsd8 I6c580 D_50d04 (at_ sp (-48)).                  (* [comment removed for export] *)
      change (wbytes _ _ _) with cb_m1.
      av I6c584 D_50d08 (Z_to_bv 64 0) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_sltiu in G in change_no_check G' end); unorm; change (bv_wrap 64 1) with 1%Z;
                                              replace (s <? 1)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).   (* [comment removed for export] *)
      an I6c588 D_50d0c.                                   (* [comment removed for export] *)
      av I6c58c D_50d10 (Z_to_bv 64 (2 ^ 64 - 1 - s)) ltac:(rewrite v_not_word; f_equal; unorm; reflexivity).   (* [comment removed for export] *)
      ab_tk I6c590 D_50d14 ltac:(condz).                  (* [comment removed for export] *)
      an I6c5b4 D_50d38. an I6c5b8 D_50d3c.               (* [comment removed for export] *)
      ab_tk I6c5bc D_50d40 ltac:(condz).                  (* [comment removed for export] *)
      an I6c5dc D_50d60.                                   (* [comment removed for export] *)
      ab_ft I6c5e0 D_50d64 ltac:(condz).                  (* [comment removed for export] *)
      ab_ft I6c5e4 D_50d68 ltac:(condz).                  (* [comment removed for export] *)
      an I6c5e8 D_50d6c.                                   (* [comment removed for export] *)
      wd_refl.
    - post. (lazymatch goal with |- ?G => let G' := eval unfold cb_clob in G in change_no_check G' end). ra_solve.
  Qed.
  (* [comment removed for export] *)
  Lemma cbLo : forall (M : word -> option byte) r0,
    (s <= 512)%Z ->
    getr r0 12 = Z_to_bv 64 512 -> getr r0 14 = Z_to_bv 64 s -> regs_agree CLX regs r0 ->
    exists r, msteps segs (mkst r0 (at_ rb 0x50d70) M rom) (mkst r (at_ rb 0x50e80) M rom)
      /\ getr r 8 = Z_to_bv 64 (class_of s)
      /\ (forall i : reg, In i [2; 10; 11; 13] -> getr r i = getr r0 i)
      /\ regs_agree CLX regs r.
  Proof using Hs HCB.
    intros M r0 Hle R12 R14 AG0. destruct Hs as [Hs1 Hs2].
    wd_eexists. split.
    - ab_ft I6c5ec D_50d70 ltac:(condz).                  (* [comment removed for export] *)
      av I6c5f0 D_50d74 (Z_to_bv 64 (s + 31)) ltac:(vz).  (* [comment removed for export] *)
      av I6c5f4 D_50d78 (Z_to_bv 64 ((s + 31) / 32)) ltac:(vz).  (* [comment removed for export] *)
      an I6c5f8 D_50d7c.                                   (* [comment removed for export] *)
      wd_refl.
    - post.
      + (lazymatch goal with |- ?G => let G' := eval unfold class_of in G in change_no_check G' end). replace (s <=? 512)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
      + intros i Hi; cbn [In] in Hi; repeat (destruct Hi as [<-|Hi]; [gres; reflexivity|]); destruct Hi.
      + (lazymatch goal with |- ?G => let G' := eval unfold cb_clob in G in change_no_check G' end); ra_chain.
  Qed.

  (* [comment removed for export] *)
  Ltac setlast :=
    lazymatch goal with
    | |- msteps _ (mkst (regupd _ _ ?v) _ _ _) _ => first [is_var v | let t := fresh "w" in set (t := v)]
    | |- _ => idtac
    end.
  Ltac anl F D := stepi F D; gres; rwH; imm_norm; (lazymatch goal with |- ?G => let G' := eval unfold btgt in G in change_no_check G' end); rewrite ?at_addi; zlit_at; setlast.

  (* [comment removed for export] *)
  Fixpoint wc_upds (r : bvmap 5 word) (l : list (reg * word)) : bvmap 5 word :=
    match l with [] => r | p :: l' => regupd (wc_upds r l') (fst p) (snd p) end.
  Lemma wc_upds_keep : forall r l i, forallb (fun p => negb (bv_eqb i (fst p))) l = true -> getr (wc_upds r l) i = getr r i.
  Proof.
    intros r l i. induction l as [|p l IH]; intros wcH; [reflexivity|].
    cbn [forallb] in wcH. apply andb_prop in wcH. destruct wcH as [wcHa wcHb]. (lazymatch goal with |- ?G => let G' := eval cbn [wc_upds] in G in change_no_check G' end).
    rewrite getr_other; [exact (IH wcHb)|]. apply reg_neq_of_eqb. apply negb_true_iff in wcHa. exact wcHa.
  Qed.
  Ltac wc_reify X := lazymatch X with regupd ?Y ?rd ?v => let l := wc_reify Y in constr:((rd, v) :: l) | _ => constr:(@nil (reg * word)) end.
  Ltac wc_base X := lazymatch X with regupd ?Y _ _ => wc_base Y | _ => X end.
  Ltac wc_keep := lazymatch goal with |- getr ?X ?i = _ => let l := wc_reify X in let b := wc_base X in
      change X with (wc_upds b l); refine (eq_trans (wc_upds_keep b l i (eq_refl true)) _); reflexivity end.

  Ltac wc_foldlast c :=
    lazymatch goal with
    | |- msteps ?sg (mkst (regupd ?r ?rd ?v) ?pc ?mm ?rm) ?X =>
        change (msteps sg (mkst (regupd r rd v) pc mm rm) X) with (msteps sg (mkst (regupd r rd c) pc mm rm) X)
    end.
  Ltac anlc F D c := stepi F D; gres; rwH; imm_norm; (lazymatch goal with |- ?G => let G' := eval unfold btgt in G in change_no_check G' end); rewrite ?at_addi; zlit_at; first [wc_foldlast c | setlast].
  (* [comment removed for export] *)
  Lemma cbHi : forall (M : word -> option byte) r0,
    (512 < s)%Z ->
    getr r0 12 = Z_to_bv 64 512 -> getr r0 14 = Z_to_bv 64 s -> regs_agree CLX regs r0 ->
    exists r, msteps segs (mkst r0 (at_ rb 0x50d70) M rom) (mkst r (at_ rb 0x50e80) M rom)
      /\ getr r 8 = Z_to_bv 64 (class_of s)
      /\ (forall i : reg, In i [2; 10; 11; 13] -> getr r i = getr r0 i)
      /\ regs_agree CLX regs r.
  Proof using Hs HCB.
    intros M r0 Hgt R12 R14 AG0. destruct Hs as [Hs1 Hs2].
    wd_eexists. split.
    - ab_tk I6c5ec D_50d70 ltac:(condz).                  (* [comment removed for export] *)
      anlc I6c620 D_50da4 (cidv_a2_1 (Z_to_bv 64 s)).   (* [comment removed for export] *)
      anlc I6c624 D_50da8 (cidv_a5_1 (Z_to_bv 64 s)).   (* [comment removed for export] *)
      anlc I6c628 D_50dac (cidv_a6_1 (Z_to_bv 64 s)).   (* [comment removed for export] *)
      anlc I6c62c D_50db0 (cidv_a7_1 (Z_to_bv 64 s)).   (* [comment removed for export] *)
      anlc I6c630 D_50db4 (cidv_t0_1 (Z_to_bv 64 s)).   (* [comment removed for export] *)
      anlc I6c634 D_50db8 (cidv_a2_2 (Z_to_bv 64 s)).   (* [comment removed for export] *)
      anlc I6c638 D_50dbc (cidv_a5_2 (Z_to_bv 64 s)).   (* [comment removed for export] *)
      anlc I6c63c D_50dc0 (cidv_a6_2 (Z_to_bv 64 s)).   (* [comment removed for export] *)
      anlc I6c640 D_50dc4 (cidv_a7_2 (Z_to_bv 64 s)).   (* [comment removed for export] *)
      anlc I6c644 D_50dc8 (cidv_t0_2 (Z_to_bv 64 s)).   (* [comment removed for export] *)
      anlc I6c648 D_50dcc (cidv_t1_1 (Z_to_bv 64 s)).   (* [comment removed for export] *)
      anlc I6c64c D_50dd0 (cidv_a2_3 (Z_to_bv 64 s)).   (* [comment removed for export] *)
      anlc I6c650 D_50dd4 (cidv_t1_2 (Z_to_bv 64 s)).   (* [comment removed for export] *)
      anlc I6c654 D_50dd8 (cidv_a5_3 (Z_to_bv 64 s)).   (* [comment removed for export] *)
      anlc I6c658 D_50ddc (cidv_t1_3 (Z_to_bv 64 s)).   (* [comment removed for export] *)
      anlc I6c65c D_50de0 (cidv_a6_3 (Z_to_bv 64 s)).   (* [comment removed for export] *)
      anlc I6c660 D_50de4 (cidv_t1_4 (Z_to_bv 64 s)).   (* [comment removed for export] *)
      anlc I6c664 D_50de8 (cidv_a7_3 (Z_to_bv 64 s)).   (* [comment removed for export] *)
      anlc I6c668 D_50dec (cidv_t1_5 (Z_to_bv 64 s)).   (* [comment removed for export] *)
      anlc I6c66c D_50df0 (cidv_t0_3 (Z_to_bv 64 s)).   (* [comment removed for export] *)
      anlc I6c670 D_50df4 (cidv_t1_6 (Z_to_bv 64 s)).   (* [comment removed for export] *)
      anlc I6c674 D_50df8 (cidv_a2_4 (Z_to_bv 64 s)).   (* [comment removed for export] *)
      anlc I6c678 D_50dfc (cidv_t1_7 (Z_to_bv 64 s)).   (* [comment removed for export] *)
      anlc I6c67c D_50e00 (cidv_a2_5 (Z_to_bv 64 s)).   (* [comment removed for export] *)
      anlc I6c680 D_50e04 (cidv_t1_8 (Z_to_bv 64 s)).   (* [comment removed for export] *)
      anlc I6c684 D_50e08 (cidv_a2_6 (Z_to_bv 64 s)).   (* [comment removed for export] *)
      anlc I6c688 D_50e0c (cidv_t1_9 (Z_to_bv 64 s)).   (* [comment removed for export] *)
      anlc I6c68c D_50e10 (cidv_a2_7 (Z_to_bv 64 s)).   (* [comment removed for export] *)
      anlc I6c690 D_50e14 (cidv_a2_8 (Z_to_bv 64 s)).   (* [comment removed for export] *)
      anlc I6c694 D_50e18 (cidv_t1_10 (Z_to_bv 64 s)).   (* [comment removed for export] *)
      anlc I6c698 D_50e1c (cidv_a5_4 (Z_to_bv 64 s)).   (* [comment removed for export] *)
      anlc I6c69c D_50e20 (cidv_a2_9 (Z_to_bv 64 s)).   (* [comment removed for export] *)
      anlc I6c6a0 D_50e24 (cidv_a5_5 (Z_to_bv 64 s)).   (* [comment removed for export] *)
      anlc I6c6a4 D_50e28 (cidv_a2_10 (Z_to_bv 64 s)).   (* [comment removed for export] *)
      anlc I6c6a8 D_50e2c (cidv_a2_11 (Z_to_bv 64 s)).   (* [comment removed for export] *)
      anlc I6c6ac D_50e30 (cidv_a2_12 (Z_to_bv 64 s)).   (* [comment removed for export] *)
      anlc I6c6b0 D_50e34 (cidv_a5_6 (Z_to_bv 64 s)).   (* [comment removed for export] *)
      anlc I6c6b4 D_50e38 (cidv_a2_13 (Z_to_bv 64 s)).   (* [comment removed for export] *)
      anlc I6c6b8 D_50e3c (cidv_a5_7 (Z_to_bv 64 s)).   (* [comment removed for export] *)
      anlc I6c6bc D_50e40 (cidv_a2_14 (Z_to_bv 64 s)).   (* [comment removed for export] *)
      anlc I6c6c0 D_50e44 (cidv_a6_4 (Z_to_bv 64 s)).   (* [comment removed for export] *)
      anlc I6c6c4 D_50e48 (cidv_a2_15 (Z_to_bv 64 s)).   (* [comment removed for export] *)
      anlc I6c6c8 D_50e4c (cidv_a2_16 (Z_to_bv 64 s)).   (* [comment removed for export] *)
      anlc I6c6cc D_50e50 (cidv_a5_8 (Z_to_bv 64 s)).   (* [comment removed for export] *)
      anlc I6c6d0 D_50e54 (cidv_a2_17 (Z_to_bv 64 s)).   (* [comment removed for export] *)
      anlc I6c6d4 D_50e58 (cidv_a7_4 (Z_to_bv 64 s)).   (* [comment removed for export] *)
      anlc I6c6d8 D_50e5c (cidv_a5_9 (Z_to_bv 64 s)).   (* [comment removed for export] *)
      anlc I6c6dc D_50e60 (cidv_a2_18 (Z_to_bv 64 s)).   (* [comment removed for export] *)
      anlc I6c6e0 D_50e64 (cidv_a6_5 (Z_to_bv 64 s)).   (* [comment removed for export] *)
      anlc I6c6e4 D_50e68 (cidv_a5_10 (Z_to_bv 64 s)).   (* [comment removed for export] *)
      anlc I6c6e8 D_50e6c (cidv_a4_1 (Z_to_bv 64 s)).   (* [comment removed for export] *)
      anlc I6c6ec D_50e70 (cidv_a2_19 (Z_to_bv 64 s)).   (* [comment removed for export] *)
      anlc I6c6f0 D_50e74 (cidv_a4_2 (Z_to_bv 64 s)).   (* [comment removed for export] *)
      anlc I6c6f4 D_50e78 (cidv_a2_20 (Z_to_bv 64 s)).   (* [comment removed for export] *)
      anlc I6c6f8 D_50e7c (cidv_s0_1 (Z_to_bv 64 s)).   (* [comment removed for export] *)
      wd_refl.
    - split; [|split].
      + gres. rewrite <- (cid_hi_ok s) by lia. symmetry. apply cid_hi_cidv.
      + intros i Hi; cbn [In] in Hi; repeat (destruct Hi as [<-|Hi]; [wc_keep|]); destruct Hi.
      + (lazymatch goal with |- ?G => let G' := eval unfold cb_clob in G in change_no_check G' end); ra_chain.
  Qed.
  (* [comment removed for export] *)
  Definition cb_slots : list (Z * word) := [(-8, ra); (-16, getr regs 8); (-24, getr regs 9); (-32, getr regs 18); (-40, getr regs 19); (-48, getr regs 20)]%Z.
  Lemma cbB : forall (M : word -> option byte) r0 (c cnt k : Z) (csz stw sbeg : word),
    getr r0 8 = Z_to_bv 64 c -> getr r0 2 = at_ sp (-48) -> getr r0 10 = inst -> getr r0 11 = cache -> getr r0 13 = Z_to_bv 64 8 ->
    regs_agree CLX regs r0 ->
    (1 <= c <= 30)%Z -> (1 <= cnt <= 16)%Z -> (0 <= k < 2 ^ 32)%Z ->
    rdn segs M (at_ cache (80 * c)) 4 = Some (LE4 cnt) ->
    rdn segs M (at_ cache (80 * c + 8)) 8 = Some (LE8 csz) ->
    rdn segs M (at_ cache (80 * c + 16 + 4 * (cnt - 1))) 4 = Some (LE4 k) ->
    rdn segs M (at_ cache 2576) 8 = Some (LE8 stw) ->
    store_ok segs M (at_ cache (80 * c)) 4 = true -> store_ok segs M (at_ cache 2576) 8 = true ->
    rdn segs M (at_ inst 32) 8 = Some (LE8 sbeg) ->
    (forall (o : Z) (v : word), In (o, v) cb_slots -> rdn segs M (at_ sp o) 8 = Some (LE8 v)) ->
    (U cache mod 8 = 0)%Z -> (U inst + 40 <= U cache \/ U cache + 2584 <= U inst)%Z -> (U cache + 2584 <= U sp - 48)%Z -> (U inst + 40 <= 2 ^ 32)%Z ->
    (U sbeg + 2 ^ 37 < 2 ^ 64)%Z ->
    let M1 := wbytes M (at_ cache (80 * c)) (LE4 (cnt - 1)) in
    let M' := wbytes M1 (at_ cache 2576) (LE8 (v_add stw csz)) in
    exists r, msteps segs (mkst r0 (at_ rb 0x50e80) M rom) (mkst r ra M' rom)
      /\ getr r 10 = Z_to_bv 64 (U sbeg + c * 2 ^ 32 + 16 * k)
      /\ getr r 13 = Z_to_bv 64 8
      /\ (forall i : reg, In i [1; 2; 8; 9; 18; 19; 20] -> getr r i = getr regs i)
      /\ regs_agree CLX regs r.
  Proof using G1 H1 H10 H11 H12 H2 HCB Hret Hs RB.
    intros M r0 c cnt k csz stw sbeg R8 R2 R10 R11 R13 AG0 Hc Hcnt Hk Rcnt Rcsz Rk Rst SOKc SOKs Rsb FR AL8 Gc Gcs Gi Gsb M1 M'.
    destruct G1 as [G1a G1b]. pose proof (u64_range sp) as Hspr. pose proof (u64_range cache) as Hcr. pose proof (u64_range inst) as Hir.
    pose proof (u64_range sbeg) as Hsbr.
    assert (M1_out : forall x : word, (U x < U cache + 80 * c \/ U cache + 80 * c + 4 <= U x)%Z -> M1 x = M x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end). rewrite wbytes_outside; [reflexivity | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    assert (M'_out : forall x : word, (U x < U cache + 80 * c \/ U cache + 80 * c + 4 <= U x)%Z -> (U x < U cache + 2576 \/ U cache + 2584 <= U x)%Z -> M' x = M x).
    { intros x Hx Hy. (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). rewrite wbytes_outside; [apply M1_out; exact Hx | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    assert (Rcsz1 : rdn segs M1 (at_ cache (80 * c + 8)) 8 = Some (LE8 csz)).
    { rewrite <- Rcsz. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply M1_out; rewrite at_u in Hx by lia; cbn in Hx; lia]. }
    assert (Rk1 : rdn segs M1 (at_ cache (80 * c + 16 + 4 * (cnt - 1))) 4 = Some (LE4 k)).
    { rewrite <- Rk. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply M1_out; rewrite at_u in Hx by lia; cbn in Hx; lia]. }
    assert (Rst1 : rdn segs M1 (at_ cache 2576) 8 = Some (LE8 stw)).
    { rewrite <- Rst. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply M1_out; rewrite at_u in Hx by lia; cbn in Hx; lia]. }
    assert (SOKs1 : store_ok segs M1 (at_ cache 2576) 8 = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end). eapply store_ok_mono; [apply wbytes_grows | exact SOKs]. }
    assert (Rsb' : rdn segs M' (at_ inst 32) 8 = Some (LE8 sbeg)).
    { rewrite <- Rsb. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; rewrite at_u in Hx by lia; cbn in Hx; apply M'_out; lia]. }
    assert (FR' : forall (o : Z) (v : word), In (o, v) cb_slots -> rdn segs M' (at_ sp o) 8 = Some (LE8 v)).
    { intros o v Hin. rewrite <- (FR o v Hin).
      assert (Ho : (-48 <= o <= -8)%Z). { cbn [In cb_slots] in Hin. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin. }
      apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; rewrite at_u in Hx by lia; cbn in Hx; apply M'_out; lia]. }
    wd_eexists. split; [|split; [|split; [|split]]].
    - ab_ft I6c6fc D_50e80 ltac:(condz).                  (* [comment removed for export] *)
      an I6c700 D_50e84.                                   (* [comment removed for export] *)
      ab_ft I6c704 D_50e88 ltac:(condz).                  (* [comment removed for export] *)
      an I6c708 D_50e8c.                                   (* [comment removed for export] *)
      av I6c70c D_50e90 (Z_to_bv 64 (80 * c)) ltac:(vz).  (* [comment removed for export] *)
      av I6c710 D_50e94 (at_ cache (80 * c)) ltac:(rewrite v_add_at by lia; reflexivity).  (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lw with (bs := word_to_le_bytes 4 (Z_to_bv 64 cnt)) (v := Z_to_bv 64 cnt);
          [exact I6c714 | reflexivity | exact D_50e98 | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi, ?at_add_0_r; exact Rcnt | apply bytes4_small; lia]
        | step_simpl]; rewrite (v_lw_small cnt) by lia; vn.                 (* [comment removed for export] *)
      ab_ft I6c718 D_50e9c ltac:(condz).                  (* [comment removed for export] *)
      av I6c71c D_50ea0 (Z_to_bv 64 (cnt - 1)) ltac:(vz). (* [comment removed for export] *)
      an I6c720 D_50ea4.                                   (* [comment removed for export] *)
      av I6c724 D_50ea8 (Z_to_bv 64 ((cnt - 1) * 2 ^ 32)) ltac:(vz).   (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_sw_at with (a := at_ cache (80 * c));
          [exact I6c728 | reflexivity | exact D_50eac
          | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi, ?at_add_0_r; reflexivity
          | gres; rwH; reflexivity
          | exact SOKc ]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      change (wbytes M _ _) with M1.
      an I6c72c D_50eb0.                                   (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 csz) (v := csz);
          [exact I6c730 | reflexivity | exact D_50eb4 | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi; zlit_at; exact Rcsz1 | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      av I6c734 D_50eb8 (Z_to_bv 64 (4 * (cnt - 1))) ltac:(cbv delta [v_srli] beta; rewrite Z.shiftr_div_pow2 by lia; unorm; f_equal;
            replace ((cnt - 1) * 2 ^ 32)%Z with (4 * (cnt - 1) * 2 ^ 30)%Z by lia; apply Z.div_mul; lia).   (* [comment removed for export] *)
      av I6c738 D_50ebc (at_ cache (80 * c + 4 * (cnt - 1))) ltac:(rewrite v_add_at by lia; rewrite at_at; first [reflexivity | f_equal; lia]).  (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lwu with (bs := word_to_le_bytes 4 (Z_to_bv 64 k)) (v := Z_to_bv 64 k);
          [exact I6c73c | reflexivity | exact D_50ec0
          | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; rewrite <- Rk1; f_equal; f_equal; lia
          | apply bytes4_small; lia]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_amoadd_d with (bs := LE8 stw) (v := stw);
          [exact I6c740 | reflexivity | exact D_50ec4
          | gres; rwH; rewrite at_u by lia; rewrite <- Zplus_mod_idemp_l, AL8; reflexivity
          | gres; rwH; exact Rst1
          | apply bytes_le_to_Z_8
          | gres; rwH; exact SOKs1 ]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      change (wbytes M1 _ _) with M'.
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 sbeg) (v := sbeg);
          [exact I6c744 | reflexivity | exact D_50ec8 | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi; zlit_at; exact Rsb' | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      av I6c748 D_50ecc (Z_to_bv 64 (c * 2 ^ 32)) ltac:(vz).        (* [comment removed for export] *)
      av I6c74c D_50ed0 (Z_to_bv 64 (16 * k)) ltac:(vz).            (* [comment removed for export] *)
      av I6c750 D_50ed4 (Z_to_bv 64 (U sbeg + c * 2 ^ 32)) ltac:(vz).   (* [comment removed for export] *)
      av I6c754 D_50ed8 (Z_to_bv 64 (U sbeg + c * 2 ^ 32 + 16 * k)) ltac:(vz).   (* [comment removed for export] *)
      an I6c758 D_50edc.                                   (* [comment removed for export] *)
      ab_tk I6c75c D_50ee0 ltac:(condz).                  (* [comment removed for export] *)
      Ltac cldF F D vv H := chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 vv) (v := vv);
          [exact F | reflexivity | exact D | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi, ?at_at; zlit_at; apply H; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])] | apply bytes_le_to_Z_8]
        | step_simpl]; vn.
      cldF I6c76c D_50ef0 ra (FR' (-8)%Z).                        (* [comment removed for export] *)
      cldF I6c770 D_50ef4 (getr regs 8) (FR' (-16)%Z).             (* [comment removed for export] *)
      cldF I6c774 D_50ef8 (getr regs 9) (FR' (-24)%Z).             (* [comment removed for export] *)
      cldF I6c778 D_50efc (getr regs 18) (FR' (-32)%Z).            (* [comment removed for export] *)
      cldF I6c77c D_50f00 (getr regs 19) (FR' (-40)%Z).            (* [comment removed for export] *)
      cldF I6c780 D_50f04 (getr regs 20) (FR' (-48)%Z).            (* [comment removed for export] *)
      an I6c784 D_50f08.                                   (* [comment removed for export] *)
      aret I6c788 D_50f0c ra.                              (* [comment removed for export] *)
      wd_refl.
    - gres. reflexivity.
    - gres. exact R13.
    - intros i Hi; cbn [In] in Hi.
      repeat (destruct Hi as [<-|Hi]; [gres; rwH; rewrite ?at_0; first [reflexivity | symmetry; assumption] |]). destruct Hi.
    - apply (regs_agree_strengthen (2 :: 8 :: cb_clob) (1 :: 9 :: 18 :: 19 :: 20 :: 2 :: 8 :: cb_clob) regs).
      + (lazymatch goal with |- ?G => let G' := eval unfold cb_clob in G in change_no_check G' end).
        repeat (first [ apply regs_agree_upd; [solve [in_list] |]
                      | apply regs_agree_upd_keep; [ | first [reflexivity | rwH; rewrite ?at_0; reflexivity | symmetry; assumption] | let X := fresh in intros X; discriminate X ] ]).
        regs_agree_weaken AG0.
      + intros i Hi Hni. cbn [cb_clob In] in Hi.
        repeat (destruct Hi as [<-|Hi]; [gres; rwH; rewrite ?at_addi, ?at_0; first [reflexivity | symmetry; assumption | f_equal; lia | exfalso; apply Hni; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]] |]).
        destruct Hi.
  Qed.

  (* [comment removed for export] *)
  Definition cb_mem (cnt : Z) (stw csz : word) : word -> option byte :=
    wbytes (wbytes cb_m1 (at_ cache (80 * class_of s)) (LE4 (cnt - 1))) (at_ cache 2576) (LE8 (v_add stw csz)).
  Theorem cb_run : forall (cnt k : Z) (csz stw sbeg : word),
    let c := class_of s in
    (1 <= cnt <= 16)%Z -> (0 <= k < 2 ^ 32)%Z ->
    rdn segs mem (at_ cache (80 * c)) 4 = Some (LE4 cnt) ->
    rdn segs mem (at_ cache (80 * c + 8)) 8 = Some (LE8 csz) ->
    rdn segs mem (at_ cache (80 * c + 16 + 4 * (cnt - 1))) 4 = Some (LE4 k) ->
    rdn segs mem (at_ cache 2576) 8 = Some (LE8 stw) ->
    store_ok segs mem (at_ cache (80 * c)) 4 = true -> store_ok segs mem (at_ cache 2576) 8 = true ->
    rdn segs mem (at_ inst 32) 8 = Some (LE8 sbeg) ->
    (U cache mod 8 = 0)%Z -> (U inst + 40 <= U cache \/ U cache + 2584 <= U inst)%Z -> (U cache + 2584 <= U sp - 48)%Z -> (U inst + 40 <= 2 ^ 32)%Z ->
    (U sbeg + 2 ^ 37 < 2 ^ 64)%Z ->
    exists r, msteps segs (mkst regs (at_ rb 0x50cec) mem rom) (mkst r ra (cb_mem cnt stw csz) rom)
      /\ getr r 10 = Z_to_bv 64 (U sbeg + c * 2 ^ 32 + 16 * k)
      /\ getr r 13 = Z_to_bv 64 8
      /\ (forall i : reg, In i [1; 2; 8; 9; 18; 19; 20] -> getr r i = getr regs i)
      /\ regs_agree CLX regs r.
  Proof using G1 H1 H10 H11 H12 H13 H2 HCB Hret Hs Hstk RB.
    intros cnt k csz stw sbeg c Hcnt Hk Rcnt Rcsz Rk Rst SOKc SOKs Rsb AL8 Gc Gcs Gi Gsb.
    pose proof G1 as [G1a G1b]. pose proof Hs as [Hs1 Hs2]. pose proof (u64_range sp) as Hspr. pose proof (u64_range cache) as Hcr. pose proof (u64_range inst) as Hir.
    pose proof (AsArith3.class_of_range s ltac:(lia)) as Hc. fold c in Hc.
    destruct cbP as (r1 & RUN1 & A2 & A10 & A11 & A12 & A13 & A14 & A15 & AG1).
    assert (CID : exists r2, msteps segs (mkst r1 (at_ rb 0x50d70) cb_m1 rom) (mkst r2 (at_ rb 0x50e80) cb_m1 rom)
              /\ getr r2 8 = Z_to_bv 64 c /\ (forall i : reg, In i [2; 10; 11; 13] -> getr r2 i = getr r1 i) /\ regs_agree CLX regs r2).
    { destruct (Z.leb_spec s 512).
      - exact (cbLo cb_m1 r1 ltac:(lia) A12 A14 AG1).
      - exact (cbHi cb_m1 r1 ltac:(lia) A12 A14 AG1). }
    destruct CID as (r2 & RUN2 & B8 & BK & AG2).
    Ltac cellB R OUT := rewrite <- R; apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply OUT; rewrite at_u in Hx by lia; cbn in Hx; lia].
    destruct (cbB cb_m1 r2 c cnt k csz stw sbeg B8
                ltac:(rewrite (BK 2) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]); exact A2) ltac:(rewrite (BK 10) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]); exact A10)
                ltac:(rewrite (BK 11) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]); exact A11) ltac:(rewrite (BK 13) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]); exact A13) AG2 Hc Hcnt Hk)
      as (r3 & RUN3 & C10 & C13 & CK & AG3).
    { cellB Rcnt cb_m1_outside. } { cellB Rcsz cb_m1_outside. } { cellB Rk cb_m1_outside. } { cellB Rst cb_m1_outside. }
    { eapply store_ok_mono; [apply cb_m1_grows | exact SOKc]. } { eapply store_ok_mono; [apply cb_m1_grows | exact SOKs]. }
    { cellB Rsb cb_m1_outside. }
    { intros o v Hin. apply cb_m1_slots. exact Hin. }
    { exact AL8. } { exact Gc. } { exact Gcs. } { exact Gi. } { exact Gsb. }
    exists r3. split; [|split; [exact C10 | split; [exact C13 | split; [exact CK | exact AG3]]]].
    eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. exact RUN3.
  Qed.
End CB.
(* [comment removed for export] *)
Lemma needed_facts : forall n, (1 <= n <= 64512)%Z -> (24 <= needed n <= 65536)%Z /\ (needed n mod 8 = 0)%Z.
Proof using.
intros n Hn.
  pose proof (rz_log_range n) as HRL.
  assert (Hrz : (rz n = 16 * 2 ^ rz_log n)%Z) by reflexivity.
  assert (Hrz2 : (16 <= rz n <= 1024)%Z).
  { rewrite Hrz. destruct (rz_log_cases n ltac:(lia)) as [[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[C E]]]]]]]]; rewrite E; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia. }
  assert (Hrd : (rounded n = RoundUp (Z.max n 8) 8)%Z) by reflexivity.
  assert (Hrd2 : (Z.max n 8 <= rounded n <= Z.max n 8 + 7 /\ rounded n mod 8 = 0)%Z).
  { rewrite Hrd. (lazymatch goal with |- ?G => let G' := eval unfold RoundUp in G in change_no_check G' end). pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)).
    split; [lia|]. apply Z_mod_mult. }
  assert (Hnd : (needed n = rounded n + rz n)%Z) by reflexivity.
  assert (Hprim : (needed n <= 65536)%Z).
  { pose proof (AsArith3.is_primary_iff n ltac:(lia)) as X. destruct X as [_ X]. specialize (X ltac:(lia)). unfold is_primary in X. apply Z.leb_le. exact X. }
  split; [lia|].
  rewrite Hnd, Hrz. destruct Hrd2 as [_ Hm].
  rewrite Z.add_mod, Hm by lia. replace (16 * 2 ^ rz_log n)%Z with ((2 * 2 ^ rz_log n) * 8)%Z by lia. rewrite Z_mod_mult. reflexivity.
Qed.

(* [comment removed for export] *)
Section AMB.
  Variable segs : list Segment.
  Variable rb : word.
  Hypothesis HAL : code_ato segs rb 0x4c594 al_words.
  Hypothesis HCB : code_ato segs rb 0x50cec cb_words.
  Hypothesis RB : (U rb mod 2 = 0)%Z /\ (U rb + 2 ^ 24 < 2 ^ 64)%Z.
  Variable gt : gct_tab.
  Hypothesis GTOK : gct_tab_ok segs gt.
  Hypothesis GTRB : gt_rb gt = rb.

  Lemma J67750 : fetch_word segs (at_ rb 0x4c814) = Some W_4c814.  Proof using HAL. exact (code_ato_get segs rb 0x4c594 al_words 160 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J67754 : fetch_word segs (at_ rb 0x4c818) = Some W_4c818.  Proof using HAL. exact (code_ato_get segs rb 0x4c594 al_words 161 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J67758 : fetch_word segs (at_ rb 0x4c81c) = Some W_4c81c.  Proof using HAL. exact (code_ato_get segs rb 0x4c594 al_words 162 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J6775c : fetch_word segs (at_ rb 0x4c820) = Some W_4c820.  Proof using HAL. exact (code_ato_get segs rb 0x4c594 al_words 163 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J67760 : fetch_word segs (at_ rb 0x4c824) = Some W_4c824.  Proof using HAL. exact (code_ato_get segs rb 0x4c594 al_words 164 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J67764 : fetch_word segs (at_ rb 0x4c828) = Some W_4c828.  Proof using HAL. exact (code_ato_get segs rb 0x4c594 al_words 165 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J67768 : fetch_word segs (at_ rb 0x4c82c) = Some W_4c82c.  Proof using HAL. exact (code_ato_get segs rb 0x4c594 al_words 166 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J6776c : fetch_word segs (at_ rb 0x4c830) = Some W_4c830.  Proof using HAL. exact (code_ato_get segs rb 0x4c594 al_words 167 _ HAL eq_refl). Qed.   (* [comment removed for export] *)

  Variables (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (sp tp tsdp tctx thr inst : word) (n : Z).
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H4 : getr regs 4 = tp.
  Hypothesis H19 : getr regs 19 = Z_to_bv 64 (needed n).
  Hypothesis H22 : getr regs 22 = inst.
  Hypothesis Hn : (1 <= n <= 64512)%Z.
  Hypothesis GH : gctH segs gt mem sp tp tsdp tctx thr.
  Hypothesis Hstk : store_ok segs mem (at_ sp (-48)) 48 = true.
  Hypothesis G1 : (2 ^ 32 + 48 <= U sp)%Z /\ (U sp + 16 <= 2 ^ 47)%Z.
  (* [comment removed for export] *)
  Hypothesis Gthr : (4096 <= U thr /\ (U thr + 4096 <= AIMGLO \/ AIMGHI <= U thr))%Z /\ (U thr + 4096 <= U sp - 48)%Z /\ (U thr mod 8 = 0)%Z.
  Hypothesis Ginst : (AIMGLO <= U inst /\ U inst + 40 <= AIMGHI)%Z.

  #[local] Abbreviation CLB := (fun r => In r (26 :: 1 :: 5 :: 6 :: 10 :: 11 :: 12 :: 13 :: 14 :: 15 :: 16 :: 17 :: nil)).

  Lemma RETb : forall d, (d mod 2 = 0)%Z -> (0 <= d < 2 ^ 24)%Z -> ret_ok (at_ rb d).
  Proof using Gthr thr sp RB. intros d Hd Hdr. pose proof RB as [E1 E2]. pose proof (u64_range rb). apply ret_ok_at; [exact E1 | exact Hd | lia]. Qed.


  (* [comment removed for export] *)
  Definition amB_frame : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem (at_ sp (-8)) (LE8 (at_ rb 0x4c818)))
      (at_ sp (-8)) (LE8 (at_ rb 0x4c834))) (at_ sp (-16)) (LE8 (getr regs 8))) (at_ sp (-24)) (LE8 (getr regs 9)))
      (at_ sp (-32)) (LE8 (getr regs 18))) (at_ sp (-40)) (LE8 (getr regs 19))) (at_ sp (-48)) (LE8 (getr regs 20)).
  Definition amB_mem (cnt : Z) (stw csz : word) : word -> option byte :=
    wbytes (wbytes amB_frame (at_ thr (208 + 80 * class_of (needed n))) (LE4 (cnt - 1))) (at_ thr 2784) (LE8 (v_add stw csz)).




  Theorem amB_run : forall (cnt k : Z) (csz stw sbeg : word),
    let c := class_of (needed n) in
    (1 <= cnt <= 16)%Z -> (0 <= k < 2 ^ 32)%Z ->
    rdn segs mem (at_ thr (208 + 80 * c)) 4 = Some (LE4 cnt) ->
    rdn segs mem (at_ thr (208 + 80 * c + 8)) 8 = Some (LE8 csz) ->
    rdn segs mem (at_ thr (208 + 80 * c + 16 + 4 * (cnt - 1))) 4 = Some (LE4 k) ->
    rdn segs mem (at_ thr 2784) 8 = Some (LE8 stw) ->
    store_ok segs mem (at_ thr (208 + 80 * c)) 4 = true -> store_ok segs mem (at_ thr 2784) 8 = true ->
    rdn segs mem (at_ inst 32) 8 = Some (LE8 sbeg) -> (U sbeg + 2 ^ 37 < 2 ^ 64)%Z ->
    exists r,
      msteps segs (mkst regs (at_ rb 0x4c814) mem rom) (mkst r (at_ rb 0x4c834) (amB_mem cnt stw csz) rom)
      /\ getr r 10 = Z_to_bv 64 (U sbeg + c * 2 ^ 32 + 16 * k)
      /\ getr r 26 = thr
      /\ regs_agree CLB regs r.
  Proof using G1 GH GTOK GTRB Ginst Gthr H19 H2 H22 H4 HAL HCB Hn Hstk RB.
    intros cnt k csz stw sbeg c Hcnt Hk Rcnt Rcsz Rk Rst SOKc SOKs Rsb Gsb.
    pose proof G1 as [G1a G1b]. pose proof Gthr as (Gt1 & Gt2 & Gt3). pose proof (u64_range sp) as Hspr. pose proof (u64_range thr) as Hthr. pose proof (u64_range inst) as Hir.
    pose proof (needed_facts n Hn) as NF. pose proof (AsArith3.class_of_range (needed n) ltac:(lia)) as Hc. fold c in Hc.
    (* [comment removed for export] *)
    assert (W0 : exists r0, msteps segs (mkst regs (at_ rb 0x4c814) mem rom) (mkst r0 (at_ rb 0x78e2c) mem rom)
                 /\ getr r0 1 = at_ rb 0x4c818 /\ (forall i : reg, i <> 1 -> getr r0 i = getr regs i)).
    { wd_eexists. split; [an J67750 D_4c814; wd_refl|]. split; [gres; reflexivity|]. intros i Hi. rewrite getr_other by (intros E; apply Hi; exact E). reflexivity. }
    destruct W0 as (r0 & RUN0 & A1 & AK).
    destruct (gct_run segs gt GTOK mem rom r0 (at_ rb 0x4c818) sp tp tsdp tctx thr GH) as (r1 & RUN1 & B10 & B11 & AG1).
    { rewrite <- GTRB. pose proof (gto_rb _ _ GTOK) as [E1 E2]. pose proof (u64_range (gt_rb gt)). apply ret_ok_at; [exact E1 | reflexivity | lia]. }
    { exact A1. } { rewrite AK by (intros E; discriminate E). exact H2. } { rewrite AK by (intros E; discriminate E). exact H4. }
    rewrite GTRB in RUN1.
    set (M1 := wbytes mem (at_ sp (-8)) (LE8 (at_ rb 0x4c818))) in RUN1.
    (* [comment removed for export] *)
    Ltac r1eq AG1 AK r H := rewrite (AG1 r) by notin_list; rewrite (AK r) by (intros E; discriminate E); exact H.
    assert (W2 : exists r2, msteps segs (mkst r1 (at_ rb 0x4c818) M1 rom) (mkst r2 (at_ rb 0x50cec) M1 rom)
                 /\ getr r2 1 = at_ rb 0x4c834 /\ getr r2 2 = sp /\ getr r2 10 = inst /\ getr r2 11 = at_ thr 208
                 /\ getr r2 12 = Z_to_bv 64 (needed n) /\ getr r2 13 = Z_to_bv 64 8 /\ getr r2 26 = thr
                 /\ (forall i : reg, In i [4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 27; 3] -> getr r2 i = getr regs i)
                 /\ regs_agree (fun r => In r [26; 1; 10; 11; 12; 13]) r1 r2).
    { wd_eexists. split.
      - an J67754 D_4c818.                                   (* [comment removed for export] *)
        ab_ft J67758 D_4c81c ltac:(condz).                  (* [comment removed for export] *)
        an J6775c D_4c820.                                   (* [comment removed for export] *)
        an J67760 D_4c824.                                   (* [comment removed for export] *)
        an J67764 D_4c828.                                   (* [comment removed for export] *)
        an J67768 D_4c82c.                                   (* [comment removed for export] *)
        an J6776c D_4c830.                                   (* [comment removed for export] *)
        wd_refl.
      - post; rewrite ?B10, ?at_0; try reflexivity.
        + r1eq AG1 AK (2:reg) H2.
        + r1eq AG1 AK (22:reg) H22.
        + r1eq AG1 AK (19:reg) H19.
        + intros i Hi; cbn [In] in Hi; repeat (destruct Hi as [<-|Hi]; [gres; rewrite (AG1 _) by notin_list; apply AK; intros E; discriminate E|]); destruct Hi.
        + ra_solve. }
    destruct W2 as (r2 & RUN2 & C1 & C2 & C10 & C11 & C12 & C13 & C26 & CK & AG2).
    (* [comment removed for export] *)
    assert (SOK1 : store_ok segs M1 (at_ sp (-48)) 48 = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end). eapply store_ok_mono; [apply wbytes_grows | exact Hstk]. }
    assert (M1_out : forall x : word, (U x < U sp - 8 \/ U sp <= U x)%Z -> M1 x = mem x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end). rewrite wbytes_outside; [reflexivity | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    Ltac cellM R OUT := rewrite <- R; rewrite ?at_at;
      try match goal with |- rdn _ _ ?a _ = rdn _ _ ?b _ => replace a with b by ((lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); f_equal; lia) end;
      apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply OUT; rewrite at_u in Hx by lia; cbn in Hx; lia].
    destruct (cb_run segs rb HCB RB r2 M1 rom (at_ rb 0x4c834) sp (at_ thr 208) inst (needed n) (RETb 0x4c834 eq_refl ltac:(lia))
                C1 C2 C10 C11 C12 C13 NF SOK1 G1 cnt k csz stw sbeg Hcnt Hk)
      as (r3 & RUN3 & D10 & D13 & DK & AG3).
    { cellM Rcnt M1_out. } { cellM Rcsz M1_out. } { cellM Rk M1_out. } { cellM Rst M1_out. }
    { rewrite at_at. (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end). eapply store_ok_mono; [apply wbytes_grows | exact SOKc]. }
    { rewrite at_at. (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end). eapply store_ok_mono; [apply wbytes_grows | exact SOKs]. }
    { cellM Rsb M1_out. }
    { rewrite at_u by lia. rewrite <- Zplus_mod_idemp_l, Gt3. reflexivity. }
    { rewrite at_u by lia. lia. } { rewrite at_u by lia. lia. } { lia. } { exact Gsb. }
    exists r3. split; [|split; [exact D10 | split]].
    - eapply msteps_trans; [exact RUN0|]. eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
      match type of RUN3 with msteps _ _ (mkst _ _ ?MF _) => replace (amB_mem cnt stw csz) with MF; [exact RUN3|] end.
      (lazymatch goal with |- ?G => let G' := eval unfold amB_mem, amB_frame, cb_mem, cb_m1, M1 in G in change_no_check G' end). rewrite !at_at.
      rewrite (CK 8), (CK 9), (CK 18), (CK 19), (CK 20) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]). reflexivity.
    - rewrite (AG3 26) by notin_list. exact C26.
    - (* [comment removed for export] *)
      intros i Hni.
      assert (E3 : forall j : reg, In j [1; 2; 8; 9; 18; 19; 20] -> getr r3 j = getr r2 j) by exact DK.
      destruct (In_dec (fun x y : reg => decide (x = y)) i [1; 2; 8; 9; 18; 19; 20]) as [Hin|Hnin].
      + rewrite (E3 i Hin). cbn [In] in Hin.
        repeat (destruct Hin as [<-|Hin]; [first [exfalso; apply Hni; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])] | rewrite C2; symmetry; exact H2 | apply CK; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]] |]). destruct Hin.
      + Ltac nix Hx Hni Hnin := repeat (destruct Hx as [<-|Hx]; [first [apply Hni; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])] | apply Hnin; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]] |]); destruct Hx.
        rewrite (AG3 i). 2: { intros Hx. cbn [cb_clob In] in Hx. nix Hx Hni Hnin. }
        rewrite (AG2 i). 2: { intros Hx. cbn [In] in Hx. nix Hx Hni Hnin. }
        rewrite (AG1 i). 2: { intros Hx. cbn [gct_clob In] in Hx. nix Hx Hni Hnin. }
        apply AK. intros ->. apply Hni. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). solve [repeat (first [left; reflexivity | right])].
  Qed.
End AMB.
End FPGen1.
