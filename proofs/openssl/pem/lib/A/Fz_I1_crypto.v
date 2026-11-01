(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac RzCPS NodesA SysStep FarCall.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim Malloc Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import LhPure LhRep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit Fz_ckit I_ut I_lkit Fz_chk Fz_fkit Th_mutex Th_once Fz_T_once Fz_env Fz_M_malloc Fz_W5_icb Fz_I1_defs Fz_I1_loadw Fz_I1_load Fz_I1_errload Fz_I1_const Fz_I1_reason Fz_I1_first Fz_I1_stubk Fz_I1_stubs Fz_I1_efirst Fz_I1_tabs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation z64 := (Z_to_bv 64 0) (only parsing).

Definition e_crypto_strs : Z := 0x511100.

Definition CR_SITES : list (Z * Z) :=
  [(0x511118, e_crypto_strs); (0x511120, e_crypto_strs); (0x511128, e_crypto_strs); (0x511130, e_crypto_strs); (0x511138, e_crypto_strs); (0x511140, e_crypto_strs); (0x511148, e_crypto_strs); (0x511150, e_crypto_strs); (0x511158, e_crypto_strs); (0x511160, e_crypto_strs); (0x511168, e_crypto_strs); (0x511170, e_crypto_strs); (0x511178, e_crypto_strs); (0x511180, e_crypto_strs); (0x511188, e_crypto_strs); (0x511190, e_crypto_strs); (0x511198, e_crypto_strs); (0x5111a0, e_crypto_strs); (0x5111a8, e_crypto_strs); (0x5111b0, e_crypto_strs); (0x5111b8, e_crypto_strs); (0x5111c0, e_crypto_strs); (0x5111c8, e_crypto_strs); (0x5111d0, e_crypto_strs); (0x5111d8, e_crypto_strs); (0x5111e0, e_crypto_strs); (0x5111e8, e_crypto_strs); (0x5111f0, e_crypto_strs); (0x5111f8, e_crypto_strs); (0x511200, e_crypto_strs); (0x511208, e_crypto_strs); (0x511210, e_crypto_strs); (0x511218, e_crypto_strs); (0x511220, e_crypto_strs); (0x511228, e_crypto_strs)]
  ++ EFIRST_SITES ++ STUB_SITES 0x51123c 0x511270 ++ STUB_SITES 0x511284 0x5112b8 ++ STUB_SITES 0x5112cc 0x511300 ++ STUB_SITES 0x511314 0x511348 ++ STUB_SITES 0x51135c 0x51138c ++ STUB_SITES 0x5113a0 0x5113d4 ++ STUB_SITES 0x5113e8 0x51141c ++ STUB_SITES 0x511430 0x511464 ++ STUB_SITES 0x511478 0x5114ac ++ STUB_SITES 0x5114c0 0x5114f4 ++ STUB_SITES 0x511508 0x51153c ++ STUB_SITES 0x511550 0x511584 ++ STUB_SITES 0x511598 0x5115cc ++ STUB_SITES 0x5115e0 0x511614 ++ STUB_SITES 0x511628 0x51165c ++ STUB_SITES 0x511670 0x5116a4 ++ STUB_SITES 0x5116b8 0x5116ec ++ STUB_SITES 0x511700 0x511734 ++ STUB_SITES 0x511748 0x51177c ++ STUB_SITES 0x511790 0x5117c4 ++ STUB_SITES 0x5117d8 0x51180c ++ STUB_SITES 0x511820 0x511854 ++ STUB_SITES 0x511868 0x51189c ++ STUB_SITES 0x5118b0 0x5118e4 ++ STUB_SITES 0x5118f8 0x51192c ++ STUB_SITES 0x511940 0x511974 ++ STUB_SITES 0x511988 0x5119bc ++ STUB_SITES 0x5119d0 0x511a04 ++ STUB_SITES 0x511a18 0x511a4c ++ STUB_SITES 0x511a60 0x511a94 ++ STUB_SITES 0x511aa8 0x511adc ++ STUB_SITES 0x511af0 0x511b24 ++ STUB_SITES 0x511b38 0x511b6c ++ STUB_SITES 0x511b80 0x511bb4.
Definition CR_CALLS : list (Z * Z) :=
  [(0x511118, e_err_strings); (0x511120, 0x51123c); (0x511128, 0x511284); (0x511130, 0x5112cc); (0x511138, 0x511314); (0x511140, 0x51135c); (0x511148, 0x5113a0); (0x511150, 0x5113e8); (0x511158, 0x511430); (0x511160, 0x511478); (0x511168, 0x5114c0); (0x511170, 0x511508); (0x511178, 0x511550); (0x511180, 0x511598); (0x511188, 0x5115e0); (0x511190, 0x511628); (0x511198, 0x511670); (0x5111a0, 0x5116b8); (0x5111a8, 0x511700); (0x5111b0, 0x511748); (0x5111b8, 0x511790); (0x5111c0, 0x5117d8); (0x5111c8, 0x511820); (0x5111d0, 0x511868); (0x5111d8, 0x5118b0); (0x5111e0, 0x5118f8); (0x5111e8, 0x511940); (0x5111f0, 0x511988); (0x5111f8, 0x5119d0); (0x511200, 0x511a18); (0x511208, 0x511a60); (0x511210, 0x511aa8); (0x511218, 0x511af0); (0x511220, 0x511b38); (0x511228, 0x511b80)]
  ++ EFIRST_CALLS ++ STUB_CALLS 0x511270 ++ STUB_CALLS 0x5112b8 ++ STUB_CALLS 0x511300 ++ STUB_CALLS 0x511348 ++ STUB_CALLS 0x51138c ++ STUB_CALLS 0x5113d4 ++ STUB_CALLS 0x51141c ++ STUB_CALLS 0x511464 ++ STUB_CALLS 0x5114ac ++ STUB_CALLS 0x5114f4 ++ STUB_CALLS 0x51153c ++ STUB_CALLS 0x511584 ++ STUB_CALLS 0x5115cc ++ STUB_CALLS 0x511614 ++ STUB_CALLS 0x51165c ++ STUB_CALLS 0x5116a4 ++ STUB_CALLS 0x5116ec ++ STUB_CALLS 0x511734 ++ STUB_CALLS 0x51177c ++ STUB_CALLS 0x5117c4 ++ STUB_CALLS 0x51180c ++ STUB_CALLS 0x511854 ++ STUB_CALLS 0x51189c ++ STUB_CALLS 0x5118e4 ++ STUB_CALLS 0x51192c ++ STUB_CALLS 0x511974 ++ STUB_CALLS 0x5119bc ++ STUB_CALLS 0x511a04 ++ STUB_CALLS 0x511a4c ++ STUB_CALLS 0x511a94 ++ STUB_CALLS 0x511adc ++ STUB_CALLS 0x511b24 ++ STUB_CALLS 0x511b6c ++ STUB_CALLS 0x511bb4.

(* [comment removed for export] *)
Lemma ec_w0 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => exists m' : mem,
       ms = MS (mkR (Z_to_bv 64 0x511118) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 sp s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 e_err_strings) fc None m' (seg_rom asegs)
       /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
       /\ rw_cells asegs m' (bv_unsigned sp + -16) [C8 s0; C8 ra] /\ stk asegs m' lo (bv_unsigned sp + -16))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_crypto_strs) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros stack_ok lo_high lo_room sp_cap mem_ok.
  pose proof (wmono_refl asegs m) as grown.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as touched.
  carve_frame 16%nat stack_ok.
  do 5 zstep.
  apply evt_done. exists m1.
  split; [reflexivity|].
  split; [exact touched|]. split; [exact grown|]. split; [exact mem_ok|]. split; [exact FR | exact stack_ok].
Qed.

(* [comment removed for export] *)
Definition ecw_spec (Rp Rk E : Z) : Prop :=
  forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
    stk asegs m lo (bv_unsigned sp + -16) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m ->
    evt asegs (fun ms => ms = MS (mkR (Z_to_bv 64 Rk) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 E) fc None m (seg_rom asegs))
      (MS (mkR (Z_to_bv 64 Rp) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 Rp) fc None m (seg_rom asegs)).
Ltac ecw_tac sp m :=
  set (frame_sp := Z_to_bv 64 (bv_unsigned sp + -16)) in *;
  zstep;
  lazymatch goal with
  | |- evt asegs _ (MS _ _ (if ?taken then _ else _) _ _ m _) =>
      let v := eval vm_compute in taken in change taken with v; cbv iota
  end;
  zstep;
  apply evt_done; reflexivity.
Lemma ec_w1 : ecw_spec 0x511118 0x511120 0x51123c. Proof. unfold ecw_spec; intros until lo; intros ST LO0 LO HTOP MI; ecw_tac sp m. Qed.
Lemma ec_w2 : ecw_spec 0x511120 0x511128 0x511284. Proof. unfold ecw_spec; intros until lo; intros ST LO0 LO HTOP MI; ecw_tac sp m. Qed.
Lemma ec_w3 : ecw_spec 0x511128 0x511130 0x5112cc. Proof. unfold ecw_spec; intros until lo; intros ST LO0 LO HTOP MI; ecw_tac sp m. Qed.
Lemma ec_w4 : ecw_spec 0x511130 0x511138 0x511314. Proof. unfold ecw_spec; intros until lo; intros ST LO0 LO HTOP MI; ecw_tac sp m. Qed.
Lemma ec_w5 : ecw_spec 0x511138 0x511140 0x51135c. Proof. unfold ecw_spec; intros until lo; intros ST LO0 LO HTOP MI; ecw_tac sp m. Qed.
Lemma ec_w6 : ecw_spec 0x511140 0x511148 0x5113a0. Proof. unfold ecw_spec; intros until lo; intros ST LO0 LO HTOP MI; ecw_tac sp m. Qed.
Lemma ec_w7 : ecw_spec 0x511148 0x511150 0x5113e8. Proof. unfold ecw_spec; intros until lo; intros ST LO0 LO HTOP MI; ecw_tac sp m. Qed.
Lemma ec_w8 : ecw_spec 0x511150 0x511158 0x511430. Proof. unfold ecw_spec; intros until lo; intros ST LO0 LO HTOP MI; ecw_tac sp m. Qed.
Lemma ec_w9 : ecw_spec 0x511158 0x511160 0x511478. Proof. unfold ecw_spec; intros until lo; intros ST LO0 LO HTOP MI; ecw_tac sp m. Qed.
Lemma ec_w10 : ecw_spec 0x511160 0x511168 0x5114c0. Proof. unfold ecw_spec; intros until lo; intros ST LO0 LO HTOP MI; ecw_tac sp m. Qed.
Lemma ec_w11 : ecw_spec 0x511168 0x511170 0x511508. Proof. unfold ecw_spec; intros until lo; intros ST LO0 LO HTOP MI; ecw_tac sp m. Qed.
Lemma ec_w12 : ecw_spec 0x511170 0x511178 0x511550. Proof. unfold ecw_spec; intros until lo; intros ST LO0 LO HTOP MI; ecw_tac sp m. Qed.
Lemma ec_w13 : ecw_spec 0x511178 0x511180 0x511598. Proof. unfold ecw_spec; intros until lo; intros ST LO0 LO HTOP MI; ecw_tac sp m. Qed.
Lemma ec_w14 : ecw_spec 0x511180 0x511188 0x5115e0. Proof. unfold ecw_spec; intros until lo; intros ST LO0 LO HTOP MI; ecw_tac sp m. Qed.
Lemma ec_w15 : ecw_spec 0x511188 0x511190 0x511628. Proof. unfold ecw_spec; intros until lo; intros ST LO0 LO HTOP MI; ecw_tac sp m. Qed.
Lemma ec_w16 : ecw_spec 0x511190 0x511198 0x511670. Proof. unfold ecw_spec; intros until lo; intros ST LO0 LO HTOP MI; ecw_tac sp m. Qed.
Lemma ec_w17 : ecw_spec 0x511198 0x5111a0 0x5116b8. Proof. unfold ecw_spec; intros until lo; intros ST LO0 LO HTOP MI; ecw_tac sp m. Qed.
Lemma ec_w18 : ecw_spec 0x5111a0 0x5111a8 0x511700. Proof. unfold ecw_spec; intros until lo; intros ST LO0 LO HTOP MI; ecw_tac sp m. Qed.
Lemma ec_w19 : ecw_spec 0x5111a8 0x5111b0 0x511748. Proof. unfold ecw_spec; intros until lo; intros ST LO0 LO HTOP MI; ecw_tac sp m. Qed.
Lemma ec_w20 : ecw_spec 0x5111b0 0x5111b8 0x511790. Proof. unfold ecw_spec; intros until lo; intros ST LO0 LO HTOP MI; ecw_tac sp m. Qed.
Lemma ec_w21 : ecw_spec 0x5111b8 0x5111c0 0x5117d8. Proof. unfold ecw_spec; intros until lo; intros ST LO0 LO HTOP MI; ecw_tac sp m. Qed.
Lemma ec_w22 : ecw_spec 0x5111c0 0x5111c8 0x511820. Proof. unfold ecw_spec; intros until lo; intros ST LO0 LO HTOP MI; ecw_tac sp m. Qed.
Lemma ec_w23 : ecw_spec 0x5111c8 0x5111d0 0x511868. Proof. unfold ecw_spec; intros until lo; intros ST LO0 LO HTOP MI; ecw_tac sp m. Qed.
Lemma ec_w24 : ecw_spec 0x5111d0 0x5111d8 0x5118b0. Proof. unfold ecw_spec; intros until lo; intros ST LO0 LO HTOP MI; ecw_tac sp m. Qed.
Lemma ec_w25 : ecw_spec 0x5111d8 0x5111e0 0x5118f8. Proof. unfold ecw_spec; intros until lo; intros ST LO0 LO HTOP MI; ecw_tac sp m. Qed.
Lemma ec_w26 : ecw_spec 0x5111e0 0x5111e8 0x511940. Proof. unfold ecw_spec; intros until lo; intros ST LO0 LO HTOP MI; ecw_tac sp m. Qed.
Lemma ec_w27 : ecw_spec 0x5111e8 0x5111f0 0x511988. Proof. unfold ecw_spec; intros until lo; intros ST LO0 LO HTOP MI; ecw_tac sp m. Qed.
Lemma ec_w28 : ecw_spec 0x5111f0 0x5111f8 0x5119d0. Proof. unfold ecw_spec; intros until lo; intros ST LO0 LO HTOP MI; ecw_tac sp m. Qed.
Lemma ec_w29 : ecw_spec 0x5111f8 0x511200 0x511a18. Proof. unfold ecw_spec; intros until lo; intros ST LO0 LO HTOP MI; ecw_tac sp m. Qed.
Lemma ec_w30 : ecw_spec 0x511200 0x511208 0x511a60. Proof. unfold ecw_spec; intros until lo; intros ST LO0 LO HTOP MI; ecw_tac sp m. Qed.
Lemma ec_w31 : ecw_spec 0x511208 0x511210 0x511aa8. Proof. unfold ecw_spec; intros until lo; intros ST LO0 LO HTOP MI; ecw_tac sp m. Qed.
Lemma ec_w32 : ecw_spec 0x511210 0x511218 0x511af0. Proof. unfold ecw_spec; intros until lo; intros ST LO0 LO HTOP MI; ecw_tac sp m. Qed.
Lemma ec_w33 : ecw_spec 0x511218 0x511220 0x511b38. Proof. unfold ecw_spec; intros until lo; intros ST LO0 LO HTOP MI; ecw_tac sp m. Qed.
Lemma ec_w34 : ecw_spec 0x511220 0x511228 0x511b80. Proof. unfold ecw_spec; intros until lo; intros ST LO0 LO HTOP MI; ecw_tac sp m. Qed.

(* [comment removed for export] *)
Lemma ec_wx : forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (rav s0v : word),
  rw_cells asegs m (bv_unsigned sp + -16) [C8 s0v; C8 rav] ->
  stk asegs m lo (bv_unsigned sp + -16) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR rav sp gp tp t0 t1 t2 s0v s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc rav) fc None m (seg_rom asegs)
                       /\ stk asegs m lo (bv_unsigned sp))
    (MS (mkR (Z_to_bv 64 0x511228) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x511228) fc None m (seg_rom asegs)).
Proof.
  intros until s0v. intros saved stack_ok lo_high lo_room sp_cap mem_ok.
  do 5 zstep.
  apply evt_done. split; [reflexivity|].
  pose proof (stk_release asegs m lo (bv_unsigned sp + -16) [C8 s0v; C8 rav] stack_ok saved ltac:(lia)) as popped.
  cbn [cells_size csize Nat.add Z.of_nat] in popped.
  replace (bv_unsigned sp) with (bv_unsigned sp + -16 + 16) by lia. exact popped.
Qed.

Section Crypto.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_EFIRST : efirst_stmt RT GOBJ.
Hypothesis C_ERS : ers_stmt RT GOBJ.
Hypothesis C_ELC : err_const_stmt RT GOBJ.
(* [comment removed for export] *)
Hypothesis GO_libraries : exists b sz, GOBJ b sz /\ b <= 0x52ec60 /\ 0x52ec60 + 16 * (43 + 1) <= b + sz.
Hypothesis GO_reasons : exists b sz, GOBJ b sz /\ b <= 0x52efc0 /\ 0x52efc0 + 16 * (39 + 1) <= b + sz.
Hypothesis GO_BN : exists b sz, GOBJ b sz /\ b <= 0x59b500 /\ 0x59b500 + 16 * (22 + 1) <= b + sz.
Hypothesis GO_RSA : exists b sz, GOBJ b sz /\ b <= 0x59b6c0 /\ 0x59b6c0 + 16 * (81 + 1) <= b + sz.
Hypothesis GO_DH : exists b sz, GOBJ b sz /\ b <= 0x59bd20 /\ 0x59bd20 + 16 * (31 + 1) <= b + sz.
Hypothesis GO_EVP : exists b sz, GOBJ b sz /\ b <= 0x59bfa0 /\ 0x59bfa0 + 16 * (125 + 1) <= b + sz.
Hypothesis GO_BUF : exists b sz, GOBJ b sz /\ b <= 0xf88e0 /\ 0xf88e0 + 16 * (0 + 1) <= b + sz.
Hypothesis GO_OBJ : exists b sz, GOBJ b sz /\ b <= 0x59c960 /\ 0x59c960 + 16 * (3 + 1) <= b + sz.
Hypothesis GO_PEM : exists b sz, GOBJ b sz /\ b <= 0x59c9c0 /\ 0x59c9c0 + 16 * (34 + 1) <= b + sz.
Hypothesis GO_DSA : exists b sz, GOBJ b sz /\ b <= 0x59cc80 /\ 0x59cc80 + 16 * (16 + 1) <= b + sz.
Hypothesis GO_X509 : exists b sz, GOBJ b sz /\ b <= 0x59cde0 /\ 0x59cde0 + 16 * (47 + 1) <= b + sz.
Hypothesis GO_ASN1 : exists b sz, GOBJ b sz /\ b <= 0x59d1a0 /\ 0x59d1a0 + 16 * (117 + 1) <= b + sz.
Hypothesis GO_CONF : exists b sz, GOBJ b sz /\ b <= 0x59dac0 /\ 0x59dac0 + 16 * (27 + 1) <= b + sz.
Hypothesis GO_CRYPTO : exists b sz, GOBJ b sz /\ b <= 0x59dce0 /\ 0x59dce0 + 16 * (31 + 1) <= b + sz.
Hypothesis GO_COMP : exists b sz, GOBJ b sz /\ b <= 0x59df60 /\ 0x59df60 + 16 * (10 + 1) <= b + sz.
Hypothesis GO_EC : exists b sz, GOBJ b sz /\ b <= 0x59e040 /\ 0x59e040 + 16 * (76 + 1) <= b + sz.
Hypothesis GO_BIO : exists b sz, GOBJ b sz /\ b <= 0x59e640 /\ 0x59e640 + 16 * (47 + 1) <= b + sz.
Hypothesis GO_PKCS7 : exists b sz, GOBJ b sz /\ b <= 0x59ea00 /\ 0x59ea00 + 16 * (38 + 1) <= b + sz.
Hypothesis GO_X509V3 : exists b sz, GOBJ b sz /\ b <= 0x59ed00 /\ 0x59ed00 + 16 * (73 + 1) <= b + sz.
Hypothesis GO_PKCS12 : exists b sz, GOBJ b sz /\ b <= 0x59f2c0 /\ 0x59f2c0 + 16 * (22 + 1) <= b + sz.
Hypothesis GO_RAND : exists b sz, GOBJ b sz /\ b <= 0x59f480 /\ 0x59f480 + 16 * (45 + 1) <= b + sz.
Hypothesis GO_DSO : exists b sz, GOBJ b sz /\ b <= 0x59f800 /\ 0x59f800 + 16 * (16 + 1) <= b + sz.
Hypothesis GO_TS : exists b sz, GOBJ b sz /\ b <= 0x59f960 /\ 0x59f960 + 16 * (39 + 1) <= b + sz.
Hypothesis GO_HTTP : exists b sz, GOBJ b sz /\ b <= 0x59fc80 /\ 0x59fc80 + 16 * (32 + 1) <= b + sz.
Hypothesis GO_OCSP : exists b sz, GOBJ b sz /\ b <= 0x59ff20 /\ 0x59ff20 + 16 * (25 + 1) <= b + sz.
Hypothesis GO_UI : exists b sz, GOBJ b sz /\ b <= 0x5a0120 /\ 0x5a0120 + 16 * (13 + 1) <= b + sz.
Hypothesis GO_CMS : exists b sz, GOBJ b sz /\ b <= 0x5a0220 /\ 0x5a0220 + 16 * (102 + 1) <= b + sz.
Hypothesis GO_CRMF : exists b sz, GOBJ b sz /\ b <= 0x5a0a20 /\ 0x5a0a20 + 16 * (30 + 1) <= b + sz.
Hypothesis GO_CMP : exists b sz, GOBJ b sz /\ b <= 0x5a0c80 /\ 0x5a0c80 + 16 * (106 + 1) <= b + sz.
Hypothesis GO_CT : exists b sz, GOBJ b sz /\ b <= 0x5a14e0 /\ 0x5a14e0 + 16 * (17 + 1) <= b + sz.
Hypothesis GO_ESS : exists b sz, GOBJ b sz /\ b <= 0x5a1640 /\ 0x5a1640 + 16 * (9 + 1) <= b + sz.
Hypothesis GO_ASYNC : exists b sz, GOBJ b sz /\ b <= 0x5a1700 /\ 0x5a1700 + 16 * (4 + 1) <= b + sz.
Hypothesis GO_SM2 : exists b sz, GOBJ b sz /\ b <= 0x5a1780 /\ 0x5a1780 + 16 * (14 + 1) <= b + sz.
Hypothesis GO_OSSL_STORE : exists b sz, GOBJ b sz /\ b <= 0x5a18a0 /\ 0x5a18a0 + 16 * (25 + 1) <= b + sz.
Hypothesis GO_PROP : exists b sz, GOBJ b sz /\ b <= 0x5a1aa0 /\ 0x5a1aa0 + 16 * (11 + 1) <= b + sz.
Hypothesis GO_PROV : exists b sz, GOBJ b sz /\ b <= 0x5a1b80 /\ 0x5a1b80 + 16 * (160 + 1) <= b + sz.

Lemma TAB_libraries : els_table GOBJ ERR_TAB1 43.
Proof using GO_libraries.
  destruct GO_libraries as (base & size & owner & base_below & end_within).
  refine (els_table_ut GOBJ ERR_TAB1 43%nat base size owner base_below end_within _).
  exact els_okb_libraries.
Qed.
Lemma TAB_reasons : els_table GOBJ ERR_TAB2 39.
Proof using GO_reasons.
  destruct GO_reasons as (base & size & owner & base_below & end_within).
  refine (els_table_ut GOBJ ERR_TAB2 39%nat base size owner base_below end_within _).
  exact els_okb_reasons.
Qed.

Lemma TAB_BN : els_table GOBJ 0x59b500 22.
Proof using GO_BN.
  destruct GO_BN as (base & size & owner & base_below & end_within).
  refine (els_table_ut GOBJ 0x59b500 22%nat base size owner base_below end_within _).
  exact els_okb_BN.
Qed.
Lemma TAB_RSA : els_table GOBJ 0x59b6c0 81.
Proof using GO_RSA.
  destruct GO_RSA as (base & size & owner & base_below & end_within).
  refine (els_table_ut GOBJ 0x59b6c0 81%nat base size owner base_below end_within _).
  exact els_okb_RSA.
Qed.
Lemma TAB_DH : els_table GOBJ 0x59bd20 31.
Proof using GO_DH.
  destruct GO_DH as (base & size & owner & base_below & end_within).
  refine (els_table_ut GOBJ 0x59bd20 31%nat base size owner base_below end_within _).
  exact els_okb_DH.
Qed.
Lemma TAB_EVP : els_table GOBJ 0x59bfa0 125.
Proof using GO_EVP.
  destruct GO_EVP as (base & size & owner & base_below & end_within).
  refine (els_table_ut GOBJ 0x59bfa0 125%nat base size owner base_below end_within _).
  exact els_okb_EVP.
Qed.
Lemma TAB_BUF : els_table GOBJ 0xf88e0 0.
Proof. destruct GO_BUF as (b & sz & G & B1 & B2). exact (els_table_rom0 GOBJ 0xf88e0 b sz G B1 ltac:(lia) eq_refl ltac:(lia) ltac:(unfold SEGTOP_A; lia) buf_table_rom). Qed.
Lemma TAB_OBJ : els_table GOBJ 0x59c960 3.
Proof using GO_OBJ.
  destruct GO_OBJ as (base & size & owner & base_below & end_within).
  refine (els_table_ut GOBJ 0x59c960 3%nat base size owner base_below end_within _).
  exact els_okb_OBJ.
Qed.
Lemma TAB_PEM : els_table GOBJ 0x59c9c0 34.
Proof using GO_PEM.
  destruct GO_PEM as (base & size & owner & base_below & end_within).
  refine (els_table_ut GOBJ 0x59c9c0 34%nat base size owner base_below end_within _).
  exact els_okb_PEM.
Qed.
Lemma TAB_DSA : els_table GOBJ 0x59cc80 16.
Proof using GO_DSA.
  destruct GO_DSA as (base & size & owner & base_below & end_within).
  refine (els_table_ut GOBJ 0x59cc80 16%nat base size owner base_below end_within _).
  exact els_okb_DSA.
Qed.
Lemma TAB_X509 : els_table GOBJ 0x59cde0 47.
Proof using GO_X509.
  destruct GO_X509 as (base & size & owner & base_below & end_within).
  refine (els_table_ut GOBJ 0x59cde0 47%nat base size owner base_below end_within _).
  exact els_okb_X509.
Qed.
Lemma TAB_ASN1 : els_table GOBJ 0x59d1a0 117.
Proof using GO_ASN1.
  destruct GO_ASN1 as (base & size & owner & base_below & end_within).
  refine (els_table_ut GOBJ 0x59d1a0 117%nat base size owner base_below end_within _).
  exact els_okb_ASN1.
Qed.
Lemma TAB_CONF : els_table GOBJ 0x59dac0 27.
Proof using GO_CONF.
  destruct GO_CONF as (base & size & owner & base_below & end_within).
  refine (els_table_ut GOBJ 0x59dac0 27%nat base size owner base_below end_within _).
  exact els_okb_CONF.
Qed.
Lemma TAB_CRYPTO : els_table GOBJ 0x59dce0 31.
Proof using GO_CRYPTO.
  destruct GO_CRYPTO as (base & size & owner & base_below & end_within).
  refine (els_table_ut GOBJ 0x59dce0 31%nat base size owner base_below end_within _).
  exact els_okb_CRYPTO.
Qed.
Lemma TAB_COMP : els_table GOBJ 0x59df60 10.
Proof using GO_COMP.
  destruct GO_COMP as (base & size & owner & base_below & end_within).
  refine (els_table_ut GOBJ 0x59df60 10%nat base size owner base_below end_within _).
  exact els_okb_COMP.
Qed.
Lemma TAB_EC : els_table GOBJ 0x59e040 76.
Proof using GO_EC.
  destruct GO_EC as (base & size & owner & base_below & end_within).
  refine (els_table_ut GOBJ 0x59e040 76%nat base size owner base_below end_within _).
  exact els_okb_EC.
Qed.
Lemma TAB_BIO : els_table GOBJ 0x59e640 47.
Proof using GO_BIO.
  destruct GO_BIO as (base & size & owner & base_below & end_within).
  refine (els_table_ut GOBJ 0x59e640 47%nat base size owner base_below end_within _).
  exact els_okb_BIO.
Qed.
Lemma TAB_PKCS7 : els_table GOBJ 0x59ea00 38.
Proof using GO_PKCS7.
  destruct GO_PKCS7 as (base & size & owner & base_below & end_within).
  refine (els_table_ut GOBJ 0x59ea00 38%nat base size owner base_below end_within _).
  exact els_okb_PKCS7.
Qed.
Lemma TAB_X509V3 : els_table GOBJ 0x59ed00 73.
Proof using GO_X509V3.
  destruct GO_X509V3 as (base & size & owner & base_below & end_within).
  refine (els_table_ut GOBJ 0x59ed00 73%nat base size owner base_below end_within _).
  exact els_okb_X509V3.
Qed.
Lemma TAB_PKCS12 : els_table GOBJ 0x59f2c0 22.
Proof using GO_PKCS12.
  destruct GO_PKCS12 as (base & size & owner & base_below & end_within).
  refine (els_table_ut GOBJ 0x59f2c0 22%nat base size owner base_below end_within _).
  exact els_okb_PKCS12.
Qed.
Lemma TAB_RAND : els_table GOBJ 0x59f480 45.
Proof using GO_RAND.
  destruct GO_RAND as (base & size & owner & base_below & end_within).
  refine (els_table_ut GOBJ 0x59f480 45%nat base size owner base_below end_within _).
  exact els_okb_RAND.
Qed.
Lemma TAB_DSO : els_table GOBJ 0x59f800 16.
Proof using GO_DSO.
  destruct GO_DSO as (base & size & owner & base_below & end_within).
  refine (els_table_ut GOBJ 0x59f800 16%nat base size owner base_below end_within _).
  exact els_okb_DSO.
Qed.
Lemma TAB_TS : els_table GOBJ 0x59f960 39.
Proof using GO_TS.
  destruct GO_TS as (base & size & owner & base_below & end_within).
  refine (els_table_ut GOBJ 0x59f960 39%nat base size owner base_below end_within _).
  exact els_okb_TS.
Qed.
Lemma TAB_HTTP : els_table GOBJ 0x59fc80 32.
Proof using GO_HTTP.
  destruct GO_HTTP as (base & size & owner & base_below & end_within).
  refine (els_table_ut GOBJ 0x59fc80 32%nat base size owner base_below end_within _).
  exact els_okb_HTTP.
Qed.
Lemma TAB_OCSP : els_table GOBJ 0x59ff20 25.
Proof using GO_OCSP.
  destruct GO_OCSP as (base & size & owner & base_below & end_within).
  refine (els_table_ut GOBJ 0x59ff20 25%nat base size owner base_below end_within _).
  exact els_okb_OCSP.
Qed.
Lemma TAB_UI : els_table GOBJ 0x5a0120 13.
Proof using GO_UI.
  destruct GO_UI as (base & size & owner & base_below & end_within).
  refine (els_table_ut GOBJ 0x5a0120 13%nat base size owner base_below end_within _).
  exact els_okb_UI.
Qed.
Lemma TAB_CMS : els_table GOBJ 0x5a0220 102.
Proof using GO_CMS.
  destruct GO_CMS as (base & size & owner & base_below & end_within).
  refine (els_table_ut GOBJ 0x5a0220 102%nat base size owner base_below end_within _).
  exact els_okb_CMS.
Qed.
Lemma TAB_CRMF : els_table GOBJ 0x5a0a20 30.
Proof using GO_CRMF.
  destruct GO_CRMF as (base & size & owner & base_below & end_within).
  refine (els_table_ut GOBJ 0x5a0a20 30%nat base size owner base_below end_within _).
  exact els_okb_CRMF.
Qed.
Lemma TAB_CMP : els_table GOBJ 0x5a0c80 106.
Proof using GO_CMP.
  destruct GO_CMP as (base & size & owner & base_below & end_within).
  refine (els_table_ut GOBJ 0x5a0c80 106%nat base size owner base_below end_within _).
  exact els_okb_CMP.
Qed.
Lemma TAB_CT : els_table GOBJ 0x5a14e0 17.
Proof using GO_CT.
  destruct GO_CT as (base & size & owner & base_below & end_within).
  refine (els_table_ut GOBJ 0x5a14e0 17%nat base size owner base_below end_within _).
  exact els_okb_CT.
Qed.
Lemma TAB_ESS : els_table GOBJ 0x5a1640 9.
Proof using GO_ESS.
  destruct GO_ESS as (base & size & owner & base_below & end_within).
  refine (els_table_ut GOBJ 0x5a1640 9%nat base size owner base_below end_within _).
  exact els_okb_ESS.
Qed.
Lemma TAB_ASYNC : els_table GOBJ 0x5a1700 4.
Proof using GO_ASYNC.
  destruct GO_ASYNC as (base & size & owner & base_below & end_within).
  refine (els_table_ut GOBJ 0x5a1700 4%nat base size owner base_below end_within _).
  exact els_okb_ASYNC.
Qed.
Lemma TAB_SM2 : els_table GOBJ 0x5a1780 14.
Proof using GO_SM2.
  destruct GO_SM2 as (base & size & owner & base_below & end_within).
  refine (els_table_ut GOBJ 0x5a1780 14%nat base size owner base_below end_within _).
  exact els_okb_SM2.
Qed.
Lemma TAB_OSSL_STORE : els_table GOBJ 0x5a18a0 25.
Proof using GO_OSSL_STORE.
  destruct GO_OSSL_STORE as (base & size & owner & base_below & end_within).
  refine (els_table_ut GOBJ 0x5a18a0 25%nat base size owner base_below end_within _).
  exact els_okb_OSSL_STORE.
Qed.
Lemma TAB_PROP : els_table GOBJ 0x5a1aa0 11.
Proof using GO_PROP.
  destruct GO_PROP as (base & size & owner & base_below & end_within).
  refine (els_table_ut GOBJ 0x5a1aa0 11%nat base size owner base_below end_within _).
  exact els_okb_PROP.
Qed.
Lemma TAB_PROV : els_table GOBJ 0x5a1b80 160.
Proof using GO_PROV.
  destruct GO_PROV as (base & size & owner & base_below & end_within).
  refine (els_table_ut GOBJ 0x5a1b80 160%nat base size owner base_below end_within _).
  exact els_okb_PROV.
Qed.

Section Run.
Variable Σ0 : rts RT.
Variable PMc : Model -> Prop.
Variables ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable m0 : mem.
Variable lo : Z.
Variable outer : list Z.
Variables canary od oldcb : word.
Variable T : list event -> Prop.
Let usp := bv_unsigned sp.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis ART00 : ART RT Σ0 m0.
Hypothesis CALL : call_ok RT Σ0 m0 sp lo.
Hypothesis HSTK : lo + RT_STACK + 0x2f0 <= usp.
Hypothesis CTX : cg_ctx (rt_cg RT Σ0) e_crypto_strs (bv_unsigned ra :: outer).
Hypothesis CGH : cg_has (rt_cg RT Σ0) CR_SITES CR_CALLS.
Hypothesis Hfr : (length (rt_frames RT Σ0) < FRAMES_MAX)%nat.
Hypothesis Hlen : Z.of_nat (length (rt_live RT Σ0)) + 4324 < LIVE_MAX.
Hypothesis Hcr : 36 <= rt_credit RT Σ0.
Hypothesis POS : Forall (fun x => 0 < snd x) (rt_live RT Σ0).

(* [comment removed for export] *)
Definition CRI (site bnd itb crd : Z) (c : config) : Prop :=
  exists (Σ' : rts RT) (pk lh B : Z) (L' : list (Z * Z)) (g' : lh_geo) (bks' : list (list (bptr * Z))) (lb' : byte),
    ASTA RT Σ' PMc (fun ms => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem),
        ms = MS (mkR (Z_to_bv 64 site) (Z_to_bv 64 (bv_unsigned sp + -16)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp s1 (Z_to_bv 64 1)
                     a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F' (Z_to_bv 64 site) fc' None m' (seg_rom asegs)
        /\ ART RT Σ' m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp + -16)
        /\ rw_cells asegs m' (bv_unsigned sp + -16) [C8 s0; C8 ra] /\ uw_chain m' sp s0 outer
        /\ rt_pres_fp (rt_live RT Σ0) (rt_frames RT Σ0) (bv_unsigned sp) (EFIRST_W pk) m0 m'
        /\ cl_env m' lb' canary
        /\ rw_cells asegs m' G_IC_STOPPED [C1 (Z_to_bv 8 0)] /\ rw_cells asegs m' G_IC_OPTSDONE [C8 od]
        /\ rw_cells asegs m' G_IC_BASE_ONCE [C4 (Z_to_bv 64 2)] /\ rw_cells asegs m' G_IC_BASE_RET [C4 (Z_to_bv 64 1)]
        /\ err_statics m' pk lh /\ rw_cells asegs m' G_CANCELBUF [C8 oldcb] /\ rw_cells asegs m' pk (mutex_cells z64 z64)
        /\ lh_repE GOBJ m' L' lh B g' bks') c
    /\ Permutation (rt_live RT Σ') (L' ++ (pk, 40) :: rt_live RT Σ0)
    /\ Z.of_nat (length L') <= bnd /\ 0 <= g_items g' <= itb
    /\ rt_frames RT Σ' = rt_frames RT Σ0 /\ rt_sp0 RT Σ' = rt_sp0 RT Σ0
    /\ rt_credit RT Σ0 - crd <= rt_credit RT Σ' /\ rt_cg RT Σ' = rt_cg RT Σ0
    /\ 0 < pk /\ pk mod 16 = 0 /\ pk + 40 < USTACK_TOP /\ 0x10007fff8000 <= pk
    /\ (forall x, aclient (rt_live RT Σ0) (rt_frames RT Σ0) (bv_unsigned sp + -16) x -> ~ (pk <= x < pk + 40)).

(* [comment removed for export] *)
Lemma cr_step : forall (E R2 TAB n Rp Rk bnd itb crd bnd' itb' crd' : Z),
  stub_stmt RT GOBJ E TAB R2 n -> els_table GOBJ TAB n -> 0 <= n -> ecw_spec Rp Rk E ->
  memP (Rk, e_crypto_strs) CR_SITES = true -> memP (Rk, E) CR_CALLS = true -> inclP (STUB_SITES E R2) CR_SITES = true -> inclP (STUB_CALLS R2) CR_CALLS = true ->
  0 <= Rk < 2 ^ 32 -> Rk mod 2 = 0 ->
  bnd + 82 + n <= bnd' -> itb + 82 + n <= itb' -> crd + 1 <= crd' -> 0 <= bnd -> bnd' <= 4320 -> itb' <= 4318 -> 0 <= crd -> crd' <= 36 ->
  forall c, CRI Rp bnd itb crd c -> (forall c', CRI Rk bnd' itb' crd' c' -> realizes asegs c' T) -> realizes asegs c T.
Proof using AF GO_libraries GO_reasons FDO MST ART00 CALL HSTK CTX CGH Hfr Hlen Hcr POS.
  intros E R2 TAB n Rp Rk bnd itb crd bnd' itb' crd' callee table n_nonneg walk
    site_in call_in sites_in calls_in rk_range rk_even
    bnd_step itb_step crd_step bnd_pos bnd_cap itb_cap crd_pos crd_cap c here next.
  destruct here as (Σ1 & pk & lh & B & L1 & g1 & bks1 & lb1 & at1 & perm1 & len1 & items1 & frames1 & sp01 & credit1 & cg1 & pk_pos & pk_al & pk_top & pk_high & pk_apart).
  destruct (ASTA_unpack RT Σ1 PMc _ c at1) as (ms1 & (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F1 & fc1 & m1 & -> & art1 & inv1 & stk1 & frame1 & chain1 & pres1 & env1 & stp1 & od1 & once1 & bret1 & errs1 & cbuf1 & mtx1 & rep1) & now1).
  clear at1.
  destruct CALL as (stk0 & lo_win & lo_stack & sp_top & sp_align).
  pose proof (af_sp0_win RT AF Σ0 m0 ART00) as sp0_high.
  assert (lo_high : 0x10007fff8000 <= lo) by (unfold STACK_WIN in *; lia).
  assert (lo_room : lo <= bv_unsigned sp - 16) by (unfold usp, RT_STACK in *; lia).
  assert (sp_cap : bv_unsigned sp <= 2 ^ 47) by (unfold USTACK_TOP in *; lia).
  assert (callee_sp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp + -16) by (apply unsigned_lit; lia).
  assert (rk_lit : bv_unsigned (Z_to_bv 64 Rk) = Rk) by (apply unsigned_lit; lia).
  pose proof (walk sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F1 fc1 m1 lo stk1 lo_high lo_room sp_cap inv1) as run1.
  refine (cps_realizes asegs _ _ T c (asta_evt' RT AF Σ1 PMc _ _ MST _) now1 _); [intros ms <-; exact run1|].
  intros c2 at2. clear run1 now1.
  refine (callee Σ1 PMc (Z_to_bv 64 Rk) (Z_to_bv 64 (bv_unsigned sp + -16)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp s1 (Z_to_bv 64 1)
            a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F1 fc1 m1 lo (bv_unsigned ra :: outer) lb1 canary
            L1 ((pk, 40) :: rt_live RT Σ0) lh B g1 bks1 pk 43 39 FDO MST eq_refl art1 inv1 _ _ _ _ _ _ _ _ env1 errs1 (or_introl eq_refl) _ mtx1 rep1 perm1 _
            TAB_libraries TAB_reasons table _ _ n_nonneg _ T c2 _ _).

  - unfold call_ok. rewrite callee_sp. rewrite sp01.
    refine (conj stk1 (conj lo_win (conj _ (conj _ _)))); [unfold RT_STACK in *; lia | lia |].
    rewrite Zplus_mod, sp_align. reflexivity.
  - rewrite callee_sp. unfold usp, RT_STACK in *. lia.
  - rewrite cg1, rk_lit.
    apply (cg_ctx_call _ e_crypto_strs E Rk _ CTX).
    + exact (cg_has_site _ _ _ _ _ CGH (memP_true _ _ site_in)).
    + exact (cg_has_call _ _ _ _ _ CGH (memP_true _ _ call_in)).
  - cbn [uw_chain]. rewrite callee_sp.
    split; [lia|]. split; [exact sp_top|]. exists s0. split; [|exact chain1].
    rewrite (Z_to_bv_bv_unsigned ra). replace (bv_unsigned sp - 16) with (bv_unsigned sp + -16) by lia. exact frame1.
  - rewrite cg1. exact (cg_has_weaken _ _ _ _ _ CGH sites_in calls_in).
  - rewrite frames1. exact Hfr.
  - rewrite (Permutation_length perm1), length_app. cbn [length]. lia.
  - lia.
  - clear - pk_al. Z.div_mod_to_equations. lia.
  - constructor; [cbn; lia | exact POS].
  - lia.
  - lia.
  - unfold LH_KMAX. lia.
  - refine (ASTA_conseq RT Σ1 PMc _ _ c2 at2 _). intros ms ->. reflexivity.
  - intros c3 (Σ2 & L2 & B2 & g2 & bks2 & lb2 & at3 & perm2 & len2 & items2 & frames2 & sp02 & credit2 & cg2).
    apply next. unfold CRI.
    exists Σ2, pk, lh, B2, L2, g2, bks2, lb2.
    refine (conj _ (conj perm2 _)).
    2: { split; [lia|]. split; [lia|]. split; [congruence|]. split; [congruence|]. split; [lia|]. split; [congruence|].
         exact (conj pk_pos (conj pk_al (conj pk_top (conj pk_high pk_apart)))). }
    refine (ASTA_conseq RT Σ2 PMc _ _ c3 at3 _).
    intros ms (m2 & (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->) & (art2 & inv2 & stk2) & pres2 & env2 & rep2 & mtx2 & errs2).
    rewrite callee_sp in stk2, pres2.
    assert (kept : forall a : word, aclient (rt_live RT Σ0) (rt_frames RT Σ0) (bv_unsigned sp + -16) (bv_unsigned a) ->
                    ~ (G_ALLOW_CUST <= bv_unsigned a < G_ALLOW_CUST + 1) -> m2 a = m1 a).
    { intros a client not_flag. apply pres2.
      - apply (aclient_mono _ _ _ _ _ _ _ client); [intros e e_in; right; exact e_in | rewrite frames1; tauto | lia].
      - cbn [outside]. pose proof (pk_apart _ client). split; [exact not_flag|]. split; [lia | exact I]. }
    assert (stays : forall A cs, rw_cells asegs m1 A cs ->
                (forall x, A <= x < A + Z.of_nat (cells_size cs) ->
                   aclient (rt_live RT Σ0) (rt_frames RT Σ0) (bv_unsigned sp + -16) x /\ ~ (G_ALLOW_CUST <= x < G_ALLOW_CUST + 1)) ->
                rw_cells asegs m2 A cs).
    { intros A cs held span. apply (rw_cells_agree_nw asegs m1 m2 A cs held). intros a a_in. destruct (span _ a_in) as [client flag]. exact (kept a client flag). }
    exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, F2, fc2, m2.
    split. { rewrite (ret_pc_even Rk) by lia. reflexivity. }
    split; [exact art2|]. split; [exact inv2|]. split; [exact stk2|].
    split.
    { apply (stays _ _ frame1). intros x x_in. cbn [cells_size csize Nat.add] in x_in.
      split; [left; unfold USTACK_TOP in *; lia | unfold G_ALLOW_CUST; lia]. }
    split.
    { apply (uw_chain_agree outer m1 m2 sp s0 chain1). intros a a_in. cbv beta in a_in.
      apply kept; [left; lia | unfold G_ALLOW_CUST; lia]. }
    split.
    { intros a client outside_w. pose proof outside_w as flag. cbn [EFIRST_W outside] in flag. destruct flag as [flag _].
      rewrite (kept a ltac:(apply (aclient_mono _ _ _ _ _ _ _ client); [tauto | tauto | lia]) flag).
      exact (pres1 a client outside_w). }
    split; [exact env2|].
    split.
    { apply (stays _ _ stp1). intros x x_in. cbn in x_in. split; [right; left; apply client_static_intro|]; unfold G_ALLOW_CUST, G_IC_STOPPED in *; lia. }
    split.
    { apply (stays _ _ od1). intros x x_in. cbn in x_in. split; [right; left; apply client_static_intro|]; unfold G_ALLOW_CUST, G_IC_OPTSDONE in *; lia. }
    split.
    { apply (stays _ _ once1). intros x x_in. cbn in x_in. split; [right; left; apply client_static_intro|]; unfold G_ALLOW_CUST, G_IC_BASE_ONCE in *; lia. }
    split.
    { apply (stays _ _ bret1). intros x x_in. cbn in x_in. split; [right; left; apply client_static_intro|]; unfold G_ALLOW_CUST, G_IC_BASE_RET in *; lia. }
    split; [exact errs2|].
    split.
    { apply (stays _ _ cbuf1). intros x x_in. cbn in x_in. split; [right; left; apply client_static_intro|]; unfold G_ALLOW_CUST, G_CANCELBUF in *; lia. }
    exact (conj mtx2 rep2).
Qed.

(* [comment removed for export] *)
Lemma cr_step0 : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (lb : byte) (lk0 h0 f0 : word) c,
  mem_inv asegs m0 -> uw_chain m0 sp s0 outer -> cl_env m0 lb canary ->
  rw_cells asegs m0 G_IC_STOPPED [C1 (Z_to_bv 8 0)] -> rw_cells asegs m0 G_IC_OPTSDONE [C8 od] -> rw_cells asegs m0 G_IC_BASE_ONCE [C4 (Z_to_bv 64 2)] -> rw_cells asegs m0 G_IC_BASE_RET [C4 (Z_to_bv 64 1)] ->
  rw_cells asegs m0 G_ERR_ONCE [C4 z64] -> rw_cells asegs m0 G_ERR_LOCK [C8 lk0] -> rw_cells asegs m0 G_ERR_HASH [C8 h0] -> rw_cells asegs m0 G_ERR_FLAG [C4 f0] ->
  rw_cells asegs m0 G_CANCELBUF [C8 oldcb] ->
  ASTA RT Σ0 PMc (eq (entry_st ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_crypto_strs m0)) c ->
  (forall c', CRI 0x511118 84 82 2 c' -> realizes asegs c' T) -> realizes asegs c T.
Proof using AF C_EFIRST GO_libraries GO_reasons FDO MST ART00 CALL HSTK CTX CGH Hfr Hlen Hcr POS.
  intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc lb lk0 h0 f0 c
    inv0 chain0 env0 stp0 od0 once0 bret0 eonce0 elock0 ehash0 eflag0 cbuf0 entry next.
  destruct CALL as (stk0 & lo_win & lo_stack & sp_top & sp_align).
  pose proof (af_sp0_win RT AF Σ0 m0 ART00) as sp0_high.
  assert (lo_high : 0x10007fff8000 <= lo) by (unfold STACK_WIN in *; lia).
  assert (lo_room : lo <= bv_unsigned sp - 16) by (unfold usp, RT_STACK in *; lia).
  assert (sp_cap : bv_unsigned sp <= 2 ^ 47) by (unfold USTACK_TOP in *; lia).
  assert (callee_sp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp + -16) by (apply unsigned_lit; lia).
  pose proof (ec_w0 ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m0 lo stk0 lo_high lo_room sp_cap inv0) as run0.
  refine (cps_realizes asegs _ _ T c (asta_evt' RT AF Σ0 PMc _ _ MST _) entry _); [intros ms <-; exact run0|].
  intros c1 at1. clear run0 entry.
  destruct (ASTA_unpack RT Σ0 PMc _ c1 at1) as (ms1 & (m1 & -> & munch1 & mono1 & inv1 & frame1 & stk1) & now1). clear at1.
  pose proof (cl_seg_ART RT AF Σ0 m0 m1 (bv_unsigned sp) 16 [] ART00 ltac:(unfold STACK_WIN in *; lia) ltac:(lia) munch1
                ltac:(intros x x_out; exfalso; apply x_out; exact I) mono1) as art1.
  pose proof (cl_seg_pres RT AF Σ0 m0 m1 (bv_unsigned sp) 16 [] ART00 ltac:(unfold STACK_WIN in *; lia) ltac:(lia) munch1) as pres01.
  assert (above1 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m0 m1).
  { intros a a_in. apply munch1. cbn [outside]. split; [lia | exact I]. }
  assert (below : forall A cs, rw_cells asegs m0 A cs -> A + Z.of_nat (cells_size cs) <= bv_unsigned sp - 16 -> rw_cells asegs m1 A cs).
  { intros A cs held fits. apply (rw_cells_agree_nw asegs m0 m1 A cs held). intros a a_in. apply munch1. cbn [outside]. split; [lia | exact I]. }
  pose proof (cl_env_seg [(bv_unsigned sp - 16, bv_unsigned sp)] m0 m1 lb canary env0 munch1 ltac:(cl_fp_lia)) as env1.
  refine (C_EFIRST Σ0 PMc (Z_to_bv 64 0x511118) (Z_to_bv 64 (bv_unsigned sp + -16)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp s1 a0 a1 a2 a3 a4 a5 a6 a7
            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo (bv_unsigned ra :: outer) lb canary od lk0 h0 f0 oldcb 43 39
            FDO MST eq_refl art1 inv1 _ _ _ _ _ Hfr _ _ POS env1 _ _ _ _ _ _ _ _ _ TAB_libraries TAB_reasons _ _ _ T c1 now1 _).

  - unfold call_ok. rewrite callee_sp.
    refine (conj stk1 (conj lo_win (conj _ (conj _ _)))); [unfold RT_STACK in *; lia | lia |].
    rewrite Zplus_mod, sp_align. reflexivity.
  - rewrite callee_sp. unfold usp, RT_STACK in *. lia.
  - rewrite (unsigned_lit 0x511118) by lia.
    apply (cg_ctx_call _ e_crypto_strs e_err_strings 0x511118 _ CTX).
    + apply (cg_has_site _ _ _ _ _ CGH). vm_compute. left. reflexivity.
    + apply (cg_has_call _ _ _ _ _ CGH). vm_compute. left. reflexivity.
  - cbn [uw_chain]. rewrite callee_sp.
    split; [lia|]. split; [exact sp_top|]. exists s0. split.
    + rewrite (Z_to_bv_bv_unsigned ra). replace (bv_unsigned sp - 16) with (bv_unsigned sp + -16) by lia. exact frame1.
    + exact (uw_chain_agree outer m0 m1 sp s0 chain0 above1).
  - apply (cg_has_weaken _ _ _ _ _ CGH); vm_compute; reflexivity.
  - lia.
  - lia.
  - apply (below _ _ stp0). cbn. unfold G_IC_STOPPED. lia.
  - apply (below _ _ od0). cbn. unfold G_IC_OPTSDONE. lia.
  - apply (below _ _ once0). cbn. unfold G_IC_BASE_ONCE. lia.
  - apply (below _ _ bret0). cbn. unfold G_IC_BASE_RET. lia.
  - apply (below _ _ eonce0). cbn. unfold G_ERR_ONCE. lia.
  - apply (below _ _ elock0). cbn. unfold G_ERR_LOCK. lia.
  - apply (below _ _ ehash0). cbn. unfold G_ERR_HASH. lia.
  - apply (below _ _ eflag0). cbn. unfold G_ERR_FLAG. lia.
  - apply (below _ _ cbuf0). cbn. unfold G_CANCELBUF. lia.
  - lia.
  - lia.
  - unfold LH_KMAX. lia.
  - intros c2 (Σ1 & pk & lh & B & L1 & g1 & bks1 & lb1 & at2 & perm1 & len1 & items1 & frames1 & sp01 & credit1 & cg1 & pk_pos & pk_al & pk_top & pk_high & pk_apart).
    rewrite callee_sp in pk_apart.
    apply next. unfold CRI. exists Σ1, pk, lh, B, L1, g1, bks1, lb1.
    refine (conj _ (conj perm1 _)).
    2: { split; [lia|]. split; [lia|]. split; [exact frames1|]. split; [exact sp01|]. split; [lia|]. split; [exact cg1|].
         exact (conj pk_pos (conj pk_al (conj pk_top (conj pk_high pk_apart)))). }
    refine (ASTA_conseq RT Σ1 PMc _ _ c2 at2 _).
    intros ms (m2 & (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->) & (art2 & inv2 & stk2) & pres12 & env2
                  & stp2 & od2 & once2 & bret2 & errs2 & cbuf2 & mtx2 & rep2).
    rewrite callee_sp in stk2, pres12.
    exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, F2, fc2, m2.
    split. { rewrite (ret_pc_even 0x511118) by lia. reflexivity. }
    split; [exact art2|]. split; [exact inv2|]. split; [exact stk2|].
    split.
    { apply (rw_cells_agree_nw asegs m1 m2 _ _ frame1). intros a a_in. cbn [cells_size csize Nat.add] in a_in. cbv beta in a_in.
      apply pres12; [left; unfold USTACK_TOP in *; lia|].
      cbn [EFIRST_W outside]. unfold G_ALLOW_CUST, G_ERR_ONCE, G_ERR_LOCK, G_ERR_HASH, G_ERR_FLAG, G_CANCELBUF. repeat split; try lia. }
    split.
    { apply (uw_chain_agree outer m0 m2 sp s0 chain0). intros a a_in. cbv beta in a_in.
      rewrite (pres12 a ltac:(left; lia)); [exact (above1 a a_in)|].
      cbn [EFIRST_W outside]. unfold G_ALLOW_CUST, G_ERR_ONCE, G_ERR_LOCK, G_ERR_HASH, G_ERR_FLAG, G_CANCELBUF. repeat split; try lia. }
    split.
    { intros a client outside_w.
      rewrite (pres12 a ltac:(apply (aclient_mono _ _ _ _ _ _ _ client); [tauto | tauto | lia]) outside_w).
      exact (pres01 a client I). }
    exact (conj env2 (conj stp2 (conj od2 (conj once2 (conj bret2 (conj errs2 (conj cbuf2 (conj mtx2 rep2)))))))).
Qed.

(* [comment removed for export] *)
Lemma cr_exit : forall (Hk0 : forall c', (exists (Σ' : rts RT) (pk lh B : Z) (L' : list (Z * Z)) (g' : lh_geo) (bks' : list (list (bptr * Z))) (lb' : byte),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) m' ms
           /\ rt_after_f RT Σ' usp lo m0 m'
           /\ rt_pres_fp (rt_live RT Σ0) (rt_frames RT Σ0) usp (EFIRST_W pk) m0 m'
           /\ cl_env m' lb' canary
           /\ rw_cells asegs m' G_IC_STOPPED [C1 (Z_to_bv 8 0)] /\ rw_cells asegs m' G_IC_OPTSDONE [C8 od] /\ rw_cells asegs m' G_IC_BASE_ONCE [C4 (Z_to_bv 64 2)] /\ rw_cells asegs m' G_IC_BASE_RET [C4 (Z_to_bv 64 1)]
           /\ err_statics m' pk lh /\ rw_cells asegs m' G_CANCELBUF [C8 oldcb] /\ rw_cells asegs m' pk (mutex_cells z64 z64) /\ lh_repE GOBJ m' L' lh B g' bks') c'
       /\ Permutation (rt_live RT Σ') (L' ++ (pk, 40) :: rt_live RT Σ0) /\ Z.of_nat (length L') <= 4320 /\ 0 <= g_items g' <= 4318
       /\ rt_frames RT Σ' = rt_frames RT Σ0 /\ rt_sp0 RT Σ' = rt_sp0 RT Σ0 /\ rt_credit RT Σ0 - 36 <= rt_credit RT Σ' /\ rt_cg RT Σ' = rt_cg RT Σ0
       /\ 0 < pk /\ pk mod 16 = 0 /\ pk + 40 < USTACK_TOP) -> realizes asegs c' T) c,
  CRI 0x511228 4320 4318 36 c -> realizes asegs c T.
Proof using AF MST ART00 CALL HSTK Hfr.
  intros done c here.
  destruct here as (Σ1 & pk & lh & B & L1 & g1 & bks1 & lb1 & at1 & perm1 & len1 & items1 & frames1 & sp01 & credit1 & cg1 & pk_pos & pk_al & pk_top & _ & pk_apart).
  destruct (ASTA_unpack RT Σ1 PMc _ c at1) as (ms1 & (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F1 & fc1 & m1 & -> & art1 & inv1 & stk1 & frame1 & chain1 & pres1 & env1 & stp1 & od1 & once1 & bret1 & errs1 & cbuf1 & mtx1 & rep1) & now1).
  clear at1.
  destruct CALL as (stk0 & lo_win & lo_stack & sp_top & sp_align).
  pose proof (af_sp0_win RT AF Σ0 m0 ART00) as sp0_high.
  assert (lo_high : 0x10007fff8000 <= lo) by (unfold STACK_WIN in *; lia).
  assert (lo_room : lo <= bv_unsigned sp - 16) by (unfold usp, RT_STACK in *; lia).
  assert (sp_cap : bv_unsigned sp <= 2 ^ 47) by (unfold USTACK_TOP in *; lia).
  pose proof (ec_wx sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F1 fc1 m1 lo ra s0 frame1 stk1 lo_high lo_room sp_cap inv1) as run1.
  refine (cps_realizes asegs _ _ T c (asta_evt' RT AF Σ1 PMc _ _ MST _) now1 _); [intros ms <-; exact run1|].
  intros c2 at2. apply done.
  exists Σ1, pk, lh, B, L1, g1, bks1, lb1.
  split.
  - refine (ASTA_conseq RT Σ1 PMc _ _ c2 at2 _). intros ms (-> & stk2).
    exists m1. split; [exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, F1, fc1; reflexivity|].
    exact (conj (conj art1 (conj inv1 stk2)) (conj pres1 (conj env1 (conj stp1 (conj od1 (conj once1 (conj bret1 (conj errs1 (conj cbuf1 (conj mtx1 rep1)))))))))).
  - exact (conj perm1 (conj len1 (conj items1 (conj frames1 (conj sp01 (conj credit1 (conj cg1 (conj pk_pos (conj pk_al pk_top))))))))).
Qed.
End Run.

Local Notation IP := (ltac:(vm_compute; reflexivity)) (only parsing).
Local Notation L := (ltac:(lia)) (only parsing).

(* [comment removed for export] *)
Definition crypto_strs_stmt : Prop :=
  forall (Σ : rts RT) (PMc : Model -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary od lk0 h0 f0 oldcb : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x2f0 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_crypto_strs (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> cg_has (rt_cg RT Σ) CR_SITES CR_CALLS ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> Z.of_nat (length (rt_live RT Σ)) + 4324 < LIVE_MAX -> 36 <= rt_credit RT Σ ->
  Forall (fun x => 0 < snd x) (rt_live RT Σ) -> cl_env m lb canary ->
  rw_cells asegs m G_IC_STOPPED [C1 (Z_to_bv 8 0)] -> rw_cells asegs m G_IC_OPTSDONE [C8 od] -> rw_cells asegs m G_IC_BASE_ONCE [C4 (Z_to_bv 64 2)] -> rw_cells asegs m G_IC_BASE_RET [C4 (Z_to_bv 64 1)] ->
  rw_cells asegs m G_ERR_ONCE [C4 z64] -> rw_cells asegs m G_ERR_LOCK [C8 lk0] -> rw_cells asegs m G_ERR_HASH [C8 h0] -> rw_cells asegs m G_ERR_FLAG [C4 f0] ->
  rw_cells asegs m G_CANCELBUF [C8 oldcb] ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_crypto_strs m)))
    (fun c => exists (Σ' : rts RT) (pk lh B : Z) (L' : list (Z * Z)) (g' : lh_geo) (bks' : list (list (bptr * Z))) (lb' : byte),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) m' ms
           /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (EFIRST_W pk) m m'
           /\ cl_env m' lb' canary
           /\ rw_cells asegs m' G_IC_STOPPED [C1 (Z_to_bv 8 0)] /\ rw_cells asegs m' G_IC_OPTSDONE [C8 od] /\ rw_cells asegs m' G_IC_BASE_ONCE [C4 (Z_to_bv 64 2)] /\ rw_cells asegs m' G_IC_BASE_RET [C4 (Z_to_bv 64 1)]
           /\ err_statics m' pk lh /\ rw_cells asegs m' G_CANCELBUF [C8 oldcb] /\ rw_cells asegs m' pk (mutex_cells z64 z64) /\ lh_repE GOBJ m' L' lh B g' bks') c
       /\ Permutation (rt_live RT Σ') (L' ++ (pk, 40) :: rt_live RT Σ) /\ Z.of_nat (length L') <= 4320 /\ 0 <= g_items g' <= 4318
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 36 <= rt_credit RT Σ' /\ rt_cg RT Σ' = rt_cg RT Σ
       /\ 0 < pk /\ pk mod 16 = 0 /\ pk + 40 < USTACK_TOP).

Theorem crypto_strs_cps : crypto_strs_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary od lk0 h0 f0 oldcb
    FDO MST -> ART0 MI0 CALL HSTK CTX UWC CGH Hfr Hlen Hcr POS ENV STP OD ONCE BRET ONC LKC LHC FLC CBC.
  intros T c HA Hk.
  eapply (cr_step0 Σ PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo outer canary od oldcb T FDO MST ART0 CALL HSTK CTX CGH Hfr Hlen Hcr POS
            t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc lb lk0 h0 f0 c MI0 UWC ENV STP OD ONCE BRET ONC LKC LHC FLC CBC HA).
  intros c0 H0.
  pose proof (cr_step Σ PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo outer canary od oldcb T FDO MST ART0 CALL HSTK CTX CGH Hfr Hlen Hcr POS) as STEP.
  apply (STEP 0x51123c 0x511270 0x59b500 22 0x511118 0x511120 84 82 2 188 186 3 (stub_BN RT GOBJ AF AFP C_ERS C_ELC) TAB_BN ltac:(lia) ec_w1 IP IP IP IP L L L L L L L L L L c0 H0); clear H0; intros c1 H1.
  apply (STEP 0x511284 0x5112b8 0x59b6c0 81 0x511120 0x511128 188 186 3 351 349 4 (stub_RSA RT GOBJ AF AFP C_ERS C_ELC) TAB_RSA ltac:(lia) ec_w2 IP IP IP IP L L L L L L L L L L c1 H1); clear H1; intros c2 H2.
  apply (STEP 0x5112cc 0x511300 0x59bd20 31 0x511128 0x511130 351 349 4 464 462 5 (stub_DH RT GOBJ AF AFP C_ERS C_ELC) TAB_DH ltac:(lia) ec_w3 IP IP IP IP L L L L L L L L L L c2 H2); clear H2; intros c3 H3.
  apply (STEP 0x511314 0x511348 0x59bfa0 125 0x511130 0x511138 464 462 5 671 669 6 (stub_EVP RT GOBJ AF AFP C_ERS C_ELC) TAB_EVP ltac:(lia) ec_w4 IP IP IP IP L L L L L L L L L L c3 H3); clear H3; intros c4 H4.
  apply (STEP 0x51135c 0x51138c 0xf88e0 0 0x511138 0x511140 671 669 6 753 751 7 (stub_BUF RT GOBJ AF AFP C_ERS C_ELC) TAB_BUF ltac:(lia) ec_w5 IP IP IP IP L L L L L L L L L L c4 H4); clear H4; intros c5 H5.
  apply (STEP 0x5113a0 0x5113d4 0x59c960 3 0x511140 0x511148 753 751 7 838 836 8 (stub_OBJ RT GOBJ AF AFP C_ERS C_ELC) TAB_OBJ ltac:(lia) ec_w6 IP IP IP IP L L L L L L L L L L c5 H5); clear H5; intros c6 H6.
  apply (STEP 0x5113e8 0x51141c 0x59c9c0 34 0x511148 0x511150 838 836 8 954 952 9 (stub_PEM RT GOBJ AF AFP C_ERS C_ELC) TAB_PEM ltac:(lia) ec_w7 IP IP IP IP L L L L L L L L L L c6 H6); clear H6; intros c7 H7.
  apply (STEP 0x511430 0x511464 0x59cc80 16 0x511150 0x511158 954 952 9 1052 1050 10 (stub_DSA RT GOBJ AF AFP C_ERS C_ELC) TAB_DSA ltac:(lia) ec_w8 IP IP IP IP L L L L L L L L L L c7 H7); clear H7; intros c8 H8.
  apply (STEP 0x511478 0x5114ac 0x59cde0 47 0x511158 0x511160 1052 1050 10 1181 1179 11 (stub_X509 RT GOBJ AF AFP C_ERS C_ELC) TAB_X509 ltac:(lia) ec_w9 IP IP IP IP L L L L L L L L L L c8 H8); clear H8; intros c9 H9.
  apply (STEP 0x5114c0 0x5114f4 0x59d1a0 117 0x511160 0x511168 1181 1179 11 1380 1378 12 (stub_ASN1 RT GOBJ AF AFP C_ERS C_ELC) TAB_ASN1 ltac:(lia) ec_w10 IP IP IP IP L L L L L L L L L L c9 H9); clear H9; intros c10 H10.
  apply (STEP 0x511508 0x51153c 0x59dac0 27 0x511168 0x511170 1380 1378 12 1489 1487 13 (stub_CONF RT GOBJ AF AFP C_ERS C_ELC) TAB_CONF ltac:(lia) ec_w11 IP IP IP IP L L L L L L L L L L c10 H10); clear H10; intros c11 H11.
  apply (STEP 0x511550 0x511584 0x59dce0 31 0x511170 0x511178 1489 1487 13 1602 1600 14 (stub_CRYPTO RT GOBJ AF AFP C_ERS C_ELC) TAB_CRYPTO ltac:(lia) ec_w12 IP IP IP IP L L L L L L L L L L c11 H11); clear H11; intros c12 H12.
  apply (STEP 0x511598 0x5115cc 0x59df60 10 0x511178 0x511180 1602 1600 14 1694 1692 15 (stub_COMP RT GOBJ AF AFP C_ERS C_ELC) TAB_COMP ltac:(lia) ec_w13 IP IP IP IP L L L L L L L L L L c12 H12); clear H12; intros c13 H13.
  apply (STEP 0x5115e0 0x511614 0x59e040 76 0x511180 0x511188 1694 1692 15 1852 1850 16 (stub_EC RT GOBJ AF AFP C_ERS C_ELC) TAB_EC ltac:(lia) ec_w14 IP IP IP IP L L L L L L L L L L c13 H13); clear H13; intros c14 H14.
  apply (STEP 0x511628 0x51165c 0x59e640 47 0x511188 0x511190 1852 1850 16 1981 1979 17 (stub_BIO RT GOBJ AF AFP C_ERS C_ELC) TAB_BIO ltac:(lia) ec_w15 IP IP IP IP L L L L L L L L L L c14 H14); clear H14; intros c15 H15.
  apply (STEP 0x511670 0x5116a4 0x59ea00 38 0x511190 0x511198 1981 1979 17 2101 2099 18 (stub_PKCS7 RT GOBJ AF AFP C_ERS C_ELC) TAB_PKCS7 ltac:(lia) ec_w16 IP IP IP IP L L L L L L L L L L c15 H15); clear H15; intros c16 H16.
  apply (STEP 0x5116b8 0x5116ec 0x59ed00 73 0x511198 0x5111a0 2101 2099 18 2256 2254 19 (stub_X509V3 RT GOBJ AF AFP C_ERS C_ELC) TAB_X509V3 ltac:(lia) ec_w17 IP IP IP IP L L L L L L L L L L c16 H16); clear H16; intros c17 H17.
  apply (STEP 0x511700 0x511734 0x59f2c0 22 0x5111a0 0x5111a8 2256 2254 19 2360 2358 20 (stub_PKCS12 RT GOBJ AF AFP C_ERS C_ELC) TAB_PKCS12 ltac:(lia) ec_w18 IP IP IP IP L L L L L L L L L L c17 H17); clear H17; intros c18 H18.
  apply (STEP 0x511748 0x51177c 0x59f480 45 0x5111a8 0x5111b0 2360 2358 20 2487 2485 21 (stub_RAND RT GOBJ AF AFP C_ERS C_ELC) TAB_RAND ltac:(lia) ec_w19 IP IP IP IP L L L L L L L L L L c18 H18); clear H18; intros c19 H19.
  apply (STEP 0x511790 0x5117c4 0x59f800 16 0x5111b0 0x5111b8 2487 2485 21 2585 2583 22 (stub_DSO RT GOBJ AF AFP C_ERS C_ELC) TAB_DSO ltac:(lia) ec_w20 IP IP IP IP L L L L L L L L L L c19 H19); clear H19; intros c20 H20.
  apply (STEP 0x5117d8 0x51180c 0x59f960 39 0x5111b8 0x5111c0 2585 2583 22 2706 2704 23 (stub_TS RT GOBJ AF AFP C_ERS C_ELC) TAB_TS ltac:(lia) ec_w21 IP IP IP IP L L L L L L L L L L c20 H20); clear H20; intros c21 H21.
  apply (STEP 0x511820 0x511854 0x59fc80 32 0x5111c0 0x5111c8 2706 2704 23 2820 2818 24 (stub_HTTP RT GOBJ AF AFP C_ERS C_ELC) TAB_HTTP ltac:(lia) ec_w22 IP IP IP IP L L L L L L L L L L c21 H21); clear H21; intros c22 H22.
  apply (STEP 0x511868 0x51189c 0x59ff20 25 0x5111c8 0x5111d0 2820 2818 24 2927 2925 25 (stub_OCSP RT GOBJ AF AFP C_ERS C_ELC) TAB_OCSP ltac:(lia) ec_w23 IP IP IP IP L L L L L L L L L L c22 H22); clear H22; intros c23 H23.
  apply (STEP 0x5118b0 0x5118e4 0x5a0120 13 0x5111d0 0x5111d8 2927 2925 25 3022 3020 26 (stub_UI RT GOBJ AF AFP C_ERS C_ELC) TAB_UI ltac:(lia) ec_w24 IP IP IP IP L L L L L L L L L L c23 H23); clear H23; intros c24 H24.
  apply (STEP 0x5118f8 0x51192c 0x5a0220 102 0x5111d8 0x5111e0 3022 3020 26 3206 3204 27 (stub_CMS RT GOBJ AF AFP C_ERS C_ELC) TAB_CMS ltac:(lia) ec_w25 IP IP IP IP L L L L L L L L L L c24 H24); clear H24; intros c25 H25.
  apply (STEP 0x511940 0x511974 0x5a0a20 30 0x5111e0 0x5111e8 3206 3204 27 3318 3316 28 (stub_CRMF RT GOBJ AF AFP C_ERS C_ELC) TAB_CRMF ltac:(lia) ec_w26 IP IP IP IP L L L L L L L L L L c25 H25); clear H25; intros c26 H26.
  apply (STEP 0x511988 0x5119bc 0x5a0c80 106 0x5111e8 0x5111f0 3318 3316 28 3506 3504 29 (stub_CMP RT GOBJ AF AFP C_ERS C_ELC) TAB_CMP ltac:(lia) ec_w27 IP IP IP IP L L L L L L L L L L c26 H26); clear H26; intros c27 H27.
  apply (STEP 0x5119d0 0x511a04 0x5a14e0 17 0x5111f0 0x5111f8 3506 3504 29 3605 3603 30 (stub_CT RT GOBJ AF AFP C_ERS C_ELC) TAB_CT ltac:(lia) ec_w28 IP IP IP IP L L L L L L L L L L c27 H27); clear H27; intros c28 H28.
  apply (STEP 0x511a18 0x511a4c 0x5a1640 9 0x5111f8 0x511200 3605 3603 30 3696 3694 31 (stub_ESS RT GOBJ AF AFP C_ERS C_ELC) TAB_ESS ltac:(lia) ec_w29 IP IP IP IP L L L L L L L L L L c28 H28); clear H28; intros c29 H29.
  apply (STEP 0x511a60 0x511a94 0x5a1700 4 0x511200 0x511208 3696 3694 31 3782 3780 32 (stub_ASYNC RT GOBJ AF AFP C_ERS C_ELC) TAB_ASYNC ltac:(lia) ec_w30 IP IP IP IP L L L L L L L L L L c29 H29); clear H29; intros c30 H30.
  apply (STEP 0x511aa8 0x511adc 0x5a1780 14 0x511208 0x511210 3782 3780 32 3878 3876 33 (stub_SM2 RT GOBJ AF AFP C_ERS C_ELC) TAB_SM2 ltac:(lia) ec_w31 IP IP IP IP L L L L L L L L L L c30 H30); clear H30; intros c31 H31.
  apply (STEP 0x511af0 0x511b24 0x5a18a0 25 0x511210 0x511218 3878 3876 33 3985 3983 34 (stub_OSSL_STORE RT GOBJ AF AFP C_ERS C_ELC) TAB_OSSL_STORE ltac:(lia) ec_w32 IP IP IP IP L L L L L L L L L L c31 H31); clear H31; intros c32 H32.
  apply (STEP 0x511b38 0x511b6c 0x5a1aa0 11 0x511218 0x511220 3985 3983 34 4078 4076 35 (stub_PROP RT GOBJ AF AFP C_ERS C_ELC) TAB_PROP ltac:(lia) ec_w33 IP IP IP IP L L L L L L L L L L c32 H32); clear H32; intros c33 H33.
  apply (STEP 0x511b80 0x511bb4 0x5a1b80 160 0x511220 0x511228 4078 4076 35 4320 4318 36 (stub_PROV RT GOBJ AF AFP C_ERS C_ELC) TAB_PROV ltac:(lia) ec_w34 IP IP IP IP L L L L L L L L L L c33 H33); clear H33; intros c34 H34.
  exact (cr_exit Σ PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo outer canary od oldcb T MST ART0 CALL HSTK Hfr Hk c34 H34).
Qed.
End Crypto.
