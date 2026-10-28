(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
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
  intros until lo. intros ST LO0 LO HTOP MI. unfold e_crypto_strs.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  th_frame 16%nat [8; 8]%nat ST.
  do 5 zstep.
  apply evt_done. unfold e_err_strings. eexists.
  split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [eassumption| assumption].
Qed.

(* [comment removed for export] *)
Definition ecw_spec (Rp Rk E : Z) : Prop := forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -16) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR (Z_to_bv 64 Rk) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (Z_to_bv 64 E) fc None m (seg_rom asegs))
    (MS (mkR (Z_to_bv 64 Rp) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 Rp) fc None m (seg_rom asegs)).
Ltac ecw_tac sp m :=
  let RSP := fresh "RSP" in pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP;
  let MU := fresh "MU" in let WM := fresh "WM" in pose proof (munch_refl ([] : list (Z * Z)) m) as MU; pose proof (wmono_refl asegs m) as WM;
  let HWU := fresh "HWU" in let HWS := fresh "HWS" in assert (HWU : ut_fp []) by ut_fp_lia; assert (HWS : sh_fp []) by sh_fp_lia;
  zstep; th_if_lit; zstep; apply evt_done; cbv delta [mkR]; reflexivity.
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
  intros until s0v. intros FR ST LO0 LO HTOP MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  cl_eu (bv_unsigned sp) (-16) EU1.
  do 3 zstep.
  pose proof FR as FR'. eapply stk_release in FR'; [| exact ST| lia]. cbn [cells_size csize Nat.add] in FR'.
  replace (bv_unsigned sp + -16 + Z.of_nat 16) with (bv_unsigned sp) in FR' by lia.
  zstep. zstep. apply evt_done. split; [| exact FR']. cbv delta [mkR].
  replace (bv_unsigned sp + -16 + 16) with (bv_unsigned sp) by lia. rewrite ?(Z_to_bv_bv_unsigned sp). reflexivity.
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
Proof. destruct GO_libraries as (b & sz & G & B1 & B2). exact (els_table_ut GOBJ 0x52ec60 43 b sz G B1 B2 els_okb_libraries). Qed.
Lemma TAB_reasons : els_table GOBJ ERR_TAB2 39.
Proof. destruct GO_reasons as (b & sz & G & B1 & B2). exact (els_table_ut GOBJ 0x52efc0 39 b sz G B1 B2 els_okb_reasons). Qed.

Lemma TAB_BN : els_table GOBJ 0x59b500 22.
Proof. destruct GO_BN as (b & sz & G & B1 & B2). exact (els_table_ut GOBJ 0x59b500 22 b sz G B1 B2 els_okb_BN). Qed.
Lemma TAB_RSA : els_table GOBJ 0x59b6c0 81.
Proof. destruct GO_RSA as (b & sz & G & B1 & B2). exact (els_table_ut GOBJ 0x59b6c0 81 b sz G B1 B2 els_okb_RSA). Qed.
Lemma TAB_DH : els_table GOBJ 0x59bd20 31.
Proof. destruct GO_DH as (b & sz & G & B1 & B2). exact (els_table_ut GOBJ 0x59bd20 31 b sz G B1 B2 els_okb_DH). Qed.
Lemma TAB_EVP : els_table GOBJ 0x59bfa0 125.
Proof. destruct GO_EVP as (b & sz & G & B1 & B2). exact (els_table_ut GOBJ 0x59bfa0 125 b sz G B1 B2 els_okb_EVP). Qed.
Lemma TAB_BUF : els_table GOBJ 0xf88e0 0.
Proof. destruct GO_BUF as (b & sz & G & B1 & B2). exact (els_table_rom0 GOBJ 0xf88e0 b sz G B1 ltac:(lia) eq_refl ltac:(lia) ltac:(unfold SEGTOP_A; lia) buf_table_rom). Qed.
Lemma TAB_OBJ : els_table GOBJ 0x59c960 3.
Proof. destruct GO_OBJ as (b & sz & G & B1 & B2). exact (els_table_ut GOBJ 0x59c960 3 b sz G B1 B2 els_okb_OBJ). Qed.
Lemma TAB_PEM : els_table GOBJ 0x59c9c0 34.
Proof. destruct GO_PEM as (b & sz & G & B1 & B2). exact (els_table_ut GOBJ 0x59c9c0 34 b sz G B1 B2 els_okb_PEM). Qed.
Lemma TAB_DSA : els_table GOBJ 0x59cc80 16.
Proof. destruct GO_DSA as (b & sz & G & B1 & B2). exact (els_table_ut GOBJ 0x59cc80 16 b sz G B1 B2 els_okb_DSA). Qed.
Lemma TAB_X509 : els_table GOBJ 0x59cde0 47.
Proof. destruct GO_X509 as (b & sz & G & B1 & B2). exact (els_table_ut GOBJ 0x59cde0 47 b sz G B1 B2 els_okb_X509). Qed.
Lemma TAB_ASN1 : els_table GOBJ 0x59d1a0 117.
Proof. destruct GO_ASN1 as (b & sz & G & B1 & B2). exact (els_table_ut GOBJ 0x59d1a0 117 b sz G B1 B2 els_okb_ASN1). Qed.
Lemma TAB_CONF : els_table GOBJ 0x59dac0 27.
Proof. destruct GO_CONF as (b & sz & G & B1 & B2). exact (els_table_ut GOBJ 0x59dac0 27 b sz G B1 B2 els_okb_CONF). Qed.
Lemma TAB_CRYPTO : els_table GOBJ 0x59dce0 31.
Proof. destruct GO_CRYPTO as (b & sz & G & B1 & B2). exact (els_table_ut GOBJ 0x59dce0 31 b sz G B1 B2 els_okb_CRYPTO). Qed.
Lemma TAB_COMP : els_table GOBJ 0x59df60 10.
Proof. destruct GO_COMP as (b & sz & G & B1 & B2). exact (els_table_ut GOBJ 0x59df60 10 b sz G B1 B2 els_okb_COMP). Qed.
Lemma TAB_EC : els_table GOBJ 0x59e040 76.
Proof. destruct GO_EC as (b & sz & G & B1 & B2). exact (els_table_ut GOBJ 0x59e040 76 b sz G B1 B2 els_okb_EC). Qed.
Lemma TAB_BIO : els_table GOBJ 0x59e640 47.
Proof. destruct GO_BIO as (b & sz & G & B1 & B2). exact (els_table_ut GOBJ 0x59e640 47 b sz G B1 B2 els_okb_BIO). Qed.
Lemma TAB_PKCS7 : els_table GOBJ 0x59ea00 38.
Proof. destruct GO_PKCS7 as (b & sz & G & B1 & B2). exact (els_table_ut GOBJ 0x59ea00 38 b sz G B1 B2 els_okb_PKCS7). Qed.
Lemma TAB_X509V3 : els_table GOBJ 0x59ed00 73.
Proof. destruct GO_X509V3 as (b & sz & G & B1 & B2). exact (els_table_ut GOBJ 0x59ed00 73 b sz G B1 B2 els_okb_X509V3). Qed.
Lemma TAB_PKCS12 : els_table GOBJ 0x59f2c0 22.
Proof. destruct GO_PKCS12 as (b & sz & G & B1 & B2). exact (els_table_ut GOBJ 0x59f2c0 22 b sz G B1 B2 els_okb_PKCS12). Qed.
Lemma TAB_RAND : els_table GOBJ 0x59f480 45.
Proof. destruct GO_RAND as (b & sz & G & B1 & B2). exact (els_table_ut GOBJ 0x59f480 45 b sz G B1 B2 els_okb_RAND). Qed.
Lemma TAB_DSO : els_table GOBJ 0x59f800 16.
Proof. destruct GO_DSO as (b & sz & G & B1 & B2). exact (els_table_ut GOBJ 0x59f800 16 b sz G B1 B2 els_okb_DSO). Qed.
Lemma TAB_TS : els_table GOBJ 0x59f960 39.
Proof. destruct GO_TS as (b & sz & G & B1 & B2). exact (els_table_ut GOBJ 0x59f960 39 b sz G B1 B2 els_okb_TS). Qed.
Lemma TAB_HTTP : els_table GOBJ 0x59fc80 32.
Proof. destruct GO_HTTP as (b & sz & G & B1 & B2). exact (els_table_ut GOBJ 0x59fc80 32 b sz G B1 B2 els_okb_HTTP). Qed.
Lemma TAB_OCSP : els_table GOBJ 0x59ff20 25.
Proof. destruct GO_OCSP as (b & sz & G & B1 & B2). exact (els_table_ut GOBJ 0x59ff20 25 b sz G B1 B2 els_okb_OCSP). Qed.
Lemma TAB_UI : els_table GOBJ 0x5a0120 13.
Proof. destruct GO_UI as (b & sz & G & B1 & B2). exact (els_table_ut GOBJ 0x5a0120 13 b sz G B1 B2 els_okb_UI). Qed.
Lemma TAB_CMS : els_table GOBJ 0x5a0220 102.
Proof. destruct GO_CMS as (b & sz & G & B1 & B2). exact (els_table_ut GOBJ 0x5a0220 102 b sz G B1 B2 els_okb_CMS). Qed.
Lemma TAB_CRMF : els_table GOBJ 0x5a0a20 30.
Proof. destruct GO_CRMF as (b & sz & G & B1 & B2). exact (els_table_ut GOBJ 0x5a0a20 30 b sz G B1 B2 els_okb_CRMF). Qed.
Lemma TAB_CMP : els_table GOBJ 0x5a0c80 106.
Proof. destruct GO_CMP as (b & sz & G & B1 & B2). exact (els_table_ut GOBJ 0x5a0c80 106 b sz G B1 B2 els_okb_CMP). Qed.
Lemma TAB_CT : els_table GOBJ 0x5a14e0 17.
Proof. destruct GO_CT as (b & sz & G & B1 & B2). exact (els_table_ut GOBJ 0x5a14e0 17 b sz G B1 B2 els_okb_CT). Qed.
Lemma TAB_ESS : els_table GOBJ 0x5a1640 9.
Proof. destruct GO_ESS as (b & sz & G & B1 & B2). exact (els_table_ut GOBJ 0x5a1640 9 b sz G B1 B2 els_okb_ESS). Qed.
Lemma TAB_ASYNC : els_table GOBJ 0x5a1700 4.
Proof. destruct GO_ASYNC as (b & sz & G & B1 & B2). exact (els_table_ut GOBJ 0x5a1700 4 b sz G B1 B2 els_okb_ASYNC). Qed.
Lemma TAB_SM2 : els_table GOBJ 0x5a1780 14.
Proof. destruct GO_SM2 as (b & sz & G & B1 & B2). exact (els_table_ut GOBJ 0x5a1780 14 b sz G B1 B2 els_okb_SM2). Qed.
Lemma TAB_OSSL_STORE : els_table GOBJ 0x5a18a0 25.
Proof. destruct GO_OSSL_STORE as (b & sz & G & B1 & B2). exact (els_table_ut GOBJ 0x5a18a0 25 b sz G B1 B2 els_okb_OSSL_STORE). Qed.
Lemma TAB_PROP : els_table GOBJ 0x5a1aa0 11.
Proof. destruct GO_PROP as (b & sz & G & B1 & B2). exact (els_table_ut GOBJ 0x5a1aa0 11 b sz G B1 B2 els_okb_PROP). Qed.
Lemma TAB_PROV : els_table GOBJ 0x5a1b80 160.
Proof. destruct GO_PROV as (b & sz & G & B1 & B2). exact (els_table_ut GOBJ 0x5a1b80 160 b sz G B1 B2 els_okb_PROV). Qed.

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
  exists (Σ : rts RT) (m : mem) (pk lh B : Z) (L : list (Z * Z)) (g : lh_geo) (bks : list (list (bptr * Z))) (lb : byte)
         (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    ASTA RT Σ PMc (eq (MS (mkR (Z_to_bv 64 site) (Z_to_bv 64 (usp + -16)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (Z_to_bv 64 site) fc None m (seg_rom asegs))) c
    /\ ART RT Σ m /\ mem_inv asegs m /\ stk asegs m lo (usp + -16) /\ rw_cells asegs m (usp + -16) [C8 s0; C8 ra]
    /\ cl_env m lb canary
    /\ rw_cells asegs m G_IC_STOPPED [C1 (Z_to_bv 8 0)] /\ rw_cells asegs m G_IC_OPTSDONE [C8 od] /\ rw_cells asegs m G_IC_BASE_ONCE [C4 (Z_to_bv 64 2)] /\ rw_cells asegs m G_IC_BASE_RET [C4 (Z_to_bv 64 1)]
    /\ err_statics m pk lh /\ rw_cells asegs m G_CANCELBUF [C8 oldcb] /\ rw_cells asegs m pk (mutex_cells z64 z64)
    /\ lh_repE GOBJ m L lh B g bks /\ Permutation (rt_live RT Σ) (L ++ (pk, 40) :: rt_live RT Σ0) /\ Z.of_nat (length L) <= bnd /\ 0 <= g_items g <= itb
    /\ rt_frames RT Σ = rt_frames RT Σ0 /\ rt_sp0 RT Σ = rt_sp0 RT Σ0 /\ rt_credit RT Σ0 - crd <= rt_credit RT Σ /\ rt_cg RT Σ = rt_cg RT Σ0
    /\ uw_chain m sp s0 outer /\ rt_pres_fp (rt_live RT Σ0) (rt_frames RT Σ0) usp (EFIRST_W pk) m0 m
    /\ (forall x, aclient (rt_live RT Σ0) (rt_frames RT Σ0) usp x -> ~ (pk <= x < pk + 40)) /\ 0 < pk /\ pk mod 16 = 0 /\ pk + 40 < USTACK_TOP /\ 0x10007fff8000 <= pk.

(* [comment removed for export] *)
Lemma cr_step : forall (E R2 TAB n Rp Rk bnd itb crd bnd' itb' crd' : Z),
  stub_stmt RT GOBJ E TAB R2 n -> els_table GOBJ TAB n -> 0 <= n -> ecw_spec Rp Rk E ->
  memP (Rk, e_crypto_strs) CR_SITES = true -> memP (Rk, E) CR_CALLS = true -> inclP (STUB_SITES E R2) CR_SITES = true -> inclP (STUB_CALLS R2) CR_CALLS = true ->
  0 <= Rk < 2 ^ 32 -> Rk mod 2 = 0 ->
  bnd + 82 + n <= bnd' -> itb + 82 + n <= itb' -> crd + 1 <= crd' -> 0 <= bnd -> bnd' <= 4320 -> itb' <= 4318 -> 0 <= crd -> crd' <= 36 ->
  forall c, CRI Rp bnd itb crd c -> (forall c', CRI Rk bnd' itb' crd' c' -> realizes asegs c' T) -> realizes asegs c T.
Proof.
  intros E R2 TAB n Rp Rk bnd itb crd bnd' itb' crd' STUB TAB_E N0 ECW INS INC INSS INCC RK EVEN Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 c (Σ & m & pk & lh & B & L & g & bks & lb & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & HA & ART1 & MI1 & ST1 & FR1 & ENV1 & STP1 & OD1 & ONCE1 & BRET1
            & STC1 & CB1 & MC1 & REPE1 & PERM1 & LL1 & IT1 & FRS1 & SP1 & CR1 & CG1 & UWC1 & PRES1 & NPK & PK0 & PK16 & PKHI & PKH) Hk.
  pose proof CALL as (ST & LOW & LOR & SPT & SPA). pose proof (af_sp0_win RT AF Σ0 m0 ART00) as SP0W. pose proof (af_sp0_range RT AF Σ0 m0 ART00) as SP0R.
  assert (NUM : 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold usp, RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  assert (EU1 : bv_unsigned (Z_to_bv 64 (usp + -16)) = usp + -16) by (apply unsigned_lit; unfold usp, USTACK_TOP, RT_STACK in *; lia).
  assert (HT1 : bv_unsigned sp <= 2 ^ 47) by (unfold usp, USTACK_TOP in *; lia).
  pose proof (ECW sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo ST1 ltac:(lia) ltac:(unfold usp, RT_STACK in *; lia) HT1 MI1) as W.
  cl_lift W HA c1 Hc1. destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & -> & Hc1'). clear Hc1.
  pose proof CTX as CTXk. pose proof CGH as CGHk. rewrite <- CG1 in CTXk, CGHk.
  destruct (cl_chain_call (rt_cg RT Σ) e_crypto_strs E Rk m m ra s0 sp (Z_to_bv 64 (usp + -16)) outer CTXk (cg_has_site _ _ _ Rk e_crypto_strs CGHk (memP_true _ _ INS)) (cg_has_call _ _ _ Rk E CGHk (memP_true _ _ INC)) UWC1 ltac:(intros a _; reflexivity)
              ltac:(fold usp; replace (usp - 16) with (usp + -16) by lia; exact FR1) ltac:(rewrite EU1; unfold usp; lia) SPT) as (CTXc & UWCc).
  pose proof (Permutation_length PERM1) as PL1. rewrite length_app in PL1. cbn [length] in PL1.
  assert (INPK : In (pk, 40) (rt_live RT Σ)) by (eapply Permutation_in; [apply Permutation_sym; exact PERM1| apply in_or_app; right; left; reflexivity]).
  pose proof (af_live_range RT AF Σ m pk 40 ART1 INPK) as (_ & PKLO & _). rewrite SP1 in PKLO.
  apply (STUB Σ PMc (Z_to_bv 64 Rk) (Z_to_bv 64 (usp + -16)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo (bv_unsigned ra :: outer) lb canary L ((pk, 40) :: rt_live RT Σ0) lh B g bks pk 43 39 FDO MST eq_refl ART1 MI1).
  { unfold call_ok. rewrite EU1. split; [exact ST1|]. split; [rewrite SP1; exact LOW|]. split; [unfold usp, RT_STACK in *; lia|]. split; [unfold usp, USTACK_TOP in *; lia|].
    unfold usp in *. clear - SPA. Z.div_mod_to_equations. lia. }
  { rewrite EU1. unfold usp, RT_STACK in *. lia. }
  { rewrite (unsigned_lit Rk) by lia. exact CTXc. }
  { exact UWCc. }
  { exact (cg_has_weaken _ _ _ _ _ CGHk INSS INCC). }
  { rewrite FRS1. exact Hfr. }
  { cbn [length]. lia. }
  { lia. }
  { exact ENV1. }
  { exact STC1. }
  { left. reflexivity. }
  { clear - PK16. Z.div_mod_to_equations. lia. }
  { exact MC1. }
  { exact REPE1. }
  { exact PERM1. }
  { constructor; [cbn; lia| exact POS]. }
  { exact TAB_libraries. }
  { exact TAB_reasons. }
  { exact TAB_E. }
  { lia. }
  { lia. }
  { lia. }
  { unfold LH_KMAX. lia. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ2 & L2 & B2 & g2 & bks2 & lb2 & Hc2 & PERM2 & LL2 & IT2 & FRS2 & SP2 & CR2 & CG2).
  destruct (ASTA_unpack RT Σ2 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & ST2) & PRES2 & ENV2 & REPE2 & MC2 & STC2) & Hc2'). clear Hc2.
  destruct RS2 as (w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even Rk) in Hc2' by lia. rewrite FRS1 in PRES2.
  assert (AG2 : forall P : Z -> Prop, (forall x, P x -> aclient ((pk, 40) :: rt_live RT Σ0) (rt_frames RT Σ0) (usp - 16) x /\ x <> G_ALLOW_CUST /\ ~ (pk + 4 <= x < pk + 8)) -> agree_on P m m2).
  { intros P HP a Ha. destruct (HP _ Ha) as (X1 & X2 & X3). apply PRES2; [| cbn [outside]; repeat split; try exact I; lia].
    apply (aclient_mono _ _ _ _ _ _ _ X1); [intros e He; exact He| intros e He; exact He| lia]. }
  assert (STAT2 : forall a cs, rw_cells asegs m a cs -> 0xb8f190 <= a -> a + Z.of_nat (cells_size cs) <= 0xba3e98 -> (a + Z.of_nat (cells_size cs) <= G_ALLOW_CUST \/ G_ALLOW_CUST + 1 <= a) -> rw_cells asegs m2 a cs).
  { intros a cs H H1 H2 H3. apply (rw_cells_agree_nw asegs m m2 _ _ H). apply AG2. intros x Hx. split; [right; left; apply client_static_intro; lia|]. unfold G_ALLOW_CUST in *. lia. }
  unfold G_ALLOW_CUST, G_IC_STOPPED, G_IC_OPTSDONE, G_IC_BASE_ONCE, G_IC_BASE_RET, G_CANCELBUF in *.
  apply Hk. exists Σ2, m2, pk, lh, B2, L2, g2, bks2, lb2, w0, w1, w2, e1, e2, e3, e4, e5, e6, e7, w3, w4, w5, w6, F2, fc2.
  split; [exact Hc2'|]. split; [exact ART2|]. split; [exact MI2|]. split; [exact ST2|].
  split. { apply (rw_cells_agree_nw asegs m m2 _ _ FR1). apply AG2. cbn [cells_size csize Nat.add]. intros x Hx. split; [left; unfold usp, USTACK_TOP in *; lia|]. unfold usp, STACK_WIN, RT_STACK in *. lia. }
  split; [exact ENV2|].
  split; [exact (STAT2 _ _ STP1 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia))|]. split; [exact (STAT2 _ _ OD1 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia))|].
  split; [exact (STAT2 _ _ ONCE1 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia))|]. split; [exact (STAT2 _ _ BRET1 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia))|].
  split; [exact STC2|]. split; [exact (STAT2 _ _ CB1 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia))|]. split; [exact MC2|]. split; [exact REPE2|]. split; [exact PERM2|].
  split; [lia|]. split; [pose proof (proj1 (proj1 REPE2)) as GOK; unfold lh_geo_ok in GOK; lia|].
  split; [rewrite FRS2; exact FRS1|]. split; [rewrite SP2; exact SP1|]. split; [lia|]. split; [rewrite CG2; exact CG1|].
  split; [exact (uw_chain_agree outer m m2 sp s0 UWC1 ltac:(apply AG2; intros x Hx; split; [left; unfold usp in *; lia|]; unfold usp, USTACK_TOP, STACK_WIN, RT_STACK in *; lia))|].
  split. { intros a Ha Ho. pose proof Ho as Ho'. cbn [outside] in Ho'. destruct Ho' as (O1 & _). unfold G_ALLOW_CUST in O1.
           rewrite (PRES2 a ltac:(apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; right; exact He| intros e He; exact He| lia]) ltac:(cbn [outside]; pose proof (NPK _ Ha); repeat split; try exact I; lia)).
           exact (PRES1 a Ha Ho). }
  split; [exact NPK|]. split; [exact PK0|]. split; [exact PK16|]. exact (conj PKHI PKH).
Qed.

(* [comment removed for export] *)
Lemma cr_step0 : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (lb : byte) (lk0 h0 f0 : word) c,
  mem_inv asegs m0 -> uw_chain m0 sp s0 outer -> cl_env m0 lb canary ->
  rw_cells asegs m0 G_IC_STOPPED [C1 (Z_to_bv 8 0)] -> rw_cells asegs m0 G_IC_OPTSDONE [C8 od] -> rw_cells asegs m0 G_IC_BASE_ONCE [C4 (Z_to_bv 64 2)] -> rw_cells asegs m0 G_IC_BASE_RET [C4 (Z_to_bv 64 1)] ->
  rw_cells asegs m0 G_ERR_ONCE [C4 z64] -> rw_cells asegs m0 G_ERR_LOCK [C8 lk0] -> rw_cells asegs m0 G_ERR_HASH [C8 h0] -> rw_cells asegs m0 G_ERR_FLAG [C4 f0] ->
  rw_cells asegs m0 G_CANCELBUF [C8 oldcb] ->
  ASTA RT Σ0 PMc (eq (entry_st ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_crypto_strs m0)) c ->
  (forall c', CRI 0x511118 84 82 2 c' -> realizes asegs c' T) -> realizes asegs c T.
Proof.
  intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc lb lk0 h0 f0 c MI0 UWC ENV STP OD ONCE BRET ONC LKC LHC FLC CBC HA Hk.
  pose proof CALL as (ST & LOW & LOR & SPT & SPA). pose proof (af_sp0_win RT AF Σ0 m0 ART00) as SP0W. pose proof (af_sp0_range RT AF Σ0 m0 ART00) as SP0R.
  assert (NUM : 0x10007fff8000 <= lo /\ usp <= USTACK_TOP /\ SEGTOP_A <= lo) by (unfold usp, RT_STACK, STACK_WIN, USTACK_TOP, SEGTOP_A in *; lia).
  assert (EU1 : bv_unsigned (Z_to_bv 64 (usp + -16)) = usp + -16) by (apply unsigned_lit; unfold usp, USTACK_TOP, RT_STACK in *; lia).
  assert (HT1 : bv_unsigned sp <= 2 ^ 47) by (unfold usp, USTACK_TOP in *; lia).
  pose proof (ec_w0 ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 lo ST ltac:(lia) ltac:(unfold usp, RT_STACK in *; lia) HT1 MI0) as W.
  cl_lift W HA c1 Hc1. destruct (ASTA_unpack RT Σ0 _ _ c1 Hc1) as (ms1 & (m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1'). clear Hc1. fold usp in MU1, FR1, ST1, Hc1'.
  assert (MU1' : munch ([] ++ [(usp - 16, usp)]) m0 m1) by (eapply munch_weaken; [| exact MU1]; unfold sub_fp; cbn [outside app]; intros; lia).
  pose proof (cl_seg_ART RT AF Σ0 m0 m1 usp 16 [] ART00 ltac:(unfold usp, RT_STACK in *; lia) ltac:(lia) MU1' ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ0 m0 m1 usp 16 [] ART00 ltac:(unfold usp, RT_STACK in *; lia) ltac:(lia) MU1') as PR1.
  assert (STAT1 : forall a cs, rw_cells asegs m0 a cs -> 0x10000 <= a -> a + Z.of_nat (cells_size cs) <= SEGTOP_A -> rw_cells asegs m1 a cs).
  { intros a cs H H1 H2. apply (rw_cells_agree asegs m0 m1 _ _ H); [| exact WM1]. intros x Hx. cbv beta in Hx. apply MU1. cbn [outside]. unfold SEGTOP_A, RT_STACK in *. split; [lia| exact I]. }
  unfold G_IC_STOPPED, G_IC_OPTSDONE, G_IC_BASE_ONCE, G_IC_BASE_RET, G_ERR_ONCE, G_ERR_LOCK, G_ERR_HASH, G_ERR_FLAG, G_CANCELBUF in *.
  assert (ENV1 : cl_env m1 lb canary).
  { apply (cl_env_agree m0 m1 lb canary ENV). intros a Ha. pose proof (client_static_range _ (cl_cell_static _ Ha)) as CR. unfold SEGTOP_A, RT_STACK in *. apply MU1. cbn [outside]. split; [lia| exact I]. }
  pose proof (uw_chain_agree outer m0 m1 sp s0 UWC ltac:(intros a Ha; apply MU1; cbn [outside]; cbv beta in Ha; unfold usp in *; split; [lia| exact I])) as UWC1.
  pose proof CTX as CTXk. pose proof CGH as CGHk.
  destruct (cl_chain_call (rt_cg RT Σ0) e_crypto_strs e_err_strings 0x511118 m1 m1 ra s0 sp (Z_to_bv 64 (usp + -16)) outer CTXk
              (cg_has_site _ _ _ 0x511118 e_crypto_strs CGHk ltac:(apply memP_true; vm_compute; reflexivity))
              (cg_has_call _ _ _ 0x511118 e_err_strings CGHk ltac:(apply memP_true; vm_compute; reflexivity)) UWC1 ltac:(intros a _; reflexivity)
              ltac:(fold usp; replace (usp - 16) with (usp + -16) by lia; exact FR1) ltac:(rewrite EU1; unfold usp; lia) SPT) as (CTXc & UWCc).
  apply (C_EFIRST Σ0 PMc (Z_to_bv 64 0x511118) (Z_to_bv 64 (usp + -16)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp s1 a0 a1 a2 a3 a4 a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo (bv_unsigned ra :: outer) lb canary od lk0 h0 f0 oldcb 43 39 FDO MST eq_refl ART1 MI1).
  { unfold call_ok. rewrite EU1. split; [exact ST1|]. split; [exact LOW|]. split; [unfold usp, RT_STACK in *; lia|]. split; [unfold usp, USTACK_TOP in *; lia|].
    unfold usp in *. clear - SPA. Z.div_mod_to_equations. lia. }
  { rewrite EU1. unfold usp, RT_STACK in *. lia. }
  { rewrite (unsigned_lit 0x511118) by lia. exact CTXc. }
  { exact UWCc. }
  { apply (cg_has_weaken _ _ _ _ _ CGHk); vm_compute; reflexivity. }
  { exact Hfr. }
  { lia. }
  { lia. }
  { exact POS. }
  { exact ENV1. }
  { exact (STAT1 _ _ STP ltac:(lia) ltac:(cbn; unfold SEGTOP_A; lia)). }
  { exact (STAT1 _ _ OD ltac:(lia) ltac:(cbn; unfold SEGTOP_A; lia)). }
  { exact (STAT1 _ _ ONCE ltac:(lia) ltac:(cbn; unfold SEGTOP_A; lia)). }
  { exact (STAT1 _ _ BRET ltac:(lia) ltac:(cbn; unfold SEGTOP_A; lia)). }
  { exact (STAT1 _ _ ONC ltac:(lia) ltac:(cbn; unfold SEGTOP_A; lia)). }
  { exact (STAT1 _ _ LKC ltac:(lia) ltac:(cbn; unfold SEGTOP_A; lia)). }
  { exact (STAT1 _ _ LHC ltac:(lia) ltac:(cbn; unfold SEGTOP_A; lia)). }
  { exact (STAT1 _ _ FLC ltac:(lia) ltac:(cbn; unfold SEGTOP_A; lia)). }
  { exact (STAT1 _ _ CBC ltac:(lia) ltac:(cbn; unfold SEGTOP_A; lia)). }
  { exact TAB_libraries. }
  { exact TAB_reasons. }
  { lia. }
  { lia. }
  { unfold LH_KMAX. lia. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ2 & pk & lh & B & L2 & g2 & bks2 & lb2 & Hc2 & PERM2 & LL2 & IT2 & FRS2 & SP2 & CR2 & CG2 & PK0 & PK16 & PKHI & PKH & NPK).
  destruct (ASTA_unpack RT Σ2 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & ST2) & PRES2 & ENV2 & STP2 & OD2 & ONCE2 & BRET2 & STC2 & CB2 & MC2 & REPE2) & Hc2'). clear Hc2.
  destruct RS2 as (w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2, NPK. rewrite (ret_pc_even 0x511118) in Hc2' by lia. fold usp in NPK.
  assert (AG2 : forall P : Z -> Prop, (forall x, P x -> aclient (rt_live RT Σ0) (rt_frames RT Σ0) (usp - 16) x /\ x <> G_ALLOW_CUST /\ ~ (0xb9f820 <= x < 0xb9f824) /\ ~ (0xb9f7e0 <= x < 0xb9f7e8)
                    /\ ~ (0xb9f800 <= x < 0xb9f808) /\ ~ (0xb9f840 <= x < 0xb9f844) /\ ~ (0xba3e90 <= x < 0xba3e98)) -> agree_on P m1 m2).
  { intros P HP a Ha. destruct (HP _ Ha) as (X1 & X2 & X3 & X4 & X5 & X6 & X7). apply PRES2; [exact X1|]. unfold EFIRST_W. cbn [outside]. unfold G_ALLOW_CUST, G_ERR_ONCE, G_ERR_LOCK, G_ERR_HASH, G_ERR_FLAG, G_CANCELBUF in *. repeat split; try exact I; lia. }
  apply Hk. exists Σ2, m2, pk, lh, B, L2, g2, bks2, lb2, w0, w1, w2, e1, e2, e3, e4, e5, e6, e7, w3, w4, w5, w6, F2, fc2.
  split; [exact Hc2'|]. split; [exact ART2|]. split; [exact MI2|]. split; [exact ST2|].
  split. { apply (rw_cells_agree_nw asegs m1 m2 _ _ FR1). apply AG2. cbn [cells_size csize Nat.add]. intros x Hx. split; [left; unfold usp, USTACK_TOP in *; lia|]. unfold G_ALLOW_CUST, usp, STACK_WIN, RT_STACK in *. repeat split; lia. }
  split; [exact ENV2|]. split; [exact STP2|]. split; [exact OD2|]. split; [exact ONCE2|]. split; [exact BRET2|]. split; [exact STC2|]. split; [exact CB2|]. split; [exact MC2|]. split; [exact REPE2|]. split; [exact PERM2|].
  split; [lia|]. split; [lia|].
  split; [exact FRS2|]. split; [exact SP2|]. split; [lia|]. split; [exact CG2|].
  split; [exact (uw_chain_agree outer m1 m2 sp s0 UWC1 ltac:(apply AG2; intros x Hx; split; [left; unfold usp in *; lia|]; unfold G_ALLOW_CUST, usp, USTACK_TOP, STACK_WIN, RT_STACK in *; repeat split; lia))|].
  split. { intros a Ha Ho. assert (NPKa : ~ (pk <= bv_unsigned a < pk + 40)) by (apply NPK; apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; exact He| intros e He; exact He| lia]).
           pose proof Ho as Ho'. cbn [outside] in Ho'. unfold G_ALLOW_CUST, G_ERR_ONCE, G_ERR_LOCK, G_ERR_HASH, G_ERR_FLAG, G_CANCELBUF in Ho'. destruct Ho' as (O1 & O2 & O3 & O4 & O5 & O6 & _).
           rewrite (PRES2 a ltac:(apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; exact He| intros e He; exact He| lia]) Ho). exact (PR1 a Ha I). }
  split; [intros x Hx; apply NPK; apply (aclient_mono _ _ _ _ _ _ _ Hx); [intros e He; exact He| intros e He; exact He| lia]|].
  split; [exact PK0|]. split; [exact PK16|]. exact (conj PKHI PKH).
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
Proof.
  intros Hk0 c (Σ & m & pk & lh & B & L & g & bks & lb & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & HA & ART1 & MI1 & ST1 & FR1 & ENV1 & STP1 & OD1 & ONCE1 & BRET1
            & STC1 & CB1 & MC1 & REPE1 & PERM1 & LL1 & IT1 & FRS1 & SP1 & CR1 & CG1 & UWC1 & PRES1 & NPK & PK0 & PK16 & PKHI & PKH).
  pose proof CALL as (ST & LOW & LOR & SPT & SPA). pose proof (af_sp0_win RT AF Σ0 m0 ART00) as SP0W.
  assert (HT1 : bv_unsigned sp <= 2 ^ 47) by (unfold usp, USTACK_TOP in *; lia).
  pose proof (ec_wx sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo ra s0 FR1 ST1 ltac:(unfold RT_STACK, STACK_WIN in *; lia) ltac:(unfold usp, RT_STACK in *; lia) HT1 MI1) as W.
  cl_lift W HA c1 Hc1. destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (-> & ST2) & Hc1'). clear Hc1.
  apply Hk0. exists Σ, pk, lh, B, L, g, bks, lb.
  split; [| split; [exact PERM1| split; [exact LL1| split; [exact IT1| split; [exact FRS1| split; [exact SP1| split; [exact CR1| split; [exact CG1| split; [exact PK0| exact (conj PK16 PKHI)]]]]]]]]].
  apply (ASTA_conseq RT Σ PMc _ _ c1 Hc1'). intros ms1 <-. exists m.
  split; [exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, F, fc; reflexivity|].
  split; [exact (conj ART1 (conj MI1 ST2))|]. split; [exact PRES1|]. split; [exact ENV1|]. split; [exact STP1|]. split; [exact OD1|]. split; [exact ONCE1|]. split; [exact BRET1|].
  split; [exact STC1|]. split; [exact CB1|]. exact (conj MC1 REPE1).
Qed.
End Run.

Local Notation IP := (ltac:(vm_compute; reflexivity)) (only parsing).
Local Notation L := (ltac:(lia)) (only parsing).

(* [comment removed for export] *)
Definition crypto_strs_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary od lk0 h0 f0 oldcb : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x2f0 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_crypto_strs (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer ->
  cg_has (rt_cg RT Σ) CR_SITES CR_CALLS ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> Z.of_nat (length (rt_live RT Σ)) + 4324 < LIVE_MAX -> 36 <= rt_credit RT Σ ->
  Forall (fun x => 0 < snd x) (rt_live RT Σ) ->
  cl_env m lb canary ->
  rw_cells asegs m G_IC_STOPPED [C1 (Z_to_bv 8 0)] -> rw_cells asegs m G_IC_OPTSDONE [C8 od] ->
  rw_cells asegs m G_IC_BASE_ONCE [C4 (Z_to_bv 64 2)] -> rw_cells asegs m G_IC_BASE_RET [C4 (Z_to_bv 64 1)] ->
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
