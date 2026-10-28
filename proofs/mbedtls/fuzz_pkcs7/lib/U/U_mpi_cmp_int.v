(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux CellsX MpiCoreAux HeapIface ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_mpi_cmp.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import MpiFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import MpiOpnd.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPMpiTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_mpi_cmp_int () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.eq"; "stdpp.bitvector.definitions.bv_swrap"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.lxor"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.shiftr"; "Stdlib.ZArith.BinInt.Z.abs"; "Corelib.Init.Logic.iff"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.lval"; "Corelib.Init.Logic.not"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_cmp.SIGF"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Stdlib.ZArith.BinInt.Z.add"].


(* [comment removed for export] *)
Lemma to_sign64 : forall z, -2^31 <= z < 2^31 ->
  Z.lor ((z ≫ 30) mod 18446744073709551616) 1 = (if z <? 0 then 2^64 - 1 else 1).
Proof.
  intros z Hz. rewrite Z.shiftr_div_pow2 by lia. destruct (Z.ltb_spec z 0).
  - assert (C : z / 2^30 = -1 \/ z / 2^30 = -2) by lia. destruct C as [-> | ->]; reflexivity.
  - assert (C : z / 2^30 = 0 \/ z / 2^30 = 1) by lia. destruct C as [-> | ->]; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma swrap32_mod64_small : forall z, -2^31 <= z < 2^31 -> bv_swrap 32 (z mod 18446744073709551616) = z.
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
  destruct (Z.lt_ge_cases z 0).
  - replace (z mod 18446744073709551616) with (z + 2^64) by (symmetry; rewrite <- (Z.mod_add z 1 18446744073709551616) by lia; apply Z.mod_small; lia).
    replace (z + 2^64 + 2^31) with ((z + 2^31) + 2^32 * 2^32) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
  - rewrite (Z.mod_small z) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma swrap32_period : forall a k, bv_swrap 32 (a + k * 2^32) = bv_swrap 32 a.
Proof.
  intros a k. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32).
  replace (a + k * 2^32 + bv_half_modulus 32) with ((a + bv_half_modulus 32) + k * 2^32) by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sint_abs32 : ltac2:(CDefT.buildp (gd_tbl_P_mpi_cmp_int ()) "Pz,$0.P,(1.(2.(3.(4.+2.+1?.))R1.)(5.R1.(4.+2.+1?.)))(6.$0.(7.&20.(8.(9.(:.R2.+10000000000000000.)(:.(7.&20.(;.(7.&20.(:.R2.+10000000000000000.))+1?.))+10000000000000000.))(:.(7.&20.(;.(7.&20.(:.R2.+10000000000000000.))+1?.))+10000000000000000.)))(7.&20.(<.R2.)))")
(* [comment removed for export] *).
Proof.
  intros z Hz. rewrite swrap32_mod64_small by lia. rewrite Z.shiftr_div_pow2 by lia.
  destruct (Z.lt_ge_cases z 0).
  - replace (z / 2^31) with (-1) by lia. change (bv_swrap 32 (-1) mod 18446744073709551616) with 18446744073709551615.
    replace (z mod 18446744073709551616) with (z + 2^64) by (symmetry; rewrite <- (Z.mod_add z 1 18446744073709551616) by lia; apply Z.mod_small; lia).
    rewrite zb_lxor_ones by lia. replace (18446744073709551615 - (z + 2 ^ 64) - 18446744073709551615) with (Z.abs z + (- 2^32) * 2^32) by lia.
    apply swrap32_period.
  - replace (z / 2^31) with 0 by lia. change (bv_swrap 32 0 mod 18446744073709551616) with 0.
    rewrite Z.lxor_0_r, Z.sub_0_r. rewrite swrap32_mod64_small by lia. rewrite Z.abs_eq, swrap32_of_small by lia. reflexivity.
Qed.

Lemma shr30_neg_iff : ltac2:(CDefT.buildp (gd_tbl_P_mpi_cmp_int ()) "Pz,$0.P,(1.(2.(3.(4.+2.+1?.))R1.)(5.R1.(4.+2.+1?.)))(=.(2.+8000000000000000.(:.(;.R2.+1>.)+10000000000000000.))(5.R2.=))")
(* [comment removed for export] *).
Proof.
  intros z Hz. rewrite Z.shiftr_div_pow2 by lia. destruct (Z.lt_ge_cases z 0).
  - assert (C : z / 2^30 = -1 \/ z / 2^30 = -2) by lia. destruct C as [-> | ->]; cbn; lia.
  - assert (C : z / 2^30 = 0 \/ z / 2^30 = 1) by lia. destruct C as [-> | ->]; cbn; lia.
Qed.

Lemma sign_lor_low16 : forall z, -2^31 <= z < 2^31 ->
  Z.lor (Z.shiftr (zlow 64 z) 30) 1 mod 2^16 = (if z <? 0 then -1 else 1) mod 2^16.
Proof.
  intros z Hz. unfold zlow. rewrite Z.shiftr_div_pow2 by lia. destruct (Z.ltb_spec z 0) as [L|L].
  - replace (z mod 2^64) with (z + 2^64) by (symmetry; rewrite <- (Z.mod_add z 1 (2^64)) by lia; apply Z.mod_small; lia).
    assert (C : (z + 2^64) / 2^30 = 2^34 - 1 \/ (z + 2^64) / 2^30 = 2^34 - 2) by lia.
    destruct C as [-> | ->]; reflexivity.
  - rewrite (Z.mod_small z (2^64)) by lia. assert (C : z / 2^30 = 0 \/ z / 2^30 = 1) by lia.
    destruct C as [-> | ->]; reflexivity.
Qed.

Lemma abs_limb : forall z, -2^31 <= z < 2^31 ->
  bv_unsigned (Z_to_bv 64 (zswrap 32 (zlow 32 (Z.lxor z (Z.shiftr z 31) + - Z.shiftr z 31)))) mod 2^32 = Z.abs z.
Proof.
  intros z Hz.
  assert (E : Z.lxor z (Z.shiftr z 31) + - Z.shiftr z 31 = Z.abs z).
  { rewrite Z.shiftr_div_pow2 by lia. destruct (Z.ltb_spec z 0) as [L|L].
    - replace (z / 2^31) with (-1) by lia. rewrite Z.lxor_m1_r. unfold Z.lnot. lia.
    - replace (z / 2^31) with 0 by lia. rewrite Z.lxor_0_r. lia. }
  rewrite E, unsigned_lit_wrap. unfold zswrap, zlow. change (32 - 1) with 31.
  rewrite (Z.mod_small (Z.abs z) (2^32)) by lia.
  destruct (Z.ltb_spec (Z.abs z) (2^31)) as [L|L].
  - rewrite (Z.mod_small (Z.abs z + 2^31) (2^32)) by lia. replace (Z.abs z + 2^31 - 2^31) with (Z.abs z) by lia.
    rewrite (Z.mod_small (Z.abs z) (2^64)) by lia. apply Z.mod_small. lia.
  - assert (A : Z.abs z = 2^31) by lia. rewrite A. reflexivity.
Qed.

Lemma mpd_val_T : forall z a p pd own, -2^31 <= z < 2^31 ->
  mpd_val (mkMPD a (if z <? 0 then -1 else 1) 1 p
             [Z_to_bv 64 (zswrap 32 (zlow 32 (Z.lxor z (Z.shiftr z 31) + - Z.shiftr z 31)))] pd own) = z.
Proof.
  intros z a p pd own Hz. unfold mpd_val. cbn [md_sg md_limbs limbs_val].
  rewrite abs_limb by lia. destruct (Z.ltb_spec z 0); lia.
Qed.

Theorem U_mpi_cmp_int_spec {L : heap_layout} : mpi_cmp_int_stmt usegs U_MPI_CMP_INT.
Proof.
  unfold mpi_cmp_int_stmt, U_MPI_CMP_INT. intros until lo. intros HX PX Hz ST SLO ACL SPA DX DP MI -> ->.
  pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (proj1 ST) as LO0.
  carve_frame 32%nat ST.
  lxp_split_frame [4;4;8;2;2;4;8]%nat.
  lx_run_tac (PLAN [131748] [] 60%N); lx_tree.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  lazymatch goal with
  | H1 : rw_cells _ m1 _ _, H2 : stk _ m1 _ _, H3 : munch _ m m1, H4 : wmono _ m m1, H5 : mem_inv _ m1 |- _ =>
      rename H1 into FR1; rename H2 into ST1; rename H3 into MU1; rename H4 into WM1; rename H5 into MI1
  end.
  pose proof U_mpi_cmp_mpi_spec_o as SPEC. unfold mpi_cmp_mpi_stmt_o, U_MPI_CMP_MPI in SPEC.
  pose proof FR1 as FRk.
  lxp_chunk_split FR1 2%nat FA FB. lxp_chunk_split FB 4%nat FC FD. lxp_chunk_split FA 1%nat FA0 FL.
  pose proof FL as BL. destruct BL as [[_ BL] _].
  lazymatch type of FC with rw_cells _ _ _ [C8 _; C2 _; C2 _; C4 ?pd] =>
  lazymatch type of FL with rw_cells _ _ _ [C4 ?wl] =>
    eapply evt_cut;
    [ eapply SPEC with (LB := LB) (dX := dX)
        (dY := mkMPD (bv_unsigned sp + -24) (if z <? 0 then -1 else 1) 1 (bv_unsigned sp + -28) [wl] pd LStatic)
    | ]
  end end.
  - left. eapply mpd_at_munch_any; [exact HX | exact MU1 | exact WM1 | |].
    + cbn [disjoint_from]. split; [lia | exact I].
    + intros _. cbn [disjoint_from]. split; [lia | exact I].
  - right. unfold stack_opnd. cbn [md_own md_addr md_sg md_n md_p md_limbs md_pad].
    rewrite unsigned_lit by lia.
    split; [reflexivity|]. split.
    { unfold mpi_cells. refine (rw_cells_C2_congr _ _ _ [_] _ _ _ FC _). apply sign_lor_low16; lia. }
    split; [lia|]. split; [lia|]. split; [reflexivity|]. split; [unfold MPI_MAX_LIMBS; lia|].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [exact BL|]. split; [lia|]. split; [lia|].
    destruct (z <? 0); [right| left]; reflexivity.
  - exact PX.
  - cbn. intros E. discriminate E.
  - exact MI1.
  - reflexivity.
  - reflexivity.
  - intros ms' PO. unfold mpi_cmp_post in PO.
    destruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & -> & MU2 & WM2 & MI2).
    rewrite mpd_val_T by lia. rewrite (ret_pc_even 132232) by lia.
    clear FA0 FL FC FD BL SPEC MU2 WM2.
    lx_run_tac (PLAN (@nil Z) [] 40%N); lx_tree.
    lazymatch goal with H : ?l = m1 |- _ => subst l end.
    release_frame FRk ST1 (bv_unsigned sp).
    apply evt_done. unfold mpi_cmp_int_post. cbv beta. do 15 eexists.
    split; [reflexivity|]. split; [assumption|]. split; [assumption|]. split; [assumption| exact ST1].
Qed.
