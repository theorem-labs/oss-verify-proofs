(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux CellsX MpiCoreAux HeapIface ZBridge.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import PImg P_mpi_cmp.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_mpi_cmp_int () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.eq"; "stdpp.bitvector.definitions.bv_swrap"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.lxor"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.shiftr"; "Stdlib.ZArith.BinInt.Z.abs"; "Corelib.Init.Logic.iff"; "stdpp.bitvector.definitions.bv"; "OSSVerify.KrLib.Lib.MpiCoreAux.lval"; "Corelib.Init.Logic.not"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.Lib.Exec.evt"; "OSSVerify.KrLib.P.PImg.psegs"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.P.P_mpi_cmp.SIGF"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Stdlib.ZArith.BinInt.Z.add"].


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

Section WalkP.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (X P n sg : Z) (xs : list word) (pad : word) (z lo : Z).
  Hypothesis CX : rw_cells psegs m X [C8 (Z_to_bv 64 P); C2 (Z_to_bv 64 sg); C2 (Z_to_bv 64 n); C4 pad].
  Hypothesis HX : bytes_at psegs m P (u32s xs).
  Hypothesis LX : Z.of_nat (length xs) = n.
  Hypothesis Hn : 0 <= n <= 10000.
  Hypothesis SG : sg = 1 \/ sg = -1.
  Hypothesis XB : 0 <= X /\ X + 16 <= 2^64.
  Hypothesis PB : n = 0 \/ 0 < P /\ P mod 4 = 0.
  Hypothesis Hz : -2^31 <= z < 2^31.
  Hypothesis ST : stk psegs m lo (bv_unsigned sp).
  Hypothesis MI : mem_inv psegs m.

  Let POST := mpi_cmp_int_post psegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z.sgn (sg * lval xs n - z)) lo m.

  (* [comment removed for export] *)
  #[using="P pad CX HX LX SG PB Hz ST MI"] Lemma p_int_tail : ltac2:(CDefT.buildp (gd_tbl_P_mpi_cmp_int ()) "Pa4,(>.&40.)Pa5,(>.&40.)Pa6,(>.&40.)Pa7,(>.&40.)P,(6.$0.(?.Vxs,Vn,)(?.Vxs,+1.))P,(2.+1.Vn,)P,(10.(6.$0.Vz,=))P,(5.=(11.Vsg,Vz,))(12.$13.VPOST,(14.(15.Vra,Vsp,Vgp,Vtp,Vt0,Vt1,Vt2,Vs0,Vs1,(16.&40.VX,)(16.&40.Vz,)(16.&40.+1.)(16.&40.Vsg,)R8.R7.R6.R5.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(16.&40.+1?:48.)Vfc,(17.(>.&40.))Vm,(18.$13.)))")
(* [comment removed for export] *).
  Proof.
    intros a4 a5 a6 a7 IV N1 NE SS.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl psegs m) as WM.
    zstep. zstep. zstep. rewrite sint_abs32 by lia.
    pose proof (swrap32_mod64 (Z.abs z)) as AZ. rewrite (Z.mod_small (Z.abs z)) in AZ by lia. change (2^64)%Z with 18446744073709551616%Z in AZ.
    zstep. zstep. zstep. zstep. zstep. if_false.
    destruct (nth_error xs 0%nat) as [wx|] eqn:NX; [| apply nth_error_None in NX; cbn in NX; lia].
    pose proof (u32ro_read psegs m P xs 0 wx _ HX NX ltac:(lia) eq_refl) as RDX.
    zstep. zstep. zstep. clear RDX.
    pose proof (limb32_of_read xs 1 wx NX) as LXr. change (Z.to_nat (1 - 1)) with 0%nat in LXr.
    pose proof (Z.mod_pos_bound (bv_unsigned wx) (2^32) ltac:(lia)) as Bx.
    assert (V1 : lval xs 1 = limb32 xs 0).
    { pose proof (lval_succ xs 0 ltac:(lia)) as E. rewrite lval_0 in E. change (2 ^ (32 * 0)) with 1 in E. change (Z.to_nat 0) with 0%nat in E. change (0 + 1) with 1 in E. lia. }
    assert (Ba : 0 <= Z.abs z < 2^32) by lia.
    zstep. if_cases K1; zify_cond K1; rewrite ?bv_unsigned_sx32, ?AZ in K1.
    - (* [comment removed for export] *)
      apply (proj1 (sxz_lt_iff _ _ Ba Bx)) in K1.
      zstep. zstep. replace (Z_to_bv 64 sg) with (Z_to_bv 64 (Z.sgn (sg * lval xs n - z))); [finish| f_equal].
      rewrite IV, V1, LXr. destruct SG as [-> | ->]; [apply Z.sgn_pos; lia| apply Z.sgn_neg; lia].
    - apply (proj1 (sxz_le_iff _ _ Bx Ba)) in K1.
      zstep. zstep. if_cases K2; zify_cond K2; rewrite ?bv_unsigned_sx32, ?AZ in K2.
      + (* [comment removed for export] *)
        apply (proj1 (sxz_le_iff _ _ Ba Bx)) in K2.
        zstep. zstep. if_true. zstep. zstep.
        replace (Z_to_bv 64 0) with (Z_to_bv 64 (Z.sgn (sg * lval xs n - z))); [finish| f_equal].
        rewrite IV, V1, LXr. destruct SG as [-> | ->]; apply Z.sgn_null; lia.
      + apply (proj1 (sxz_lt_iff _ _ Bx Ba)) in K2.
        zstep. zstep.
        replace (Z_to_bv 64 (0 - sg mod 18446744073709551616)) with (Z_to_bv 64 (Z.sgn (sg * lval xs n - z))); [finish|].
        apply Z_to_bv_eqm. change 18446744073709551616 with (2^64). rewrite Zminus_mod_idemp_r. f_equal.
        rewrite IV, V1, LXr. destruct SG as [-> | ->]; [apply Z.sgn_neg; lia| apply Z.sgn_pos; lia].
  Qed.

  (* [comment removed for export] *)
  #[using="P pad CX HX LX Hn SG PB Hz ST MI"] Lemma p_int_stage2 : ltac2:(CDefT.buildp (gd_tbl_P_mpi_cmp_int ()) "Pi,$0.Pa3,(>.&40.)Pa4,(>.&40.)Pa5,(>.&40.)Pa6,(>.&40.)Pa7,(>.&40.)P,(19.Vxs,Vn,R6.)(12.$13.VPOST,(14.(15.Vra,Vsp,Vgp,Vtp,Vt0,Vt1,Vt2,Vs0,Vs1,(16.&40.VX,)(16.&40.Vz,)(16.&40.R7.)R6.R5.R4.R3.R2.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(16.&40.+1?:0<.)Vfc,(17.(>.&40.))Vm,(18.$13.)))")
(* [comment removed for export] *).
  Proof.
    intros i a3 a4 a5 a6 a7 SX. dpose SX as (I1 & I2 & I3).
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl psegs m) as WM.
    pose proof (lval_range xs i ltac:(lia)) as RX.
    zstep. set (j := Z.b2z (0 <? z mod 18446744073709551616)) in *.
    assert (Hj : (j = 0 /\ z = 0) \/ (j = 1 /\ z <> 0)).
    { subst j. destruct (Z.eq_dec z 0) as [->|NE]; [left; split; reflexivity| right; split; [| exact NE]].
      destruct (Z.lt_ge_cases z 0).
      - replace (z mod 18446744073709551616) with (z + 2^64) by (symmetry; rewrite <- (Z.mod_add z 1 18446744073709551616) by lia; apply Z.mod_small; lia).
        destruct (Z.ltb_spec 0 (z + 2^64)); [reflexivity| lia].
      - rewrite Z.mod_small by lia. destruct (Z.ltb_spec 0 z); [reflexivity| lia]. }
    clearbody j.
    zstep. zstep. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *) assert (i = 0 /\ j = 0) as [-> ->] by (rewrite Z.lor_comm in K0 || idtac; apply Z.lor_eq_0_iff in K0; lia).
      zstep. zstep. replace (Z_to_bv 64 0) with (Z_to_bv 64 (Z.sgn (sg * lval xs n - z))) by (f_equal; rewrite I2, !lval_0; lia). finish.
    - zstep. if_cases K1; zify_cond K1.
      2:{ (* [comment removed for export] *) zstep. rewrite sx16_small by lia. zstep.
          replace (Z_to_bv 64 sg) with (Z_to_bv 64 (Z.sgn (sg * lval xs n - z))); [finish| f_equal].
          destruct I3 as [->|I3]; [lia|]. rewrite I2.
          assert (Z.abs z < lval xs i).
          { destruct Hj as [[-> ->]|[-> NE]]; [pose proof (pow32_pos (i - 1)); lia|]. pose proof (pow32_le 1 (i - 1) ltac:(lia)). lia. }
          destruct SG as [-> | ->]; [apply Z.sgn_pos; lia| apply Z.sgn_neg; lia]. }
      zstep. zstep. if_cases K2; zify_cond K2.
      2:{ (* [comment removed for export] *) zstep. zstep. zstep. rewrite signed_lit_small by lia. rewrite to_sign64 by lia.
          match goal with |- context [Z_to_bv 64 (0 - ?v)] =>
            replace (Z_to_bv 64 (0 - v)) with (Z_to_bv 64 (Z.sgn (sg * lval xs n - z))); [finish|] end.
          assert (i = 0 /\ j = 1) as [-> ->] by lia. rewrite I2, lval_0. destruct Hj as [[? ?]|[_ NE]]; [lia|].
          apply Z_to_bv_eqm. destruct (Z.ltb_spec z 0); [rewrite Z.sgn_pos by lia| rewrite Z.sgn_neg by lia]; reflexivity. }
      assert (i = 1 /\ j = 1) as [-> ->] by (destruct Hj as [[-> ->]|[-> NE]]; [exfalso; assert (i = 0) as -> by lia; rewrite Z.lor_0_l in K0; cbn in K0; lia| lia]).
      destruct Hj as [[? _]|[_ NE]]; [lia|]. clear K0 K1 K2.
      rewrite signed_lit_small by lia.
      zstep. rewrite sx16_small by lia. zstep.
      destruct SG as [Es|Es]; (zstep; if_cases K3; zify_cond K3).
      all: try (apply Bool.andb_false_iff in K3; destruct K3 as [K3|K3]; apply Z.ltb_ge in K3).
      all: try (exfalso; lia).
      all: (zstep; if_cases K4; zify_cond K4).
      all: first [apply (proj1 (shr30_neg_iff z Hz)) in K4 | assert (~ z < 0) by (intros Hn0; apply (proj2 (shr30_neg_iff z Hz)) in Hn0; lia); clear K4].
      all: destruct I3 as [I3|I3]; [lia|]; change (2 ^ (32 * (1 - 1))) with 1 in I3; pose proof (lval_range xs 1 ltac:(lia)) as R1.
      + (* [comment removed for export] *) zstep. zstep. replace (Z_to_bv 64 1) with (Z_to_bv 64 (Z.sgn (sg * lval xs n - z))) by (f_equal; rewrite I2; apply Z.sgn_pos; lia). finish.
      + apply p_int_tail; [exact I2| lia| exact NE| lia].
      + apply p_int_tail; [exact I2| lia| exact NE| lia].
      + (* [comment removed for export] *) zstep. if_cases K5; zify_cond K5; [exfalso; clear - K5 Es; lia|].
        zstep. zstep. replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (Z.sgn (sg * lval xs n - z))) by (f_equal; rewrite I2; apply Z.sgn_neg; lia). finish.
  Qed.

  (* [comment removed for export] *)
  #[using="pad CX HX LX Hn SG PB Hz ST MI"] Lemma p_int_loop1 : ltac2:(CDefT.buildp (gd_tbl_P_mpi_cmp_int ()) "Pk,$1:.Pr,$0.Pw12,(>.&40.)Pw13,(>.&40.)Pa4,(>.&40.)Pa5,(>.&40.)Pa6,(>.&40.)Pa7,(>.&40.)P,(6.$1:.(1;.R7.)R8.)P,(1.(2.+1.R8.)(2.R8.Vn,))P,(6.$0.(?.Vxs,Vn,)(?.Vxs,R9.))P,(6.(>.&40.)R9.(16.&40.R:.))P,(6.(>.&40.)R9.(16.&40.(8.(1<.VP,(11.+4.R;.))+4.)))(12.$13.VPOST,(14.(15.Vra,Vsp,Vgp,Vtp,Vt0,Vt1,Vt2,Vs0,Vs1,(16.&40.VX,)(16.&40.Vz,)R;.R:.R9.R8.R7.R6.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(16.&40.+1?9?8.)Vfc,(17.(>.&40.))Vm,(18.$13.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros r w12 w13 a4 a5 a6 a7 Hk Hr INV -> ->; [lia|].
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl psegs m) as WM.
    destruct (nth_error xs (Z.to_nat (r - 1))) as [wx|] eqn:NX; [| apply nth_error_None in NX; lia].
    pose proof (u32ro_read psegs m P xs (r - 1) wx _ HX NX ltac:(lia) eq_refl) as RDX.
    zstep. clear RDX. pose proof (limb32_of_read xs r wx NX) as LXr.
    pose proof (Z.mod_pos_bound (bv_unsigned wx) (2^32) ltac:(lia)) as Bx.
    zstep. if_cases K1; zify_cond K1; rewrite ?bv_unsigned_sx32 in K1.
    - assert (NZ : limb32 xs (Z.to_nat (r - 1)) <> 0) by (rewrite LXr; intros E; apply K1; rewrite E; reflexivity).
      apply p_int_stage2. split; [lia|]. split; [exact INV|]. right. apply lval_top_nonzero; [lia| exact NZ].
    - apply (proj1 (sxz_zero_iff _ Bx)) in K1.
      zstep. zstep. zstep. if_cases K2; zify_cond K2.
      + eapply (IH (r - 1)); [lia| lia| rewrite INV; apply lval_drop_zero; lia| f_equal; lia| f_equal; lia].
      + replace (Z_to_bv 64 (r + -1)) with (Z_to_bv 64 0) by (f_equal; lia).
        apply p_int_stage2. split; [lia|]. split; [| left; reflexivity].
        rewrite INV, (lval_drop_zero xs r) by lia. replace (r - 1) with 0 by lia. reflexivity.
  Qed.

  #[using="P pad CX HX LX Hn SG PB Hz ST MI"] Lemma p_cmp_int : ltac2:(CDefT.buildp (gd_tbl_P_mpi_cmp_int ()) "Pa2,(>.&40.)Pa3,(>.&40.)Pa4,(>.&40.)Pa5,(>.&40.)Pa6,(>.&40.)Pa7,(>.&40.)(12.$13.VPOST,(14.(15.Vra,Vsp,Vgp,Vtp,Vt0,Vt1,Vt2,Vs0,Vs1,(16.&40.VX,)(16.&40.Vz,)R6.R5.R4.R3.R2.R1.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(16.&40.+1?9>0.)Vfc,(17.(>.&40.))Vm,(18.$13.)))")
(* [comment removed for export] *).
  Proof.
    intros a2 a3 a4 a5 a6 a7.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl psegs m) as WM.
    zstep. rewrite zx16_small by lia. zstep. if_cases K0; zify_cond K0.
    - apply p_int_stage2. split; [lia|]. split; [reflexivity| left; exact K0].
    - zstep. zstep. zstep. zstep. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
      eapply (p_int_loop1 (Z.to_nat n) n); [reflexivity| lia| reflexivity| reflexivity| f_equal; lia].
  Qed.
End WalkP.

Theorem P_mpi_cmp_int_spec {L : heap_layout} : mpi_cmp_int_stmt psegs P_MPI_CMP_INT.
Proof.
  unfold mpi_cmp_int_stmt, P_MPI_CMP_INT. intros until lo. intros HX PX Hz ST LO ACL SPA DA DP MI -> ->.
  destruct (mpd_raw _ _ _ _ HX PX) as (CX & BX & LX & NX & SX & ABX & PBX).
  unfold mpd_val. fold (mpd_abs dX). rewrite mpd_abs_lval by assumption.
  eapply p_cmp_int; eassumption.
Qed.
