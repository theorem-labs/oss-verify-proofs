(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk MpiCoreAux MpiWalkAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_mpi_core_mla U_mpi_mul_int_W U_mpi_core_mla_v1 U_mpi_core_mla_vA U_mpi_core_mla_vB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_mpi_core_mla_v () : Init.string Init.list := ["Corelib.Init.Datatypes.nat"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.mul"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.shiftr"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32s"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.same_from"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.sxz"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.lval"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_mul_int_W.mpi_core_mla_vpost"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_layout"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_iface"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_free"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_free.U_FREE"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_calloc"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_add_abs_W.U_CALLOC"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_static"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_written"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.ro_addr"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "RocqVerifyHarness.AgentSubmission.U.U_platform_zeroize.U_MEMSET_FUNC"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_mul_int_W.mpi_mul_int_stmt"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_mul_int_W.U_MPI_MUL_INT"].


(* [comment removed for export] *)
Section Walk.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (D dl S sl ld ls lo b : Z) (ds0 ss : list word).
  Hypothesis Hdl : 0 <= dl <= 10000.
  Hypothesis Hsl : 0 <= sl <= dl.
  Hypothesis Ln : dl <= ld /\ sl <= ls.
  Hypothesis L0 : Z.of_nat (length ds0) = ld.
  Hypothesis LS : Z.of_nat (length ss) = ls.
  Hypothesis DB : 0 < D /\ D + 4 * ld < 2^64.
  Hypothesis SB : 0 <= S /\ S + 4 * ls < 2^64.
  Hypothesis ALD : D mod 4 = 0.
  Hypothesis ALS : S mod 4 = 0.
  Hypothesis NZS : sl = 0 \/ 0 < S.
  Hypothesis SPR : 0 <= bv_unsigned sp < 2^64.
  Hypothesis LO : lo <= bv_unsigned sp - 48.
  Hypothesis SX : D + 4 * ld <= lo \/ bv_unsigned sp <= D.
  Hypothesis SSX : S + 4 * ls <= lo \/ bv_unsigned sp <= S.
  Hypothesis RA : bv_unsigned ra mod 2 = 0.
  Hypothesis HB : 0 <= b < 2^32.

  Notation POST := (mpi_core_mla_vpost usegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D dl ds0 sl ss b lo m).
  Notation W := [(D, D + 4 * dl); (bv_unsigned sp - 48, bv_unsigned sp)].
  Notation FRAME mm := (rw_cells usegs mm (bv_unsigned sp + -48) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0]).
  Notation SFACT0 := ((S = D /\ ss = ds0) \/ (bytes_at usegs m S (u32s ss) /\ (S + 4 * ls <= D \/ D + 4 * ld <= S))).
  Notation DINV mm ds := (u32arr usegs mm D ds /\ Z.of_nat (length ds) = ld
                          /\ munch W m mm /\ wmono usegs m mm /\ mem_inv usegs mm /\ stk usegs mm lo (bv_unsigned sp + -48)).
  Notation VINV ds i k c wc := (same_from (Z.to_nat i) ds ds0 /\ 0 <= c < 2^32 /\ bv_unsigned wc = sxz c
                                /\ lval ds i + 2^(32*i) * c = lval ds0 i + lval ss k * b).
  Notation SP := (Z_to_bv 64 (bv_unsigned sp + -48)).

  (* [comment removed for export] *)
  #[using="Hdl Hsl Ln L0 LS DB SB ALD ALS NZS SPR LO SX SSX RA HB"] Lemma vx8_walk : forall (k : nat) (j n8 : Z) (ds : list word) (mm : mem) (c : Z) (wc : word)
      (xs0 xs1 xs2 xs3 xs4 xs5 : word) (wt0 wn wt2 wa1 wa2 wa3 wa4 wa5 wa6 wa7 wt3 wt4 wt5 wt6 : word),
    Z.to_nat (n8 - j) = k -> 0 <= j < n8 -> n8 = sl / 8 ->
    wt0 = Z_to_bv 64 (S + 32 * j) -> wn = Z_to_bv 64 (n8 - j) -> wt2 = Z_to_bv 64 b -> wa1 = Z_to_bv 64 dl ->
    wa2 = Z_to_bv 64 (S + 32 * j) -> wa3 = Z_to_bv 64 sl -> wa4 = Z_to_bv 64 (D + 32 * j) -> wa5 = Z_to_bv 64 (D + 32 * j) ->
    wa6 = Z_to_bv 64 sl -> Z.shiftr (bv_unsigned wa7) 32 = b ->
    wt3 = Z_to_bv 64 0 -> wt4 = Z_to_bv 64 0 -> wt5 = Z_to_bv 64 4 -> wt6 = Z_to_bv 64 (-5) ->
    DINV mm ds -> SFACT0 -> FRAME mm -> VINV ds (8 * j) (8 * j) c wc ->
    evt usegs POST (MS (mkR ra SP gp tp wt0 wn wt2 xs0 xs1 wc wa1 wa2 wa3 wa4 wa5 wa6 wa7 xs2 xs3 xs4 xs5
                          s6 s7 s8 s9 s10 s11 wt3 wt4 wt5 wt6) F (Z_to_bv 64 0x23a00) fc None mm (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros j n8 ds mm c wc xs0 xs1 xs2 xs3 xs4 xs5 wt0 wn wt2 wa1 wa2 wa3 wa4 wa5 wa6 wa7 wt3 wt4 wt5 wt6
      Hk Hj Hn8 -> -> -> -> -> -> -> -> -> HA7 -> -> -> -> DI AS FR VI; [lia|].
    eapply (vx8_segA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m D dl S sl ld ls lo b ds0 ss);
      try eassumption; try lia; try bveq.
    intros ds4 m4 c4 wc4 ws4 wd4 ya0 ya5 ys3 ys5 -> -> DI4 FR4 VI4 Us4 Ud4.
    eapply (vx8_segB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m D dl S sl ld ls lo b ds0 ss) with (n8 := n8);
      try eassumption; try lia; try bveq.
    intros ds8 m8 c8 wc8 yt0 yt1 ya2 ya4 ya5' ys2 ys3' ys4 ys5' -> -> -> -> -> DI8 FR8 VI8.
    zstep. if_cases Kl; zify_cond Kl.                                   (* [comment removed for export] *)
    - eapply (IH (j + 1) n8); [lia | lia | lia | bveq | bveq | bveq | bveq | bveq | bveq | bveq | bveq | bveq | exact HA7
        | bveq | bveq | bveq | bveq | exact DI8 | exact AS | exact FR8 | replace (8 * (j + 1)) with (8 * j + 8) by lia; exact VI8].
    - eapply (vafter_x8_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m D dl S sl ld ls lo b ds0 ss) with (i0 := 8 * n8);
        try eassumption; try lia; try bveq.
      replace (8 * n8) with (8 * j + 8) by lia. exact VI8.
  Qed.
End Walk.

(* [comment removed for export] *)
Section Body.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (D dl S sl ld ls lo b : Z) (ds0 ss : list word).
  Hypothesis Hdl : 0 <= dl <= 10000.
  Hypothesis Hsl : 0 <= sl <= dl.
  Hypothesis Ln : dl <= ld /\ sl <= ls.
  Hypothesis L0 : Z.of_nat (length ds0) = ld.
  Hypothesis LS : Z.of_nat (length ss) = ls.
  Hypothesis DB : 0 < D /\ D + 4 * ld < 2^64.
  Hypothesis SB : 0 <= S /\ S + 4 * ls < 2^64.
  Hypothesis ALD : D mod 4 = 0.
  Hypothesis ALS : S mod 4 = 0.
  Hypothesis NZS : sl = 0 \/ 0 < S.
  Hypothesis SPR : 0 <= bv_unsigned sp < 2^64.
  Hypothesis LO : lo <= bv_unsigned sp - 48.
  Hypothesis SX : D + 4 * ld <= lo \/ bv_unsigned sp <= D.
  Hypothesis SSX : S + 4 * ls <= lo \/ bv_unsigned sp <= S.
  Hypothesis RA : bv_unsigned ra mod 2 = 0.
  Hypothesis HB : 0 <= b < 2^32.

  (* [comment removed for export] *)
  #[using="Hdl Hsl Ln L0 LS DB SB ALD ALS NZS SPR LO SX SSX RA HB"] Lemma vbody_walk : forall (xt0 xt1 xt2 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    bv_unsigned xa4 mod 2^32 = b -> u32arr usegs m D ds0 ->
    ((S = D /\ ss = ds0) \/ (bytes_at usegs m S (u32s ss) /\ (S + 4 * ls <= D \/ D + 4 * ld <= S))) ->
    mem_inv usegs m -> stk usegs m lo (bv_unsigned sp) ->
    evt usegs (mpi_core_mla_vpost usegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D dl ds0 sl ss b lo m)
      (MS (mkR ra sp gp tp xt0 xt1 xt2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 dl) (Z_to_bv 64 S) (Z_to_bv 64 sl) xa4 xa5 xa6 xa7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 0x239a8) fc None m (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros HA4 HX AS MI ST.
    pose proof (munch_refl [(D, D + 4 * dl); (bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl usegs m) as WM.
    pose proof (Z.div_mod sl 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound sl 8 ltac:(lia)) as MB.
    pose proof (bv_unsigned_in_range 64 xa4) as A4R. change (bv_modulus 64) with (2^64) in A4R.
    assert (VI0 : same_from (Z.to_nat 0) ds0 ds0 /\ 0 <= 0 < 2^32 /\ bv_unsigned (Z_to_bv 64 0) = sxz 0 /\ lval ds0 0 + 2^(32*0) * 0 = lval ds0 0 + lval ss 0 * b).
    { split; [apply same_from_refl|]. split; [lia|]. split; [reflexivity|]. rewrite !lval_0. lia. }
    carve_frame 48%nat ST.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by lia; [exfalso; lia|].
    zstep. zstep. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    zstep. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) => let v := getx R 17%positive in set (xa7' := v) in |- * end.
    assert (HA7 : Z.shiftr (bv_unsigned xa7') 32 = b).
    { subst xa7'. rewrite Z_to_bv_unsigned. change (bv_wrap 64 ?x) with (x mod 18446744073709551616). rewrite shl32_shr32 by lia. exact HA4. }
    clearbody xa7'.
    zstep. (* [comment removed for export] *)
    zstep. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
    - zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2; rewrite ?land_7_mod' in K2.
      + eapply (vx1_entry ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m D dl S sl ld ls lo b ds0 ss) with (i0 := 0);
          try eassumption; try lia; try bveq.
        all: first [ exact (conj HX (conj L0 (conj MU (conj WM (conj MI ST))))) | exact VI0 ].
      + eapply (vjoin_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m D dl S sl ld ls lo b ds0 ss);
          try eassumption; try lia; try bveq.
        all: first [ exact (conj HX (conj L0 (conj MU (conj WM (conj MI ST))))) | replace sl with 0 by lia; exact VI0 ].
    - zstep. rewrite HA7. zstep. zstep. zstep. zstep. zstep. zstep.
      eapply (vx8_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m D dl S sl ld ls lo b ds0 ss) with (k := Z.to_nat (sl / 8)) (j := 0) (n8 := sl / 8);
        try eassumption; try lia; try bveq.
      all: first [ exact (conj HX (conj L0 (conj MU (conj WM (conj MI ST))))) | exact VI0 ].
  Qed.
End Body.

Theorem U_mpi_core_mla_vspec : mpi_core_mla_vstmt usegs U_MPI_CORE_MLA.
Proof.
  unfold mpi_core_mla_vstmt, U_MPI_CORE_MLA.
  intros until ss. intros HX HS Hdl Hsl LX LS SLD DA ALD ALS NZD NZS DTOP STOP ST LO SPA SX SSX MI RA HBb -> -> -> ->.
  unfold MPI_CORE_MLA_STACK in *.
  pose proof (u32arr_bound _ _ _ _ HX) as DB. pose proof (u32ro_bound _ _ _ _ HS) as SB.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
  pose proof (Z.mod_pos_bound (bv_unsigned a4) (2^32) ltac:(lia)) as HB. rewrite <- HBb in HB.
  assert (AS : (S = D /\ ss = ds) \/ (bytes_at usegs m S (u32s ss) /\ (S + 4 * Z.of_nat (length ss) <= D \/ D + 4 * Z.of_nat (length ds) <= S))).
  { destruct DA as [[ES EQ]|DIS]; [left; split; [exact ES| exact EQ] | right; split; [exact HS | exact DIS]]. }
  eapply vbody_walk; try eassumption; try reflexivity; try lia. all: symmetry; exact HBb.
Qed.

(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_platform_zeroize U_mpi_free U_mpi_add_abs_W U_mpi_mul_int.

Theorem U_mpi_mul_int_spec_closed : ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_mla_v ()) "PL,$2>.PHI,(2?.$11.R1.)P,(5.$1.(30.R2.)$31.)P,(5.$1.(32.R3.)$33.)P,(9.=(34.R4.))P,Pa,$1.P,(35.R6.R1.)(36.R7.R2.)P,(8.(9.(37.R6.)(38.R6.))(9.(39.R6.)(3:.R6.)))P,Ph,(3;.$11.R7.R6.)PLB,(2.$3<.)Pm,P,(3.&40.)(4.(3.&8.))Pmo,$3=.P,(3>.$11.R;.R:.R4.R3.R2.R1.)(3?.$1.(40.(16.$1.$1.)$1.(41.$1.$1.)R4.))P,Pa,$1.P,(5.$42.(43.$11.(44.R1.))$45.)P,(8.(9.=R2.)(:.R2.(24.+2.+40.)))(8.(9.(37.R;.)R3.)(:.R3.(3:.R;.)))P,(9.(3:.R9.)(46.R9.))PMSF,$1.P,(5.$1.R1.$47.)(48.$11.R<.R;.$49.R2.)")
(* [comment removed for export] *).
Proof. intros. eapply U_mpi_mul_int_spec; try eassumption. exact U_mpi_core_mla_vspec. Qed.
