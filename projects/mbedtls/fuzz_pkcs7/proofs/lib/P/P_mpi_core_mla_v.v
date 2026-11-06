(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk MpiCoreAux MpiWalkAux.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import PImg P_mpi_core_mla P_mpi_mul_int_W P_mpi_core_mla_v1 P_mpi_core_mla_vA P_mpi_core_mla_vB.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_mpi_core_mla_v () : Init.string Init.list := ["Corelib.Init.Datatypes.nat"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.mul"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.shiftr"; "stdpp.bitvector.definitions.bv_unsigned"; "OSSVerify.KrLib.Lib.Arr.u32arr"; "OSSVerify.KrLib.P.PImg.psegs"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "OSSVerify.KrLib.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Frame.wmono"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.Lib.Frame.stk"; "Corelib.Init.Logic.or"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "OSSVerify.KrLib.Lib.Arr.u32s"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.CB"; "OSSVerify.KrLib.Lib.Cells.C8"; "OSSVerify.KrLib.Lib.MpiCoreAux.same_from"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.KrLib.Lib.MpiCoreAux.sxz"; "OSSVerify.KrLib.Lib.MpiCoreAux.lval"; "OSSVerify.KrLib.Lib.Exec.evt"; "OSSVerify.KrLib.P.P_mpi_mul_int_W.mpi_core_mla_vpost"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "Stdlib.ZArith.BinInt.Z.modulo"; "OSSVerify.KrLib.Lib.HeapIface.heap_layout"; "OSSVerify.KrLib.Lib.HeapIface.heap_iface"; "OSSVerify.KrLib.Lib.HeapIface.hl_free"; "OSSVerify.KrLib.P.P_mpi_free.P_FREE"; "OSSVerify.KrLib.Lib.HeapIface.hl_calloc"; "OSSVerify.KrLib.P.P_mpi_add_abs_W.P_CALLOC"; "OSSVerify.KrLib.Lib.HeapIface.hl_stack"; "OSSVerify.KrLib.Lib.HeapIface.hl_static"; "OSSVerify.KrLib.Lib.HeapIface.hl_written"; "OSSVerify.KrLib.Lib.HeapIface.hl_img_lo"; "OSSVerify.KrLib.Lib.HeapIface.hl_data_lo"; "OSSVerify.KrLib.Lib.HeapIface.hl_data_hi"; "OSSVerify.KrLib.Lib.HeapIface.hl_img_hi"; "OSSVerify.KrLib.Lib.HeapIface.HST"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "OSSVerify.KrLib.Lib.HeapIface.HEAP"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.bool"; "OSSVerify.KrLib.Lib.Mem.ro_addr"; "OSSVerify.KrLib.Lib.Mem.wa"; "Corelib.Init.Datatypes.true"; "OSSVerify.KrLib.Lib.HeapIface.alloc_ceiling"; "OSSVerify.KrLib.P.P_platform_zeroize.P_MEMSET_FUNC"; "OSSVerify.KrLib.P.P_mpi_mul_int_W.mpi_mul_int_stmt"; "OSSVerify.KrLib.P.P_mpi_mul_int_W.P_MPI_MUL_INT"].


(* [comment removed for export] *)
Section Walk.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (D dl S sl ld ls lo b : Z) (ds0 ss : list word) (junk : list byte).
  Hypothesis Hdl : 0 <= dl <= 10000.
  Hypothesis Hsl : 0 <= sl <= dl.
  Hypothesis Ln : dl <= ld /\ sl <= ls.
  Hypothesis L0 : Z.of_nat (length ds0) = ld.
  Hypothesis LS : Z.of_nat (length ss) = ls.
  Hypothesis DB : 0 < D /\ D + 4 * ld <= 2^64.
  Hypothesis SB : 0 <= S /\ S + 4 * ls <= 2^64.
  Hypothesis NZS : sl = 0 \/ 0 < S.
  Hypothesis SPR : 0 <= bv_unsigned sp < 2^64.
  Hypothesis LO : lo <= bv_unsigned sp - 48.
  Hypothesis SX : D + 4 * ld <= lo \/ bv_unsigned sp <= D.
  Hypothesis SSX : S + 4 * ls <= lo \/ bv_unsigned sp <= S.
  Hypothesis RA : bv_unsigned ra mod 2 = 0.
  Hypothesis HB : 0 <= b < 2^32.

  Notation POST := (mpi_core_mla_vpost psegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D dl ds0 sl ss b lo m).
  Notation W := [(D, D + 4 * dl); (bv_unsigned sp - 48, bv_unsigned sp)].
  Notation FRAME mm := (rw_cells psegs mm (bv_unsigned sp + -16) [CB 8 junk; C8 s0]).
  Notation SFACT0 := ((S = D /\ ss = ds0) \/ (bytes_at psegs m S (u32s ss) /\ (S + 4 * ls <= D \/ D + 4 * ld <= S))).
  Notation DINV mm ds := (u32arr psegs mm D ds /\ Z.of_nat (length ds) = ld
                          /\ munch W m mm /\ wmono psegs m mm /\ mem_inv psegs mm /\ stk psegs mm lo (bv_unsigned sp + -16)).
  Notation VINV ds i k c wc := (same_from (Z.to_nat i) ds ds0 /\ 0 <= c < 2^32 /\ bv_unsigned wc = sxz c
                                /\ lval ds i + 2^(32*i) * c = lval ds0 i + lval ss k * b).

  (* [comment removed for export] *)
  #[using="Hdl Hsl Ln L0 LS DB SB NZS SPR LO SX SSX HB"] Lemma vx8_walk : ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_mla_v ()) "Pk,$0.Pj,$1.Pn8,$1.Pds,(2.(3.&40.))Pmm,P,(3.&40.)(4.(3.&8.))Pc,$1.Pwc,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)Pxs0,(3.&40.)Pxa4,(3.&40.)Pwps,(3.&40.)Pwpd,(3.&40.)Pwe,(3.&40.)P,(5.$0.(6.(7.R10.R11.))R12.)P,(8.(9.=R12.)(:.R12.R11.))P,(9.(;.+8.R12.)Vsl,)P,(:.(7.Vsl,(;.+8.R13.))+8.)P,(5.(3.&40.)R7.(<.&40.(=.VS,(;.+20.R15.))))P,(5.(3.&40.)R7.(<.&40.(=.VD,(;.+20.R16.))))P,(5.(3.&40.)R7.(<.&40.(=.VS,(;.+20.R16.))))P,(5.$1.(>.(?.&40.R;.)+20.)Vb,)P,(8.(10.$11.R16.VD,R17.)(8.(5.$1.(12.(13.(3.&40.)R17.))Vld,)(8.(14.(15.(16.$1.$1.)(17.$1.$1.VD,(=.VD,(;.+4.Vdl,)))(15.(16.$1.$1.)(17.$1.$1.(7.(?.&40.Vsp,)+30.)(?.&40.Vsp,))(18.(16.$1.$1.))))Vm,R16.)(8.(19.$11.Vm,R16.)(8.(1:.$11.R16.)(1;.$11.R16.Vlo,(=.(?.&40.Vsp,)-10.)))))))P,(1<.(8.(5.$1.VS,VD,)(5.(2.(3.&40.))Vss,Vds0,))(8.(1=.$11.Vm,VS,(1>.Vss,))(1<.(9.(=.VS,(;.+4.Vls,))VD,)(9.(=.VD,(;.+4.Vld,))VS,))))P,(1?.$11.R18.(=.(?.&40.Vsp,)-10.)(15.$20.(21.#8.Vjunk,)(15.$20.(22.Vs0,)(18.$20.))))P,(8.(23.(3.&40.)(6.(;.+8.R1<.))R1:.Vds0,)(8.(8.(9.=R18.)(:.R18.(24.+2.+20.)))(8.(5.$1.(?.&40.R17.)(25.R18.))(5.$1.(=.(26.R1:.(;.+8.R1<.))(;.(24.+2.(;.+20.(;.+8.R1<.)))R18.))(=.(26.Vds0,(;.+8.R1<.))(;.(26.Vss,(;.+8.R1<.))Vb,))))))(27.$11.(28.$11.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VD,Vdl,Vds0,Vsl,Vss,Vb,Vlo,Vm,)(29.(2:.Vra,(<.&40.(=.(?.&40.Vsp,)-10.))Vgp,Vtp,R=.R17.R16.R11.Vs1,R18.(<.&40.Vdl,)R?.(<.&40.(7.Vsl,(;.+8.R1<.)))R10.R>.(<.&40.Vsl,)(<.&40.Vb,)Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R15.R14.R13.R12.)VF,(<.&40.+22:38.)Vfc,(2;.(3.&40.))R1:.(2<.$11.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros j n8 ds mm c wc xt1 xt2 xt3 xt4 xt5 xt6 xs0 xa4 wps wpd we Hk Hj Hn8 Hr -> -> -> HA4 DI AS FR VI; [lia|].
    eapply (vx8_segA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m D dl S sl ld ls lo b ds0 ss junk); try eassumption; try lia; try reflexivity.
    intros ds4 m4 c4 wc4 ws4 wd4 wd5 wd6 wd7 wv4 yt1 DI4 FR4 VI4 Us4 Ud4 Ud5 Ud6 Ud7.
    eapply (vx8_segB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m D dl S sl ld ls lo b ds0 ss junk); try eassumption; try lia; try reflexivity.
    intros ds8 m8 c8 wc8 zt1 zt2 zt3 zt4 zt5 zt6 zs0 DI8 FR8 VI8.
    dpose DI8 as (HX8 & LX8 & MU8 & WM8 & MI8 & ST8).
    zstep. ptr_cases Kl.                                                (* [comment removed for export] *)
    - eapply (IH (j + 1) n8); [lia | lia | lia | lia | f_equal; lia | f_equal; lia | reflexivity | exact HA4 | exact DI8 | exact AS | exact FR8
        | replace (8 * (j + 1)) with (8 * j + 8) by lia; exact VI8].
    - eapply (vafter_x8_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m D dl S sl ld ls lo b ds0 ss junk) with (i0 := 8 * n8);
        try eassumption; try lia; try (f_equal; lia).
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
  Hypothesis DB : 0 < D /\ D + 4 * ld <= 2^64.
  Hypothesis SB : 0 <= S /\ S + 4 * ls <= 2^64.
  Hypothesis NZS : sl = 0 \/ 0 < S.
  Hypothesis SPR : 0 <= bv_unsigned sp < 2^64.
  Hypothesis LO : lo <= bv_unsigned sp - 48.
  Hypothesis SX : D + 4 * ld <= lo \/ bv_unsigned sp <= D.
  Hypothesis SSX : S + 4 * ls <= lo \/ bv_unsigned sp <= S.
  Hypothesis RA : bv_unsigned ra mod 2 = 0.
  Hypothesis HB : 0 <= b < 2^32.

  (* [comment removed for export] *)
  #[using="Hdl Hsl Ln L0 LS DB SB NZS SPR LO SX SSX HB"] Lemma vbody_walk : ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_mla_v ()) "Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxa0,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa7,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(5.$1.(2=.(?.&40.R6.)(24.+2.+20.))Vb,)P,(10.$11.Vm,VD,Vds0,)P,(1<.(8.(5.$1.VS,VD,)(5.(2.(3.&40.))Vss,Vds0,))(8.(1=.$11.Vm,VS,(1>.Vss,))(1<.(9.(=.VS,(;.+4.Vls,))VD,)(9.(=.VD,(;.+4.Vld,))VS,))))P,(1:.$11.Vm,)P,(1;.$11.Vm,Vlo,(?.&40.Vsp,))(27.$11.(28.$11.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VD,Vdl,Vds0,Vsl,Vss,Vb,Vlo,Vm,)(29.(2:.Vra,Vsp,Vgp,Vtp,R10.R?.R>.Vs0,Vs1,R=.(<.&40.Vdl,)(<.&40.VS,)R<.R;.(<.&40.VD,)(<.&40.Vsl,)R:.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R9.R8.R7.R6.)VF,(<.&40.+22:10.)Vfc,(2;.(3.&40.))Vm,(2<.$11.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros HA4 HX AS MI ST.
    pose proof (munch_refl [(D, D + 4 * dl); (bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl psegs m) as WM.
    pose proof (Z.div_mod sl 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound sl 8 ltac:(lia)) as MB.
    pose proof (bv_unsigned_in_range 64 xa4) as A4R. change (bv_modulus 64) with (2^64) in A4R.
    assert (VI0 : same_from (Z.to_nat 0) ds0 ds0 /\ 0 <= 0 < 2^32 /\ bv_unsigned (Z_to_bv 64 0) = sxz 0 /\ lval ds0 0 + 2^(32*0) * 0 = lval ds0 0 + lval ss 0 * b).
    { split; [apply same_from_refl|]. split; [lia|]. split; [reflexivity|]. rewrite !lval_0. lia. }
    carve_frame 16%nat ST.
    zstep. zstep.
    zstep. rewrite land_7_mod'. replace (sl mod 8) with (sl - 8 * (sl / 8)) by lia.
    zstep. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    zstep. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) => let v := getx R 14%positive in set (xa4' := v) in |- * end.
    assert (HA4' : Z.shiftr (bv_unsigned xa4') 32 = b).
    { subst xa4'. rewrite Z_to_bv_unsigned. change (bv_wrap 64 ?x) with (x mod 18446744073709551616). rewrite shl32_shr32 by lia. exact HA4. }
    clearbody xa4'.
    zstep. (* [comment removed for export] *)
    zstep. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
    - eapply (vafter_x8_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m D dl S sl ld ls lo b ds0 ss);
        try eassumption; try lia; try (f_equal; lia).
      + exact (conj HX (conj L0 (conj MU (conj WM (conj MI ST))))).
      + replace (8 * (sl / 8)) with 0 by lia. exact VI0.
    - zstep. rewrite HA4'. zstep. rewrite !Z.shiftl_mul_pow2 by lia. change (2^5) with 32. zstep.
      eapply (vx8_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m D dl S sl ld ls lo b ds0 ss) with (k := Z.to_nat (sl / 8)) (j := 0) (n8 := sl / 8);
        try eassumption; try lia; try (f_equal; lia).
      exact (conj HX (conj L0 (conj MU (conj WM (conj MI ST))))).
  Qed.
End Body.

Theorem P_mpi_core_mla_vspec : mpi_core_mla_vstmt psegs P_MPI_CORE_MLA.
Proof.
  unfold mpi_core_mla_vstmt, P_MPI_CORE_MLA.
  intros until ss. intros HX HS Hdl Hsl LX LS SLD DA ALD ALS NZD NZS DTOP STOP ST LO SPA SX SSX MI RA HBb -> -> -> ->.
  unfold MPI_CORE_MLA_STACK in *.
  pose proof (u32arr_bound _ _ _ _ HX) as DB. pose proof (u32ro_bound _ _ _ _ HS) as SB.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
  pose proof (Z.mod_pos_bound (bv_unsigned a4) (2^32) ltac:(lia)) as HB. rewrite <- HBb in HB.
  assert (AS : (S = D /\ ss = ds) \/ (bytes_at psegs m S (u32s ss) /\ (S + 4 * Z.of_nat (length ss) <= D \/ D + 4 * Z.of_nat (length ds) <= S))).
  { destruct DA as [[ES EQ]|DIS]; [left; split; [exact ES| exact EQ] | right; split; [exact HS | exact DIS]]. }
  zstep. zstep. zstep. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by lia.
  2: zstep.
  1: assert (sl = dl) as -> by lia.
  all: eapply vbody_walk; try eassumption; try reflexivity; try lia. all: symmetry; exact HBb.
Qed.

(* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_platform_zeroize P_mpi_free P_mpi_add_abs_W P_mpi_mul_int.

Theorem P_mpi_mul_int_spec_closed : ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_mla_v ()) "PL,$2>.PHI,(2?.$11.R1.)P,(5.$1.(30.R2.)$31.)P,(5.$1.(32.R3.)$33.)P,(9.=(34.R4.))P,Pa,$1.P,(35.R6.R1.)(36.R7.R2.)P,(8.(9.(37.R6.)(38.R6.))(9.(39.R6.)(3:.R6.)))P,Ph,(3;.$11.R7.R6.)PLB,(2.$3<.)Pm,P,(3.&40.)(4.(3.&8.))Pmo,$3=.P,(3>.$11.R;.R:.R4.R3.R2.R1.)(3?.$1.(40.(16.$1.$1.)$1.(41.$1.$1.)R4.))P,Pa,$1.P,(5.$42.(43.$11.(44.R1.))$45.)P,(8.(9.=R2.)(:.R2.(24.+2.+40.)))(8.(9.(37.R;.)R3.)(:.R3.(3:.R;.)))P,(9.(3:.R9.)(46.R9.))PMSF,$1.P,(5.$1.R1.$47.)(48.$11.R<.R;.$49.R2.)")
(* [comment removed for export] *).
Proof. intros. eapply P_mpi_mul_int_spec; try eassumption. exact P_mpi_core_mla_vspec. Qed.
