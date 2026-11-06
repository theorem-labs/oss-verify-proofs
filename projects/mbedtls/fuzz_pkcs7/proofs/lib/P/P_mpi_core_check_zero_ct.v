(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk MpiCoreAux.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import PImg.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_mpi_core_check_zero_ct () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "OSSVerify.KrLib.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.Lib.Frame.munch"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Frame.ivl"; "OSSVerify.KrLib.Lib.Frame.wmono"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.Lib.MpiCoreAux.ct_mask"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Logic.iff"; "OSSVerify.KrLib.Lib.MpiCoreAux.limbs_zero"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "OSSVerify.KrLib.Lib.Arr.u32s"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "OSSVerify.KrLib.Lib.Exec.evt"; "mpi_core_check_zero_ct_post"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.KrLib.P.PImg.psegs"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "stdpp.bitvector.definitions.bv_unsigned"].


Definition P_MPI_CORE_CHECK_ZERO_CT : Z := 0x239bc.

Definition mpi_core_check_zero_ct_post (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (xs : list word) (n : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_check_zero_ct ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.$3.Lz,$3.(4.(5.$0.R11.(6.(7.O15.O14.O13.O12.R10.R?.R>.O11.O10.R=.R<.R;.R:.R9.R8.R7.R6.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.R5.R4.R3.R2.)O5.(8.O15.)O4.(9.(2.&40.))O1.(:.O16.)))(4.(;.(<.$=.)O1.O1.)(4.(>.O16.O1.O1.)(4.(?.O16.O1.)(4.(5.(2.&40.)R=.(10.&40.(11.R1.)))(4.(12.=R1.)(13.(5.$3.R1.=)(14.O3.O2.))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition mpi_core_check_zero_ct_stmt (segs : list Segment) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_check_zero_ct ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(15.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(16.(2.&8.))PA,$3.Pn,$3.Pxs,(17.(2.&40.))P,(18.O2.R4.R3.(19.R1.))P,(4.(12.=R3.)(12.R3.+2710.))P,(12.R4.(1:.(1;.(2.&40.)R3.)))P,(5.$3.(1<.R6.+4.)=)P,(1=.=R7.)P,(?.O2.R9.)P,(5.(2.&40.)R22.(10.&40.R9.))P,(5.(2.&40.)R22.(10.&40.R9.))(1>.O2.(1?.O2.R2=.R2<.R2;.R2:.R26.R25.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R>.R=.R9.R:.R<.)(6.(7.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.)R>.(10.&40.O1.)R=.(9.(2.&40.))R<.(:.O2.)))")
(* [comment removed for export] *).

Section Walk.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (A n : Z) (xs : list word).
  Hypothesis Hn : 0 <= n <= 10000.
  Hypothesis Ln : n <= Z.of_nat (length xs).
  Hypothesis XB : 0 < A /\ A + 4 * Z.of_nat (length xs) <= 2^64.
  Hypothesis HA : bytes_at psegs m A (u32s xs).
  Hypothesis MI : mem_inv psegs m.

  Notation POST := (mpi_core_check_zero_ct_post psegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc xs n m).

  (* [comment removed for export] *)
  #[using="MI"] Lemma tail_walk : ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_check_zero_ct ()) "Pv,$3.Px11,(2.&40.)Px12,(2.&40.)Px13,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)P,(4.(12.=R8.)(1=.R8.(20.+2.+20.)))P,(13.(5.$3.R9.=)(14.Vxs,Vn,))(1>.$21.(1?.$21.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vxs,Vn,Vm,)(6.(7.Vra,Vsp,Vgp,Vtp,Vt0,Vt1,Vt2,Vs0,Vs1,(10.&40.R:.)R9.R8.R7.R6.R5.R4.R3.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(10.&40.+239><.)Vfc,(9.(2.&40.))Vm,(:.$21.)))")
(* [comment removed for export] *).
  Proof.
    intros v x11 x12 x13 x14 x15 x16 x17 Hv Hz.
    pose proof (munch_refl ([] : list ivl) m) as MU. pose proof (wmono_refl psegs m) as WM.
    zstep. zstep. zstep. zstep. zstep. rewrite (ct_bool_tail v Hv).
    zstep. finish; [reflexivity | lia | exact Hz].
  Qed.

  (* [comment removed for export] *)
  #[using="Hn Ln XB HA MI"] Lemma loop_walk : ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_check_zero_ct ()) "Pk,$22.Pi,$3.Pacc,(2.&40.)Px13,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Ppa,(2.&40.)P,(5.$22.(23.(24.Vn,R8.))R9.)P,(4.(12.=R9.)(1=.R9.Vn,))P,(5.(2.&40.)R3.(10.&40.(25.VA,(26.+4.R:.))))P,(13.(5.$3.(1<.(27.&40.R:.)(20.+2.+20.))=)(14.Vxs,R;.))(1>.$21.(1?.$21.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vxs,Vn,Vm,)(6.(7.Vra,Vsp,Vgp,Vtp,Vt0,Vt1,Vt2,Vs0,Vs1,R5.(10.&40.(25.VA,(26.+4.Vn,)))R;.R:.R9.R8.R7.R6.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(10.&40.+239<<.)Vfc,(9.(2.&40.))Vm,(:.$21.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros i acc x13 x14 x15 x16 x17 pa Hk Hi -> Hacc; [lia|].
    destruct (nth_error xs (Z.to_nat i)) as [w|] eqn:NX; [| apply nth_error_None in NX; lia].
    pose proof (u32ro_read psegs m A xs i w _ HA NX ltac:(lia) eq_refl) as RDX.
    zstep. clear RDX. zstep. zstep.
    pose proof (limbs_zero_step xs i w acc ltac:(lia) NX Hacc) as Hacc'.
    pose proof (bv_unsigned_in_range 64 acc) as Ra. pose proof (bv_unsigned_in_range 64 (sx32 w)) as Rw. unfold bv_modulus in Ra, Rw.
    pose proof (lor_lt_pow2 (bv_unsigned (sx32 w)) (bv_unsigned acc) 64 ltac:(lia) ltac:(lia)) as RL.
    zstep. if_cases Kl; zify_cond Kl; rewrite ?unsigned_lit in Kl by lia.
    - eapply (IH (i + 1)); [lia | lia | f_equal; lia | rewrite unsigned_lit by lia; exact Hacc'].
    - zstep. zstep. zstep.
      eapply tail_walk. { apply Z.mod_pos_bound; lia. }
      replace n with (i + 1) by lia. exact Hacc'.
  Qed.
End Walk.

Lemma P_mpi_core_check_zero_ct_spec : mpi_core_check_zero_ct_stmt psegs P_MPI_CORE_CHECK_ZERO_CT.
Proof.
  unfold mpi_core_check_zero_ct_stmt, P_MPI_CORE_CHECK_ZERO_CT.
  intros until xs. intros HA Hn LX ALA NZA MI -> ->.
  pose proof (munch_refl ([] : list ivl) m) as MU. pose proof (wmono_refl psegs m) as WM.
  pose proof (u32ro_bound _ _ _ _ HA) as XB.
  zstep. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by lia.
  - (* [comment removed for export] *)
    zstep. eapply tail_walk with (n := n) (xs := xs); try eassumption; try lia.
    subst n. split; [intros _; apply limbs_zero_0 | reflexivity].
  - zstep. zstep. zstep.
    replace (A + Z.shiftl n 2) with (A + 4 * n) by (rewrite Z.shiftl_mul_pow2; lia).
    eapply loop_walk with (n := n) (xs := xs) (k := Z.to_nat n) (i := 0) (acc := Z_to_bv 64 0);
      try eassumption; try lia. { f_equal; lia. }
    rewrite unsigned_lit by lia. split; [intros _; apply limbs_zero_0 | reflexivity].
Qed.
