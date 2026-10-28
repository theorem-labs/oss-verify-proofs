(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Asn1Aux Asn1AuxA MpiCoreAux HeapIface ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import MpiJourney.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_platform_zeroize U_mpi_free U_mpi_addsub U_mpi_cmp U_mpi_core_mla U_mpi_add_abs_W.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_mpi_mul_int_W () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_val"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "Stdlib.ZArith.BinInt.Z.max"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.MBEDTLS_ERR_MPI_ALLOC_FAILED"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.binop_keep"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_sep"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.opnd_sep"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.mpd_writable"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LNull"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.const_at"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.iff"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.mpi_binop_post"; "mul_int_R"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_core_mla.MPI_CORE_MLA_STACK"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "Corelib.Lists.ListDef.skipn"; "Stdlib.ZArith.BinInt.Z.to_nat"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.lval"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32s"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "mpi_core_mla_vpost"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mkMPD"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "W.MI_FRAME"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.USpec.MpiJourney.XJ"; "W.MI_POST"; "RocqVerifyHarness.AgentSubmission.USpec.MpiJourney.BJ"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limbs_val"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_limbs"; "W.KC_stmt"; "RocqVerifyHarness.AgentSubmission.USpec.MpiJourney.JB"].


Definition U_MPI_MUL_INT : Z := 0x1fbc0.
Definition U_MPI_COPY : Z := 0x1f638.

(* [comment removed for export] *)
Notation MPI_MUL_INT_STACK := 160 (only parsing).

Definition mul_int_R (b : Z) (LB : list blk) (dX dA : mpd) (r : Z) (dX' : mpd) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_int_W ()) "(0.(1.(0.(2.$3.O2.=)(0.(2.$3.(4.O1.)(5.(4.O3.)O6.))(6.(7.O1.)(8.(7.O4.)(9.(7.O3.)+1.)))))(2.$3.O2.$:.))(;.O5.O4.O1.))")
(* [comment removed for export] *).

Definition mpi_mul_int_stmt (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (ENTRY MSF : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_int_W ()) "Pra,(<.&40.)Psp,(<.&40.)Pgp,(<.&40.)Ptp,(<.&40.)Pt0,(<.&40.)Pt1,(<.&40.)Pt2,(<.&40.)Ps0,(<.&40.)Ps1,(<.&40.)Pa0,(<.&40.)Pa1,(<.&40.)Pa2,(<.&40.)Pa3,(<.&40.)Pa4,(<.&40.)Pa5,(<.&40.)Pa6,(<.&40.)Pa7,(<.&40.)Ps2,(<.&40.)Ps3,(<.&40.)Ps4,(<.&40.)Ps5,(<.&40.)Ps6,(<.&40.)Ps7,(<.&40.)Ps8,(<.&40.)Ps9,(<.&40.)Ps10,(<.&40.)Ps11,(<.&40.)Pt3,(<.&40.)Pt4,(<.&40.)Pt5,(<.&40.)Pt6,(<.&40.)PF,(=.&5.(<.&40.))Pfc,(<.&20.)Pm,P,(<.&40.)(>.(<.&8.))Pmo,$?.Ph,(10.O5.O4.O3.)PLB,(11.$12.)PdX,$13.PdA,$13.Pb,$3.Plo,$3.P,(14.O5.O4.O3.R6.R5.R8.R7.)P,(15.O5.R9.R6.R5.)P,(15.O5.R:.R7.R5.)P,(16.R7.R6.)P,(17.(2.$18.(19.R8.)$1:.))P,(1;.R9.R8.R6.(1<.&40.R2=.))P,(1=.O4.R;.R7.(1>.R9.)+10.)P,P,(2.$18.(19.R:.)$1?.)(1=.O4.R=.R9.(20.R;.)(5.+4.(7.R;.)))P,(21.O4.R=.(1<.&40.R30.)(22.O5.O4.O3.R>.)R<.)P,P,(17.(2.$18.(19.R=.)$23.))(1.(6.(9.(20.R>.)(5.+4.(7.R>.)))R;.)(6.(1<.&40.R32.)(20.R>.)))P,(24.O5.R12.R;.(1<.&40.R32.))P,(6.R<.(25.(25.(1<.&40.R33.)+:0.)(26.O4.)))P,(6.(27.O4.)R=.)P,(6.(1<.&40.R35.)(22.O5.O4.O3.R13.))P,(2.$3.(28.(1<.&40.R36.)+10.)=)P,(6.(29.O4.)(27.O4.))P,(2.(<.&40.)R36.(2:.&40.(2;.O4.)))P,(2<.O5.R19.)P,(2=.O5.O4.R1:.)P,(2>.O4.O1.+8.)P,(0.(6.=R16.)(2?.R16.(30.+2.+20.)))P,(2.$3.(28.(1<.&40.R33.)(30.+2.+20.))R17.)P,(31.(2.$3.(1<.&40.R34.)=)(2.$3.R18.=))P,(2.(<.&40.)R37.(2:.&40.(1>.R1;.)))P,(2.(<.&40.)R37.(2:.&40.(1>.R1;.)))(32.O5.R20.(33.O5.O4.O3.R42.R41.R40.R3?.R3;.R3:.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R23.R22.R1?.R1>.R1=.(34.R1;.R1>.R1=.R1<.)R1:.R21.R20.)(35.(36.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.)R23.(2:.&40.O2.)R22.(37.(<.&40.))R21.(38.O5.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition mpi_core_mla_vpost (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D dl : Z) (ds : list word) (sl : Z) (ss : list word) (b : Z) (lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_int_W ()) "Lms',$39.(3:.(<.&40.)Lt0,(<.&40.)(3:.(<.&40.)Lt1,(<.&40.)(3:.(<.&40.)Lt2,(<.&40.)(3:.(<.&40.)La0,(<.&40.)(3:.(<.&40.)La1,(<.&40.)(3:.(<.&40.)La2,(<.&40.)(3:.(<.&40.)La3,(<.&40.)(3:.(<.&40.)La4,(<.&40.)(3:.(<.&40.)La5,(<.&40.)(3:.(<.&40.)La6,(<.&40.)(3:.(<.&40.)La7,(<.&40.)(3:.(<.&40.)Lt3,(<.&40.)(3:.(<.&40.)Lt4,(<.&40.)(3:.(<.&40.)Lt5,(<.&40.)(3:.(<.&40.)Lt6,(<.&40.)(3:.P,(<.&40.)(>.(<.&8.))Lm',P,(<.&40.)(>.(<.&8.))(3:.(11.(<.&40.))Lds',(11.(<.&40.))(3:.$3.Lc,$3.(0.(2.$39.R13.(35.(36.O1:.O19.O18.O17.R12.R11.R10.O16.O15.R?.R>.R=.R<.R;.R:.R9.R8.O14.O13.O12.O11.O10.O?.O>.O=.O<.O;.R7.R6.R5.R4.)O:.(3;.O1:.)O9.(37.(<.&40.))R3.(38.O1;.)))(0.(3<.(3=.(3>.$3.$3.)(3?.$3.$3.O8.(9.O8.(5.+4.O7.)))(3=.(3>.$3.$3.)(3?.$3.$3.(25.(1<.&40.O19.)$40.)(1<.&40.O19.))(41.(3>.$3.$3.))))O1.R3.)(0.(42.O1;.O1.R3.)(0.(2<.O1;.R3.)(0.(43.O1;.R3.O8.R2.)(0.(2.$44.(45.(<.&40.)R2.)(45.(<.&40.)O6.))(0.(2.(11.(<.&40.))(46.(<.&40.)(47.O7.)R2.)(46.(<.&40.)(47.O7.)O6.))(0.(0.(6.=R1.)(2?.R1.(30.+2.+20.)))(0.(2.$3.(9.(48.R2.O7.)(5.(30.+2.(5.+20.O7.))R1.))(9.(48.O6.O7.)(5.(48.O4.O5.)O3.)))(24.O1;.R3.O2.(1<.&40.O19.)))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition mpi_core_mla_vstmt (segs : list Segment) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_int_W ()) "Pra,(<.&40.)Psp,(<.&40.)Pgp,(<.&40.)Ptp,(<.&40.)Pt0,(<.&40.)Pt1,(<.&40.)Pt2,(<.&40.)Ps0,(<.&40.)Ps1,(<.&40.)Pa0,(<.&40.)Pa1,(<.&40.)Pa2,(<.&40.)Pa3,(<.&40.)Pa4,(<.&40.)Pa5,(<.&40.)Pa6,(<.&40.)Pa7,(<.&40.)Ps2,(<.&40.)Ps3,(<.&40.)Ps4,(<.&40.)Ps5,(<.&40.)Ps6,(<.&40.)Ps7,(<.&40.)Ps8,(<.&40.)Ps9,(<.&40.)Ps10,(<.&40.)Ps11,(<.&40.)Pt3,(<.&40.)Pt4,(<.&40.)Pt5,(<.&40.)Pt6,(<.&40.)PF,(=.&5.(<.&40.))Pfc,(<.&20.)Pm,P,(<.&40.)(>.(<.&8.))PD,$3.Pdl,$3.PS,$3.Psl,$3.Pb,$3.Plo,$3.Pds,(11.(<.&40.))Pss,(11.(<.&40.))P,(43.O2.R9.R8.R2.)P,(49.O2.R:.R7.(4:.R2.))P,(0.(6.=R9.)(6.R9.+2710.))P,(0.(6.=R8.)(6.R8.+2710.))P,(6.R;.(4;.(45.(<.&40.)R6.)))P,(6.R:.(4;.(45.(<.&40.)R6.)))P,(6.R;.R=.)P,(1.(0.(2.$3.R=.R?.)(2.(11.(<.&40.))R8.R9.))(1.(6.(9.R=.(5.+4.(4;.(45.(<.&40.)R8.))))R?.)(6.(9.R?.(5.+4.(4;.(45.(<.&40.)R9.))))R=.)))P,(2.$3.(28.R10.+4.)=)P,(2.$3.(28.R?.+4.)=)P,(2?.=R12.)P,(1.(2.$3.R10.=)(2?.=R11.))P,(2?.(9.R14.(5.+4.(4;.(45.(<.&40.)R>.))))(30.+2.+40.))P,(2?.(9.R13.(5.+4.(4;.(45.(<.&40.)R>.))))(30.+2.+40.))P,(24.O2.R17.R11.(1<.&40.R37.))P,(6.R12.(25.(1<.&40.R38.)$40.))P,(2.$3.(28.(1<.&40.R39.)+10.)=)P,(1.(6.(9.R19.(5.+4.(4;.(45.(<.&40.)R13.))))R14.)(6.(1<.&40.R3:.)R19.))P,(1.(6.(9.R18.(5.+4.(4;.(45.(<.&40.)R13.))))R15.)(6.(1<.&40.R3;.)R18.))P,(2<.O2.R1<.)P,(2.$3.(28.(1<.&40.R3>.)+2.)=)P,(2.$3.R19.(28.(1<.&40.R32.)(30.+2.+20.)))P,(2.(<.&40.)R37.(2:.&40.R1>.))P,(2.(<.&40.)R37.(2:.&40.R1>.))P,(2.(<.&40.)R37.(2:.&40.R1>.))P,(2.(<.&40.)R37.(2:.&40.R1>.))(4<.O2.(4=.O2.R44.R43.R42.R41.R3=.R3<.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R25.R24.R22.R21.R1<.R1?.R1;.R1>.R1=.R23.)(35.(36.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.)R25.(2:.&40.O1.)R24.(37.(<.&40.))R23.(38.O2.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition mi_frame (ra s0 s1 s2 s3 s4 s5 s6 : word) : list cell :=
  [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma lval_repeat0 : forall n k, lval (repeat (Z_to_bv 64 0) k) n = 0.
Proof.
  intros n k. unfold lval. generalize (Z.to_nat n) as i. clear n. intros i. revert k.
  induction i as [|i IH]; intros [|k]; cbn [firstn repeat limbs_val]; try reflexivity.
  rewrite IH. rewrite unsigned_lit by (clear; lia). reflexivity.
Qed.

Lemma firstn_repeat' : forall {T} (x : T) k j, firstn k (repeat x j) = repeat x (Nat.min k j).
Proof. intros T x k. induction k as [|k IH]; intros [|j]; cbn; try reflexivity. rewrite IH. reflexivity. Qed.

(* [comment removed for export] *)
Section W.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HFREE : hl_free L = U_FREE.
  Hypothesis HCALLOC : hl_calloc L = U_CALLOC.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m : mem) (mo : Model) (h : HST usegs L HI) (LB : list blk) (dA : mpd) (b lo : Z) (MSF : Z)
            (X sX nX pX : Z) (xs0 : list word) (padX : word) (ownX : limb_own).
  Local Notation dX := (mkMPD X sX nX pX xs0 padX ownX).
  Hypothesis MSFE : MSF = U_MEMSET_FUNC.
  Hypothesis CA : const_at L MSF 8.
  Hypothesis TP : tp = Z_to_bv 64 (hl_tp L).
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SLO2 : lo <= bv_unsigned sp - 160 - hl_stack L.
  Hypothesis BB : 0 <= b < 2^32.
  Variable wb : word.
  Hypothesis WB1 : bv_unsigned wb mod 2^32 = b.
  Hypothesis WB0 : bv_unsigned wb = 0 <-> b = 0.
  Definition MI_FRAME := mi_frame ra s0 s1 s2 s3 s4 s5 s6.
  Hypothesis JCX : JC usegs L HI h LB m mo dX sp lo 64 MI_FRAME.
  Definition MI_POST := ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_int_W ()) "(33.$4>.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,(4?.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(34.Vb,VLB,(4?.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,)Vlo,Vm,Vmo,)")
(* [comment removed for export] *).

  Local Ltac jc_open := pose proof JCX as [HLS SW DIMG HND ROIMG DHI HH MX NST XW XLS ACL FS0 SLO HTOP FSZ].
  Local Notation XJ0 := (XJ usegs L HI h LB m mo dX sp lo 64 MI_FRAME []).
  Local Notation XJ1 An cnt := (XJ usegs L HI h LB m mo dX sp lo 64 MI_FRAME [(An, 4 * cnt)]).
  Local Notation FB0 := (FB usegs L LB dX).
  Local Notation JBE dE := (JB usegs L LB m dX sp lo dE).
  Local Notation BJE dE := (BJ usegs sp dE).
  Local Ltac xj_open J := pose proof J as [MI1 ST1 FR1 HH1 HT1 MF1 SOK1 MX1 AD1 PD1 NS1 OUT1 FRS1 HPX1 XP1 NM1]; cbn [app] in HH1.

  (* [comment removed for export] *)
  #[using="L HI m mo h LB b lo X sX nX pX xs0 padX ownX wb WB0 JCX"] Lemma mi_epilogue :
    forall (t0 t1 t2 raj x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 t3 t4 t5 t6 : word) (m1 : mem),
      rw_cells usegs m1 (bv_unsigned sp - 64) MI_FRAME -> mem_inv usegs m1 ->
      evt usegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x18 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (ret_pc ra) fc None m1 (seg_rom usegs)
                               /\ munch ([] : list ivl) m1 m1 /\ wmono usegs m1 m1 /\ mem_inv usegs m1)
        (MS (mkR raj (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22
               s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1fd04) fc None m1 (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    jc_open. intros until m1. intros FR MI. pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    unfold MI_FRAME, mi_frame in FR.
    pose proof (munch_refl ([] : list ivl) m1) as MU. pose proof (wmono_refl usegs m1) as WM.
    do 11 zstep.
    replace (Z_to_bv 64 (bv_unsigned sp - 64 + 64)) with (Z_to_bv 64 (bv_unsigned sp)) by (f_equal; lia). rewrite Z_to_bv_bv_unsigned.
    finish.
  Qed.

  (* [comment removed for export] *)
  #[using="wb WB0 JCX"] Lemma mi_ret :
    forall (t0 t1 t2 raj x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 t3 t4 t5 t6 : word)
           (hc : HST usegs L HI) (LBc : list blk) (mc : mem) (moc : Model) (dXc : mpd) (r : Z),
      XJ0 hc LBc mc moc dXc ->
      (r = 0 /\ mpd_val dXc = mpd_val dA * b /\ md_n dXc <= Z.max nX (md_n dA + 1)) \/ r = MBEDTLS_ERR_MPI_ALLOC_FAILED ->
      aevtM usegs moc MI_POST
        (MS (mkR raj (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 r) x19 x20 x21 x22
               s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1fd04) fc None mc (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros until r. intros J HR. pose proof (xj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ J) as (_ & _ & _ & MK & _).
    eapply aevtM_cut_evt; [exact MK| eapply mi_epilogue; [exact (xj_fr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J)| exact (xj_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J)]|].
    cbv beta. intros ms' (-> & _). apply aevtM_done. unfold MI_POST. eapply xj_post; [exact JCX| exact J|].
    split; [exact HR|]. split; [exact (xj_addr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J)|]. split; [exact (xj_pad _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J)|].
    split; [exact (xj_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J)| exact (xj_nmono _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J)].
  Qed.

  Lemma mi_lor_align : forall a c, a mod 4 = 0 -> c mod 4 = 0 -> Z.land (Z.lor a c) 3 = 0.
  Proof.
    intros a c Ha Hc. rewrite Z.land_lor_distr_l, !land_3_mod', Ha, Hc. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition KC_stmt (n : Z) : Prop :=
    forall (t0 t1 t2 raj x9 a2 a3 a4 a5 a6 a7 x18 x19 x22 t3 t4 t5 t6 : word)
           (hc : HST usegs L HI) (LBc : list blk) (mc : mem) (moc : Model) (dXc : mpd),
      XJ0 hc LBc mc moc dXc -> (md_addr dA <> X -> BJE dA LBc mc dXc) -> md_own dXc = LHeap ->
      n + 1 <= md_n dXc -> md_n dXc <= Z.max nX (n + 1) -> md_sg dXc = sX ->
      limbs_val (md_limbs dXc) = limbs_val xs0 -> lval (md_limbs dXc) n = limbs_val xs0 ->
      aevtM usegs moc MI_POST
        (MS (mkR raj (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2 (Z_to_bv 64 n) x9 (Z_to_bv 64 X) (Z_to_bv 64 (md_addr dA))
               a2 a3 a4 a5 a6 a7 x18 x19 wb (Z_to_bv 64 X) x22 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1fcd8) fc None mc (seg_rom usegs))
(* [comment removed for export] *).

  #[using="HFREE HCALLOC MSF MSFE CA TP SPA BB WB0 JCX"] Lemma mi_G :
    forall (n : Z) (t0 t1 t2 raj x9 a2 a3 a4 a5 a6 a7 x19 x22 t3 t4 t5 t6 : word)
           (hc : HST usegs L HI) (LBc : list blk) (mc : mem) (moc : Model) (dXc : mpd),
      KC_stmt n -> XJ0 hc LBc mc moc dXc -> (md_addr dA <> X -> JBE dA /\ BJE dA LBc mc dXc) ->
      md_n dXc <= n < 625 * 16 -> 1 <= n -> md_sg dXc = sX -> md_limbs dXc = xs0 -> lval xs0 n = limbs_val xs0 ->
      aevtM usegs moc MI_POST
        (MS (mkR raj (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2 (Z_to_bv 64 n) x9 (Z_to_bv 64 X) (Z_to_bv 64 (md_addr dA))
               a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-16)) x19 wb (Z_to_bv 64 X) x22 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1fc74) fc None mc (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros until dXc. intros K1 J AJ CNT N1 SG1 LE HV. jc_open. unfold KC_stmt in K1.
    destruct dA as [Aa sA nA pA ys padA ownA]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in K1, AJ.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof alloc_ceiling_bounds as ACV.
    pose proof (xj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ J) as (HBR1 & HAP1 & ND1 & MK1 & XS & X0 & X16 & XAL & LEN1 & NR1 & OWN0 & OWN1). cbn [app] in HBR1, HAP1, ND1.
    xj_open J.
    destruct dXc as [X' sg nXc pXc xs pad' own]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. subst X' pad' sg xs.
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl usegs mc) as WM.
    zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    replace (Z_to_bv 64 0x3f960) with (Z_to_bv 64 (hl_calloc L)) by (rewrite HCALLOC; reflexivity).
    eapply aevtM_cut; [ eapply (heap_calloc usegs L HI) with (cnt := n + 1) (sz := 4) (lo := lo);
      rewrite ?(unsigned_lit (bv_unsigned sp - 64)) by (clear - SPB SLO HLS ACL ACP; lia); try eassumption; try reflexivity;
      clear - SLO HLS ACL ACP HTOP HT1 CNT NR1 SPB; try lia | ].
    intros ms' mo' PO. unfold call_post in PO. destruct_exs PO. destruct PO as [E PO]. injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp - 64)) in PO by (clear - SPB SLO HLS ACL ACP; lia).
    ddestruct PO as (MI2 & ST2 & MF2 & HPc & h2 & HT2 & RES2).
    replace (ret_pc (Z_to_bv 64 130184)) with (Z_to_bv 64 130184) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m2; rename mox into mo2 end.
    clear MU WM.
    destruct RES2 as [[-> HH2] | (An & -> & HBA & HH2 & HNEW)].
    { (* [comment removed for export] *)
      pose proof (xj_calloc_fail _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ J MI2 ST2 MF2 HPc HT2 HH2) as J2.
      pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
      pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl usegs m2) as WM.
      zstep. if_cases KZ; zify_cond KZ; [| exfalso; apply KZ; reflexivity].
      eapply mi_ret; [exact J2| right; reflexivity]. }
    (* [comment removed for export] *)
    replace ((n + 1) * 4) with (4 * (n + 1)) in * by (clear; lia).
    destruct (xj_calloc_ok _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ _ J MI2 ST2 MF2 HPc HT2 HH2 HBA HNEW ltac:(cbn [md_n]; clear - CNT; lia)) as [J2 F2].
    assert (AJ2 : Aa <> X -> JBE (mkMPD Aa sA nA pA ys padA ownA) /\ BJE (mkMPD Aa sA nA pA ys padA ownA) LBc m2 (mkMPD X sX nXc pXc xs0 padX own)).
    { intros NE. destruct (AJ NE) as [DBJ B]. split; [exact DBJ|]. eapply (bj_heap_pres _ _ _ _ _ _ _ _ _ _ _ _ JCX _ DBJ); [exact J| exact B| exact HPc| exact MI2]. }
    dpose HBA as (An0 & An16 & _ & AnC & AnI). pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
    clear HPc J AJ MI1 ST1 FR1 HH1 HT1 MF1 SOK1 MX1 NS1 OUT1 FRS1 HPX1 XP1 NM1.
    xj_open J2. pose proof MX1 as [(CX2 & _) _]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX2. unfold mpi_cells in CX2.
    pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    zstep. if_cases KZ; zify_cond KZ; [exfalso; clear - KZ An0 AnC ACV CNT NR1; lia|].
    zstep. zstep. zstep. zstep. if_cases KP; zify_cond KP.
    { (* [comment removed for export] *)
      assert (EO : own = LNull).
      { destruct own; [reflexivity| | exfalso; exact (NS1 eq_refl)]. exfalso. ddestruct (OWN1 ltac:(discriminate)) as (_ & N1' & _ & _ & _ & P0 & PC & _). rewrite Z.mod_small in KP by (clear - N1' P0 PC ACV; lia). clear - KP P0. lia. }
      subst own. pose proof (xg_null _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ J2 F2 eq_refl) as D2.
      destruct (OWN0 eq_refl) as [EP EN]. cbn [md_p md_n] in EP, EN. subst pXc nXc.
      clear MU WM. pose proof (munch_refl [(X, X + 16)] m2) as MU. pose proof (wmono_refl usegs m2) as WM.
      clear HH1 HH2 HNEW SOK1 ST2 FR1 HPX1 MI1.
      zstep. zstep.
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
      pose proof (xd_finish _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ D2 MU WM MI2 CX2) as J5. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J5.
      assert (B5 : Aa <> X -> BJE (mkMPD Aa sA nA pA ys padA ownA) ((An, 4 * (n + 1)) :: LBc) m5 (mkMPD X sX (n + 1) An (repeat (Z_to_bv 64 0) (Z.to_nat (n + 1))) padX LHeap)).
      { intros NE. destruct (AJ2 NE) as [DBJ B2].
        pose proof (bj_finish _ _ _ _ _ _ _ _ _ _ _ _ JCX _ DBJ _ _ _ _ _ _ _ _ _ D2 B2 MU WM) as B5. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in B5. exact B5. }
      zstep. eapply K1; [exact J5| exact B5| reflexivity| cbn [md_n]; clear; lia| cbn [md_n]; clear; lia| reflexivity| |].
      - cbn [md_limbs]. rewrite limbs_val_repeat0. destruct xs0; [reflexivity| exfalso; cbn [length] in *; lia].
      - cbn [md_limbs]. rewrite lval_repeat0. destruct xs0; [reflexivity| exfalso; cbn [length] in *; lia]. }
    (* [comment removed for export] *)
    assert (EO : own = LHeap).
    { destruct own; [| reflexivity| exfalso; exact (NS1 eq_refl)]. exfalso. destruct (OWN0 eq_refl) as [EP _]. cbn [md_p] in EP. apply KP. rewrite EP. reflexivity. }
    subst own. ddestruct (OWN1 ltac:(discriminate)) as (_ & N1' & XIN & XPAL & _ & P0 & PC & PI). cbn [md_p md_n] in N1', XIN, XPAL, P0, PC, PI.
    destruct (xg_memcpy_pre _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ J2 F2 eq_refl) as (SBY & SLEN & DST & DLEN & SEP & _ & _ & _ & _).
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in SBY, SLEN, DST, DLEN, SEP.
    clear HH1 HH2 HNEW SOK1 FR1 HPX1.
    zstep. zstep. zstep. if_cases KA; [zify_cond KA; exfalso; apply KA; apply mi_lor_align; clear - XPAL An16; Z.div_mod_to_equations; lia | clear KA].
    zstep. rewrite zx16_small by (clear - NR1; lia). zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep. zstep.
    pose proof U_memcpy_spec as SPc. unfold memcpy_stmt in SPc.
    assert (U1 : bv_unsigned (Z_to_bv 64 An) = An) by (apply unsigned_lit; clear - An0 AnC ACV CNT NR1; lia).
    assert (U2 : bv_unsigned (Z_to_bv 64 pXc) = pXc) by (apply unsigned_lit; clear - P0 PC ACV N1'; lia).
    assert (U3 : bv_unsigned (Z_to_bv 64 (nXc * 4)) = nXc * 4) by (apply unsigned_lit; clear - N1' CNT; lia).
    eapply aevtM_cut_evt; [ exact MK2 | eapply SPc with (src := u32s xs0); rewrite ?U1, ?U2, ?U3;
      [ exact SBY | rewrite SLEN; clear; lia | replace (Z.to_nat (nXc * 4)) with (4 * length (firstn (Z.to_nat nXc) (repeat (Z_to_bv 64 0) (Z.to_nat (n + 1)))))%nat by (rewrite DLEN; clear; lia); exact DST
      | clear - SEP; lia | exact MI2 ] | ].
    clear SPc. unfold memcpy_post. cbv beta. intros ms' PO.
    ddestruct PO as (z0 & z1 & z2 & za1 & za2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & m3 & E & MUd & WMd & MI3 & PA3 & _). subst ms'.
    rewrite ?U1, ?U2, ?U3 in MUd. rewrite ?U1, ?U2, ?U3 in PA3.
    replace (ret_pc (Z_to_bv 64 130232)) with (Z_to_bv 64 130232) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    replace (An + nXc * 4) with (An + 4 * nXc) in MUd by (clear; lia). replace (Z.to_nat (nXc * 4)) with (Z.to_nat (4 * nXc)) in PA3 by (clear; lia).
    destruct (xg_memcpy_post _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ J2 F2 eq_refl MUd WMd MI3 PA3) as [J3 F3]. cbn [md_limbs md_n] in F3.
    assert (AJ3 : Aa <> X -> JBE (mkMPD Aa sA nA pA ys padA ownA) /\ BJE (mkMPD Aa sA nA pA ys padA ownA) LBc m3 (mkMPD X sX nXc pXc xs0 padX LHeap)).
    { intros NE. destruct (AJ2 NE) as [DBJ B2]. split; [exact DBJ|].
      pose proof (bj_fb_apart _ _ _ _ _ _ _ _ _ _ _ _ JCX _ DBJ _ _ _ _ _ _ _ _ J2 F2 B2) as [ESA ELA]. cbn [md_addr md_own md_p md_n] in ESA, ELA.
      exact (bj_munch _ _ _ _ _ _ _ _ _ _ _ _ JCX _ DBJ _ _ _ _ _ B2 MUd WMd ltac:(cbn; clear - ESA CNT; lia) ltac:(intros BN; cbn; pose proof (ELA BN); clear - H CNT; lia)). }
    clear J2 F2 AJ2 MU WM DST SBY CX2 ST2 MI2 MK2 MI1 ST1 HT1 MF1 MX1 NS1 OUT1 FRS1 XP1 AD1 PD1 NM1.
    pose proof (munch_refl ([] : list ivl) m3) as MU. pose proof (wmono_refl usegs m3) as WM.
    xj_open J3. pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK3.
    destruct (xg_zfree_pre _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ J3 F3 eq_refl) as (ZIN & ZCH & ZLEN & ZB). cbn [md_p md_n md_limbs] in ZIN, ZCH, ZLEN, ZB.
    (* [comment removed for export] *)
    pose proof MX1 as [(CX3 & _) _]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX3. unfold mpi_cells in CX3.
    zstep. rewrite zx16_small by (clear - NR1; lia). zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep.
    eapply aevtM_cut.
    { eapply (U_zeroize_and_free_spec L HI HFREE HLS SW DIMG) with (buf := pXc) (len := 4 * nXc) (lo := lo) (junk := u32s xs0);
        rewrite ?(unsigned_lit (bv_unsigned sp - 64)) by (clear - SPB SLO HLS ACL ACP; lia); try eassumption; try reflexivity.
      all: try (right; split; [exact ZIN|]; rewrite <- ZLEN; exact ZCH).
      all: try exact ZB.
      all: try (rewrite HT1; clear - HTOP; lia).
      all: try (rewrite <- MSFE; exact CA).
      all: try (f_equal; clear; lia).
      all: clear - SLO SPA SPB HLS ACL ACP; lia. }
    cbv beta. intros ms' mo' PO. unfold zeroize_and_free_post in PO.
    ddestruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m4 & mo4 & h4 & E & PO). injection E as -> ->.
    rewrite ?(unsigned_lit (bv_unsigned sp - 64)) in PO by (clear - SPB SLO HLS ACL ACP; lia).
    ddestruct PO as (MI4 & ST4 & MF4 & HT4 & HH4 & PX4 & SOK4).
    replace (ret_pc (Z_to_bv 64 130248)) with (Z_to_bv 64 130248) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    pose proof (xg_zfree_post _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ _ _ J3 F3 eq_refl MI4 ST4 MF4 HT4 HH4 PX4 SOK4) as D4.
    assert (AJ4 : Aa <> X -> JBE (mkMPD Aa sA nA pA ys padA ownA) /\ BJE (mkMPD Aa sA nA pA ys padA ownA) (lb_remove pXc LBc) m4 (mkMPD X sX nXc pXc xs0 padX LHeap)).
    { intros NE. destruct (AJ3 NE) as [DBJ B3]. split; [exact DBJ|].
      pose proof (bj_zfree _ _ _ _ _ _ _ _ _ _ _ _ JCX _ DBJ _ _ _ _ _ _ _ _ _ J3 F3 B3 eq_refl PX4 MI4) as B4. cbn [md_p] in B4. exact B4. }
    pose proof (heap_mok _ _ HI _ _ _ _ HH4) as MK4.
    clear J3 F3 AJ3 MI1 ST1 FR1 HH1 HT1 MF1 SOK1 MX1 NS1 OUT1 FRS1 HPX1 XP1 AD1 PD1 NM1 MU WM MK3 HH4 PX4 ZCH PA3 MUd WMd MI3 SOK4.
    pose proof (xd_struct _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D4) as CX4. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX4. unfold mpi_cells in CX4.
    pose proof (munch_refl [(X, X + 16)] m4) as MU. pose proof (wmono_refl usegs m4) as WM.
    zstep. zstep. zstep.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    pose proof (xd_finish _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ D4 MU WM MI4 CX4) as J5. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J5.
    assert (B5 : Aa <> X -> BJE (mkMPD Aa sA nA pA ys padA ownA) ((An, 4 * (n + 1)) :: lb_remove pXc LBc) m5
                   (mkMPD X sX (n + 1) An (xs0 ++ skipn (Z.to_nat nXc) (repeat (Z_to_bv 64 0) (Z.to_nat (n + 1)))) padX LHeap)).
    { intros NE. destruct (AJ4 NE) as [DBJ B4].
      pose proof (bj_finish _ _ _ _ _ _ _ _ _ _ _ _ JCX _ DBJ _ _ _ _ _ _ _ _ _ D4 B4 MU WM) as B5. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in B5. exact B5. }
    zstep. eapply K1; [exact J5| exact B5| reflexivity| cbn [md_n]; clear; lia| cbn [md_n]; clear; lia| reflexivity| |].
    - cbn [md_limbs]. rewrite skipn_repeat, limbs_val_app_zeros. reflexivity.
    - cbn [md_limbs]. rewrite skipn_repeat. unfold lval. rewrite firstn_app, firstn_repeat', firstn_all2 by (clear - LEN1 CNT; lia).
      apply limbs_val_app_zeros.
  Qed.
End W.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_mpi_lset U_mpi_grow.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import MpiWalkAux LiaOrc.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr LxDec LxMem LxStep LxRun LxDenot LxSoundRun LxSum LxSoundSum LxTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac LxP_Flat LxP_Flat2.
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia.
Local Ltac clear_disj ::= fc_clear_disj.

Definition mpi_lset_stmt_v (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (ENTRY MSF : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (h : HST segs L HI) (LB : list blk) (dX : mpd) (z lo : Z),
    HEAP segs L HI h LB m mo -> mpd_at segs m LB dX -> md_own dX <> LStatic ->
    mpd_writable L LB (bv_unsigned sp) (heap_top segs L HI h) dX -> -(2^31) <= z < 2^31 ->
    stk segs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 48 - hl_stack L -> @alloc_ceiling L <= lo ->
    bv_unsigned sp <= heap_top segs L HI h -> bv_unsigned sp mod 16 = 0 -> hl_data_hi L <= @alloc_ceiling L ->
    tp = Z_to_bv 64 (hl_tp L) -> mem_inv segs m -> statics_ok segs L m -> const_at L MSF 8 ->
    a0 = Z_to_bv 64 (md_addr dX) -> a1 = Z_to_bv 64 z ->
    aevtM segs mo
      (mpi_binop_post segs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB dX
         (fun r dX' => lset_R z dX LB r dX' /\ (r = 0 -> mpd_val dX' = z)) lo m mo)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom segs)).

Definition lset_vR (z : Z) (dX : mpd) (LB : list blk) (r : Z) (dX' : mpd) : Prop :=
  lset_R z dX LB r dX' /\ (r = 0 -> mpd_val dX' = z).

Lemma lset_swrap_high : forall u, 2^64 - 2^31 <= u < 2^64 -> bv_swrap 32 u = u - 2^64.
Proof.
  intros u Hu. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  replace (u + 2^31) with ((u - 2^64 + 2^31) + 2^32 * 2^32) by lia.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma lset_abs32 : forall z, -(2^31) <= z < 2^31 ->
  (if z <? 0 then -1 else 1) *
  (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (Z.lxor (z mod 2^64) (bv_swrap 32 (Z.shiftr (bv_swrap 32 (z mod 2^64)) 31) mod 2^64)
                                        - bv_swrap 32 (Z.shiftr (bv_swrap 32 (z mod 2^64)) 31) mod 2^64))) mod 2^32 + 2^32 * 0) = z.
Proof.
  intros z Hz. change (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (Z.lxor (z mod 2^64) (bv_swrap 32 (Z.shiftr (bv_swrap 32 (z mod 2^64)) 31) mod 2^64)
    - bv_swrap 32 (Z.shiftr (bv_swrap 32 (z mod 2^64)) 31) mod 2^64))) mod 2^32)
    with (w32 (Z_to_bv 64 (bv_swrap 32 (Z.lxor (z mod 2^64) (bv_swrap 32 (Z.shiftr (bv_swrap 32 (z mod 2^64)) 31) mod 2^64)
    - bv_swrap 32 (Z.shiftr (bv_swrap 32 (z mod 2^64)) 31) mod 2^64)))).
  rewrite Z_to_bv64_swrap32_mod32. rewrite Z.shiftr_div_pow2 by lia.
  destruct (Z.ltb_spec z 0) as [Hn|Hp].
  - assert (E1 : z mod 2^64 = z + 2^64) by (Z.div_mod_to_equations; lia). rewrite E1.
    rewrite (lset_swrap_high (z + 2^64)) by lia. replace (z + 2^64 - 2^64) with z by lia.
    assert (E2 : z / 2^31 = -1) by (Z.div_mod_to_equations; lia). rewrite E2.
    rewrite (swrap32_signed_small (-1)) by lia.
    assert (E3 : (-1) mod 2^64 = 2^64 - 1) by reflexivity. rewrite E3.
    assert (E4 : Z.lxor (z + 2^64) (2^64 - 1) = 2^64 - 1 - (z + 2^64)).
    { change (2^64 - 1) with 18446744073709551615. apply zb_lxor_ones. lia. }
    rewrite E4.
    assert (E5 : (2^64 - 1 - (z + 2^64) - (2^64 - 1)) mod 2^32 = - z) by (Z.div_mod_to_equations; lia). rewrite E5. lia.
  - rewrite (Z.mod_small z) by lia. rewrite (swrap32_of_small z) by lia. rewrite (Z.div_small z) by lia.
    change (bv_swrap 32 0 mod 2^64) with 0. rewrite Z.lxor_0_r, Z.sub_0_r, Z.mod_small by lia. lia.
Qed.


Ltac2 gd_tbl_lset_v () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.mpd_writable"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.const_at"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.mpi_binop_post"; "lset_R"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_waddr"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_ivs"; "Corelib.Lists.ListDef.Forall"; "Corelib.Init.Datatypes.prod"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.block_range"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_written"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C2"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_pad"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.max"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_addr"; "Corelib.Init.Logic.False"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.le4"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "Corelib.Lists.ListDef.repeat"; "Stdlib.ZArith.BinInt.Z.to_nat"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_out"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mkMPD"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_blk"; "lset_vR"].

Section LSV.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HCALLOC : hl_calloc L = U_CALLOC.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP usegs L HI h LB m mo -> List.NoDup (map fst LB).

  Local Ltac flia := first [clear_disj; lia | lia].
  Local Ltac fix_regs :=
    repeat match goal with |- context [Z_to_bv 64 (Zpos ?p)] =>
      let z := constr:(Zpos p) in
      lazymatch eval compute in (Z.leb (2^63) z) with
      | true => let z' := eval compute in (z - 2^64)%Z in replace (Z_to_bv 64 z : word) with (Z_to_bv 64 z' : word) by (apply zbv_mod64; reflexivity)
      end end.
  Local Ltac land3_zero p :=
    let E := fresh "E" in
    assert (E : Z.land p 3 = 0) by (change (Z.land p 3) with (Z.land p (Z.ones 2)); rewrite Z.land_ones by lia; change (2 ^ 2) with 4; lia);
    rewrite ?E; clear E.

  Lemma L_TAIL_v : ltac2:(CDefT.buildp (gd_tbl_lset_v ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))Pmo,$3.Ph,(4.$2;.VL,VHI,)PLB,(5.$6.)PdX,$7.Pz,$8.Plo,$8.Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Px18,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pm2,P,(0.&40.)(2.(0.&8.))Pmo2,$3.Ph2,(4.$2;.VL,VHI,)PLB',(5.$6.)PP',$8.Pn',$8.Psg,(0.&40.)P,(9.$2;.VL,VHI,R5.R4.R7.R6.)P,(<.$8.(12.$2;.VL,VHI,R6.)(12.$2;.VL,VHI,R1<.))P,(3<.R1>.R8.)P,(21.$2;.VL,R:.)P,(33.$2;.VL,R1>.(11.&40.R32.)(34.R1=.)R21.R;.)P,Pa,$8.P,(13.(14.(23.R1?.)R1.)(17.R1.(2=.(23.R1?.)+10.)))(2>.VL,R;.(11.&40.R35.)(12.$2;.VL,VHI,R22.)R2.)P,Pa,$8.P,(13.(14.(23.R20.)R1.)(17.R1.(2=.(23.R20.)+10.)))P,(13.(14.(3:.VL,)R2.)(17.R2.(1=.VL,)))(3;.VL,R3.)P,(14.(11.&40.R35.)(12.$2;.VL,VHI,R22.))P,(14.(1;.VL,)R1?.)P,(14.R20.(19.(11.&40.R37.)+20.))P,(17.(11.&40.R38.)(16.+2.+40.))P,(35.(36.$8.$8.)Lb,(36.$8.$8.)(37.VL,(38.$8.$8.R1.)(39.$8.$8.R1.))R25.)P,(14.(1=.VL,)(1;.VL,))P,(13.(14.(15.(16.+2.+1?.))R25.)(17.R25.(16.+2.+1?.)))P,(20.$2;.R15.)P,(18.$2;.R16.R26.(2=.(11.&40.R3=.)-20.))P,(3=.$2;.R17.(2=.(11.&40.R3>.)-20.)(3>.$3?.(40.R39.)(3>.$3?.(40.R3:.)(3>.$3?.(40.R3;.)(3>.$3?.(40.R3?.)(41.$3?.))))))P,(3=.$2;.R18.(23.R2:.)(3>.$3?.(40.(1>.&40.R14.))(3>.$3?.(42.R12.)(3>.$3?.(42.(1>.&40.R13.))(3>.$3?.(43.(44.R2:.))(41.$3?.))))))P,(<.$8.(1<.(23.R2;.)+8.)=)P,(17.=(23.R2<.))P,(14.(2=.(23.R2=.)+10.)(16.+2.+40.))P,(3=.$2;.R1<.R18.(3>.$3?.(43.(1>.&40.=))(41.$3?.)))P,(<.$8.(1<.R19.+10.)=)P,(45.(36.$8.$8.)(46.$8.$8.R1:.(47.+4.R19.))R1;.)P,(13.(14.+1.R1:.)(14.R1:.+2710.))P,(<.$8.R1;.(48.(49.R32.)+1.))P,(17.=R1=.)P,(14.(2=.R1>.(47.+4.R1=.))(1;.VL,))P,(32.(14.(2=.R1?.(47.+4.R1>.))(3:.VL,))(14.(1=.VL,)R1?.))P,(32.(14.(2=.(23.R36.)+10.)R20.)(14.(2=.R20.(47.+4.R1?.))(23.R36.)))P,(32.(14.(2=.(23.R37.)+10.)R35.)(14.(11.&40.R4<.)(23.R37.)))P,Pa,$8.P,(13.(14.R23.R1.)(17.R1.(2=.R23.+4.)))P,(4:.VL,R3;.(11.&40.R4?.)R2.)P,(31.(34.R3;.)R3.)$4;.P,Pm5,P,(0.&40.)(2.(0.&8.))Pw,(0.&40.)P,(3=.$2;.R2.R25.(3>.$3?.(4<.#4.(4=.R1.))(41.$3?.)))P,(2?.(3>.(36.$8.$8.)(46.$8.$8.(23.R3<.)(2=.(23.R3<.)+10.))(3>.(36.$8.$8.)(46.$8.$8.R26.(2=.R26.+4.))(41.(36.$8.$8.))))R2:.R3.)P,(30.$2;.R2;.R4.)(4>.$2;.R5.R28.(3>.(0.&40.)R4.(4?.(0.&40.)(1>.&40.=)(50.(19.R27.+1.)))))P,Psg',$8.Plimbs',(5.(0.&40.))(51.R3=.R3<.R27.(52.(23.R3<.)R2.R25.R26.R1.(44.R3<.)$53.))P,(32.(45.(36.$8.$8.)(46.$8.$8.R25.(47.+4.R24.))(54.R3;.))(;.(45.(36.$8.$8.)(46.$8.$8.R25.(47.+4.R24.))R3<.)))(24.$2;.R29.(25.$2;.VL,VHI,R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R3>.R3=.R3<.(55.R3;.R3<.R3=.)R3:.R40.R3?.)(27.(28.(1>.&40.+1?8:4.)(1>.&40.(2=.(11.&40.R51.)-20.))R50.R4?.R39.R38.R37.(1>.&40.(23.R3<.))(1>.&40.R3;.)(1>.&40.R26.)R36.R35.R34.R33.R32.R31.R30.R2?.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R2>.R2=.R2<.R2;.)R42.(1>.&40.+1?8:4.)R41.(29.(0.&40.))R2:.(2:.$2;.)))").
  Proof.
    intros until sg. destruct dX as [X sg0 n P limbs pad own]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
    intros HH2 HT2 MF2 SOK2 HPX2 XCW XD HTOP ACL SLO SPB HBR DHI ZB MI2 ST2 FR CH XAL X0 X16 PZ0 PAL' PIN' NL NMAX P0' P4' PD XP' XS PFR LIMBS MO AFR.
    pose proof alloc_ceiling_pos as ACP. pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
    pose proof (conj HH2 I) as HH2c. pose proof (conj SOK2 I) as SOK2c. clear HH2 SOK2.
    pose proof (munch_refl [(X, X + 16); (P', P' + 4)] m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    pose proof (@alloc_ceiling_bounds L) as ACB.
    assert (NZP : bv_eqb (Z_to_bv 64 P') (Z_to_bv 64 0) = false) by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
    zstep. zstep. rewrite NZP; cbv_concl_iota. zstep. land3_zero P'.
    zstep. if_false. clear ACB NZP.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. zstep. zstep. zstep. zstep.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => match goal with H : stk usegs mx _ _ |- _ => release_frame FR H (bv_unsigned sp) end end.
    zstep.
    flat constr:(HH2c) 2%nat. flclear HH2c. intros HH2 _. flat constr:(SOK2c) 2%nat. flclear SOK2c. intros SOK2 _.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    match goal with H : rw_cells usegs m5 X _ |- _ => rename H into CH5 end.
    match goal with H : rw_cells usegs m5 P' _ |- _ => rename H into PZ5 end.
    apply (rw_cells_C2_congr usegs m5 X [C8 (Z_to_bv 64 P')] _ (if z <? 0 then -1 else 1)) in CH5; [| apply to_sign_mod16; lia].
    lazymatch type of PZ5 with rw_cells _ _ _ [C4 ?w] => set (w0 := w) in PZ5 end.
    assert (PZ5' : rw_cells usegs m5 P' [CB 4 (le4 w0)]).
    { eapply rw_cells_reshape; [exact PZ5| cbn -[le4]; split; [apply length_le4| exact I] | cbn -[le4]; reflexivity]. }
    apply aevtM_done. unfold mpi_binop_post. flexi 16%nat. exists h2.
    exists LB', (mkMPD X (if z <? 0 then -1 else 1) n' P' (w0 :: repeat (Z_to_bv 64 0) (Z.to_nat (n' - 1))) pad LHeap), 0.
    split; [reflexivity|]. split; [assumption|]. split; [assumption|]. split; [exact MF2|]. split; [exact HT2|].
    split. { eapply (Asn1AuxA.HEAP_munch usegs L HI) with (SP := lo); [exact HH2| exact ACL| exact MU| exact WM|].
      intros a Ha NO. cbn in NO. rewrite HT2.
      destruct (Z.le_gt_cases X a); [destruct (Z.lt_ge_cases a (X + 16)); [destruct (XCW a ltac:(lia)) as [C|[C|C]]; [left; lia| right; left; exact C| right; right; exact C] |]|].
      all: right; right; exists (P', 4 * n'); split; [exact PIN'| cbn; lia]. }
    split. { split; [| cbn; destruct (z <? 0); [right| left]; reflexivity]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
      split; [exact CH5|]. split; [exact XAL|]. split; [exact X0|]. split; [cbn [length]; rewrite repeat_length; lia|]. split; [unfold MPI_MAX_LIMBS; lia|].
      split; [lia|]. split; [exact PIN'|]. split; [exact PAL'|]. exact (LIMBS m5 w0 PZ5' MU WM). }
    split; [exact (MO _ _)|].
    split. { eapply heap_presx_trans; [exact HPX2|]. eapply heap_presx_of_munch; [exact MU| exact WM|]. intros a Ha Hc Ho.
      destruct (outside_dec [(X, X + 16); (P', P' + 4)] a) as [O|NO]; [exact O| exfalso]. cbn in NO.
      destruct (Z.le_gt_cases P' a); [destruct (Z.lt_ge_cases a (P' + 4)); [exact (PFR a ltac:(lia) Hc Ho)|]|]; cbn in Ho; (flat constr:(Ho) 2%nat; flclear Ho; intros O1 _); lia. }
    split. { eapply statics_ok_munch; [exact SOK2| exact MU|]. intros a Ha NW.
      destruct (outside_dec [(X, X + 16); (P', P' + 4)] a) as [O|NO]; [exact O| exfalso]. cbn in NO.
      destruct (Z.le_gt_cases X a); [destruct (Z.lt_ge_cases a (X + 16)); [exact (NW (XD a ltac:(lia) Ha))|]|]; lia. }
    unfold lset_vR. split.
    { unfold lset_R. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own mpd_blk].
      split; [left; split; [reflexivity|]; split; [lia|]; split; [reflexivity|]; split; [eexists; reflexivity| split; reflexivity]|].
      split; [reflexivity|]. intros b [<-|[]]. exact AFR. }
    intros _. unfold mpd_val. cbn [md_sg md_limbs limbs_val]. rewrite limbs_val_repeat0.
    unfold w0. exact (lset_abs32 z ZB).
  Qed.

  Lemma U_mpi_lset_spec_v : mpi_lset_stmt_v usegs L HI U_MPI_LSET U_MEMSET_FUNC.
  Proof.
    unfold mpi_lset_stmt_v, U_MPI_LSET. intros until lo. intros HH MA NST XW ZB ST SLO ACL HTOP SPA DHI TP MI SOK CA -> ->. change (fun r dX' => lset_R z dX LB r dX' /\ (r = 0 -> mpd_val dX' = z)) with (lset_vR z dX LB).
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof alloc_ceiling_pos as ACP.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros HBR HAP. pose proof (HND _ _ _ _ HH) as ND.
    destruct dX as [X sg n P limbs pad own].
    flat constr:(MA) 2%nat. flclear MA. intros FLt1 SG. flat constr:(FLt1) 6%nat. flclear FLt1. intros CH XAL X0 LEN NR OWN. unfold mpi_cells in CH.
    flat constr:(XW) 3%nat. flclear XW. intros XCW XD XP. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    unfold MPI_MAX_LIMBS in NR. pose proof (rw_cells_bound _ _ _ _ CH) as XB. cbn [cells_size csize Nat.add] in XB.
    pose proof (client_wrange_where L _ _ _ X 16 lo XCW ltac:(lia) HBR DHI ACL ltac:(lia)) as XS.
    assert (OWF : (own = LNull /\ P = 0 /\ n = 0 /\ limbs = []) \/ (own = LHeap /\ 1 <= n /\ In (P, 4 * n) LB /\ P mod 16 = 0 /\ u32arr usegs m P limbs /\ 0 < P /\ P + 4 * n <= alloc_ceiling)).
    { destruct own as [| |]; [left| right| exfalso; exact (NST eq_refl)].
      - flat constr:(OWN) 2%nat. flclear OWN. intros P0 N0. split; [reflexivity|]. split; [exact P0|]. split; [exact N0|]. destruct limbs; [reflexivity| cbn in LEN; lia].
      - flat constr:(OWN) 4%nat. flclear OWN. intros N1 PIN PAL PCH. flat constr:((proj1 (Forall_forall _ _) HBR _ PIN)) 5%nat. intros P0 _ _ P4 P5. cbn in P0, P4, P5.
        split; [reflexivity|]. split; [exact N1|]. split; [exact PIN|]. split; [exact PAL|]. split; [exact PCH|]. split; [exact P0| exact P4]. }
    clear OWN.
    assert (PRNG : 0 <= P /\ P + 4 * n <= alloc_ceiling) by (destruct OWF as [(_ & -> & -> & _)|(_ & _ & _ & _ & _ & P0 & P4)]; lia).
    carve_frame 32%nat ST.
    assert (HPX0 : heap_presx usegs L LB (bv_unsigned sp) (mpd_ivs (mkMPD X sg n P limbs pad own)) m m) by apply heap_presx_refl.
    assert (LXSUMS : forall AL, Forall (summary_okG usegs AL []) (@nil summary)) by (intros AL; constructor).
    rewrite TP. apply (lxp_aevtM_of_evt usegs mo _ _ MK).
    lx_run_tac (PLANS [0x46e44; 0x3f960] [] 40%N (@nil summary)); lx_tree.
    all: apply evt_done; cbv beta; rewrite <- TP; fix_regs.
    all: lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) =>
         lazymatch goal with Hm : munch ?W ?mA mx, Hw : wmono _ ?mA' mx |- _ => rename Hm into MU1; rename Hw into WM1; rename mx into m1 end end.
    2: {
      destruct OWF as [(_ & _ & -> & _)|(-> & N1 & PIN & PAL & PCH & P0 & P4)]; [exfalso; flia|]. specialize (XP eq_refl).
      flat constr:((proj1 (Forall_forall _ _) HBR _ PIN)) 5%nat. intros _ _ _ _ P5. cbn in P5.
      lazymatch goal with Hc : rw_cells _ m1 X _, Hf : rw_cells _ m1 (bv_unsigned sp + -32) _, Hs : stk _ m1 _ _, Hi : mem_inv _ m1 |- _ =>
        rename Hc into CH1; rename Hf into FR1; rename Hs into ST1; rename Hi into MI1 end.
      pose proof (run_heap L HI sp h h LB m m1 mo _ X lo HH eq_refl HTOP ACL ltac:(flia) XCW MU1 WM1 ltac:(intros a NO; cbn in NO |- *; flia)) as HH1.
      pose proof (run_statics L sp m m1 _ X lo SOK DHI ACL ltac:(flia) XD MU1 ltac:(intros a NO; cbn in NO |- *; flia)) as SOK1.
      pose proof (run_presx L DIMG sp LB _ m m m1 _ lo HPX0 HBR DHI ACL ltac:(flia) MU1 WM1 ltac:(intros a NO; cbn in NO |- *; flia)) as HPX1.
      pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK1.
      lazymatch type of MU1 with munch ?W _ _ => apply (u32arr_transport usegs W m m1) in PCH; [| exact MU1| exact WM1| cbn; flia] end.
      clear ST MI CH FR MK MU1 WM1 HPX0 HH SOK.
      pose proof (munch_refl [(P, P + 4 * n)] m1) as MU. pose proof (wmono_refl usegs m1) as WM.
      apply u32arr_cells in PCH.
      pose proof U_memset_spec as SPs. unfold memset_stmt in SPs.
      eapply aevtM_cut_evt; [ exact MK1 | eapply SPs; rewrite ?unsigned_lit by lia; [ replace (Z.to_nat (4 * n)) with (4 * length limbs)%nat by lia; exact PCH | assumption ] | ].
      clear SPs PCH. unfold memset_post. rewrite !unsigned_lit by lia. post_call usegs m1.
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
      match goal with H : rw_cells usegs m2 P _ |- _ => rename H into PZ end.
      assert (HH2 : HEAP usegs L HI h LB m2 mo).
      { eapply (Asn1AuxA.HEAP_munch usegs L HI) with (SP := lo); [exact HH1| exact ACL| exact MU| exact WM|].
        intros a Ha NO. cbn in NO. right; right. exists (P, 4 * n). split; [exact PIN| cbn; lia]. }
      assert (HPX2 : heap_presx usegs L LB (bv_unsigned sp) (mpd_ivs (mkMPD X sg n P limbs pad LHeap)) m m2).
      { eapply heap_presx_trans; [exact HPX1|]. eapply heap_presx_of_munch; [exact MU| exact WM|].
        intros a Ha Hc Ho. cbn in Ho |- *. flat constr:(Ho) 3%nat. flclear Ho. intros O1 O2 _. split; [exact O2| exact I]. }
      clear HH1 HPX1 MU WM.
      assert (PZ' : rw_cells usegs m2 P ([C4 (Z_to_bv 64 0)] ++ [CB (Z.to_nat (4 * n - 4)) (repeat (Z_to_bv 8 0) (Z.to_nat (4 * n - 4)))])).
      { eapply rw_cells_reshape; [exact PZ| |].
        - cbn. rewrite repeat_length. (flsplit; repeat split); reflexivity.
        - cbn [cells_bytes cbytes app]. rewrite !app_nil_r. change (le4 (Z_to_bv 64 0)) with (repeat (Z_to_bv 8 0) 4).
          rewrite <- repeat_app. f_equal. lia. }
      apply rw_cells_app in PZ'. flat constr:(PZ') 2%nat. flclear PZ'. intros PZ0 PZR. cbn [cells_size csize Nat.add] in PZR. clear PZ.
      replace (P + Z.of_nat 4) with (P + 4) in PZR by lia.
      try lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) =>
        replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
      lazymatch goal with Hc : rw_cells _ m2 X _, Hf : rw_cells _ m2 (bv_unsigned sp + -32) _ |- _ =>
      eapply L_TAIL_v; [exact HH2| reflexivity| apply mo_frame_refl| assumption| exact HPX2| exact XCW| exact XD| exact HTOP| exact ACL| flia| flia| exact HBR| exact DHI
        | exact ZB| assumption| assumption| exact Hf| exact Hc| exact XAL| exact X0| cbn [md_addr]; flia| exact PZ0
        | exact PAL| exact PIN| cbn [md_n]; flia| cbn [md_n]; lia| exact P0| exact P4| destruct DIMG; lia| cbn [md_addr]; exact XP| exact XS
        | intros a Ha Hc' Ho; cbn in Ho; (flat constr:(Ho) 3%nat; flclear Ho; intros _ O2 _); lia
        | intros m5 w PZ5 MU5 WM5; cbn [md_addr] in MU5;
          apply (rw_cells_transport usegs [(X, X + 16); (P, P + 4)] m2 m5) in PZR; [| exact MU5| exact WM5| cbn; flia];
          change (w :: repeat (Z_to_bv 64 0) (Z.to_nat (n - 1))) with ([w] ++ repeat (Z_to_bv 64 0) (Z.to_nat (n - 1)));
          apply u32arr_app; split;
          [ eapply u32arr_of_cells; [exact PZ5|]; cbn; rewrite ?app_nil_r; reflexivity
          | cbn [length Z.of_nat Pos.of_succ_nat]; eapply u32arr_of_cells; [exact PZR|]; rewrite u32s_repeat0; f_equal; lia ]
        | intros sg' limbs'; apply mpd_out_same_blocks; cbn; [reflexivity| discriminate| reflexivity]
        | cbn; left; left; reflexivity ] end. }
    assert (NZ : n = 0) by flia. destruct OWF as [(-> & -> & -> & ->)|(_ & N1 & _)]; [| exfalso; lia]. clear NZ LEN.
    lazymatch goal with Hc : rw_cells _ m1 X _, Hf : rw_cells _ m1 (bv_unsigned sp + -32) _, Hs : stk _ m1 _ _, Hi : mem_inv _ m1 |- _ =>
      rename Hc into CH1; rename Hf into FR1; rename Hs into ST1; rename Hi into MI1 end.
    pose proof (run_heap L HI sp h h LB m m1 mo _ X lo HH eq_refl HTOP ACL ltac:(flia) XCW MU1 WM1 ltac:(intros a NO; cbn in NO |- *; flia)) as HH1.
    pose proof (run_statics L sp m m1 _ X lo SOK DHI ACL ltac:(flia) XD MU1 ltac:(intros a NO; cbn in NO |- *; flia)) as SOK1.
    pose proof (run_presx L DIMG sp LB _ m m m1 _ lo HPX0 HBR DHI ACL ltac:(flia) MU1 WM1 ltac:(intros a NO; cbn in NO |- *; flia)) as HPX1.
    pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK1.
    clear ST MI CH FR MK MU1 WM1 HPX0 HH SOK.
    replace (Z_to_bv 64 0x3f960) with (Z_to_bv 64 (hl_calloc L)) by (rewrite HCALLOC; reflexivity).
    eapply aevtM_cut; [ eapply (heap_calloc usegs L HI) with (cnt := 1) (sz := 4) (lo := lo);
      rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by lia; try eassumption; try reflexivity; try lia | ].
    intros ms' mo' PO. unfold call_post in PO. destruct_exs PO. flat constr:(PO) 2%nat. flclear PO. intros E PO.
    injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in PO by lia.
    destruct_ands PO.
    lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m2; rename mox into mo2 end.
    match goal with H : heap_pres _ _ _ _ m1 m2 |- _ => rename H into HPc end.
    match goal with H : stk _ m2 _ _ |- _ => rename H into ST2 end.
    match goal with H : mem_inv _ m2 |- _ => rename H into MI2 end.
    match goal with H : mo_frame mo mo2 |- _ => rename H into MF2 end.
    heap_transport HPc.
    assert (SOK2 : statics_ok usegs L m2) by (eapply statics_ok_heap_pres; [exact SOK1| exact HPc| exact SW]).
    assert (HPX2 : heap_presx usegs L LB (bv_unsigned sp) (mpd_ivs (mkMPD X sg 0 0 [] pad LNull)) m m2).
    { eapply heap_presx_trans; [exact HPX1|]. eapply heap_presx_of_pres_sub; [exact HPc| intros b Hb; exact Hb| lia| lia]. }
    clear HH1 SOK1 HPX1 HPc MK1. try clear ST1. try clear MI1. try clear m1.
    destruct PO as (h2 & HT2 & [[-> HH2] | (A & -> & HBA & HH2 & HNEW)]); pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
    {
      rewrite TP. apply (lxp_aevtM_of_evt usegs mo2 _ _ MK2).
      lx_run_tac (PLANS (@nil Z) [] 40%N (@nil summary)); lx_tree.
      all: apply evt_done; cbv beta; rewrite <- TP; fix_regs.
      all: lazymatch goal with E : @eq mem ?mx ?mc0 |- _ => subst mx end.
      lazymatch goal with Hc : rw_cells _ m2 X _ |- _ => rename Hc into CH end.
      apply aevtM_done. unfold mpi_binop_post. flexi 16%nat. exists h2.
      exists LB, (mkMPD X sg 0 0 [] pad LNull), MBEDTLS_ERR_MPI_ALLOC_FAILED.
      split; [reflexivity|]. split; [assumption|]. split; [assumption|]. split; [exact MF2|]. split; [exact HT2|].
      split; [exact HH2|].
      split; [ split; [|exact SG]; split; [exact CH|]; split; [exact XAL|]; split; [exact X0|]; split; [reflexivity|]; split; [cbn [md_n]; unfold MPI_MAX_LIMBS; lia|];
               cbn [md_own md_n md_p md_limbs]; split; reflexivity |].
      split; [apply mpd_out_refl; cbn; discriminate|].
      split; [exact HPX2|].
      split; [exact SOK2|].
      unfold lset_vR. split; [| intros C; exfalso; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in C; lia]. unfold lset_R. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own mpd_blk]. split; [right; split; reflexivity|]. split; [reflexivity|]. intros b []. }
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH2)) 2%nat. intros HBR2 HAP2. pose proof (HND _ _ _ _ HH2) as ND2.
    pose proof HBA as HBA'. flat constr:(HBA') 5%nat. flclear HBA'. intros A0 A16 _ A4 A5. flat constr:(HAP2) 2%nat. flclear HAP2. intros HAPA _.
    assert (XA' : forall a, X <= a < X + 16 -> ~ (A <= a < A + 1 * 4)).
    { intros a Ha C. destruct (XCW a Ha) as [S|[[D NS]|([B k] & Hb & R)]]; [lia| destruct DIMG; lia| pose proof (HAPA B k Hb); cbn in R; lia]. }
    pose proof (pointwise_apart X 16 A (1 * 4) ltac:(lia) ltac:(lia) XA') as XA. clear XA'.
    lazymatch type of HNEW with ?T => change (lx_hidden T) in HNEW end.
    rewrite TP. apply (lxp_aevtM_of_evt usegs mo2 _ _ MK2).
    lx_run_tac (PLANS [0x46e44] [] 40%N (@nil summary)); lx_tree.
    all: apply evt_done; cbv beta; rewrite <- TP; fix_regs; unfold lx_hidden in HNEW.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    lazymatch goal with Hm : munch ?W m2 m3, Hw : wmono _ m2 m3 |- _ =>
      rename Hm into MU3; rename Hw into WM3; apply (rw_cells_transport usegs W m2 m3) in HNEW; [| exact MU3| exact WM3| cbn; flia] end.
    assert (XCW5 : forall a, X <= a < X + 16 -> client_waddr L ((A, 1 * 4) :: LB) (bv_unsigned sp) (heap_top usegs L HI h) a).
    { intros a Ha. destruct (XCW a Ha) as [C|[C|([B k] & Hb & R)]]; [left; lia| right; left; exact C| right; right; exists (B, k); split; [right; exact Hb|exact R]]. }
    pose proof (run_heap L HI sp h h2 _ m2 m3 mo2 _ X lo HH2 HT2 HTOP ACL ltac:(flia) XCW5 MU3 WM3 ltac:(intros a NO; cbn in NO |- *; flia)) as HH3.
    pose proof (run_statics L sp m2 m3 _ X lo SOK2 DHI ACL ltac:(flia) XD MU3 ltac:(intros a NO; cbn in NO |- *; flia)) as SOK3.
    pose proof (run_presx L DIMG sp LB _ m m2 m3 _ lo HPX2 HBR DHI ACL ltac:(flia) MU3 WM3 ltac:(intros a NO; cbn in NO |- *; flia)) as HPX3.
    clear MU3 WM3 HH2 SOK2 HPX2.
    repeat match goal with H : stk _ m2 _ _ |- _ => clear H | H : mem_inv _ m2 |- _ => clear H | H : rw_cells _ m2 _ _ |- _ => clear H end.
    pose proof (munch_refl [(A, A + 4)] m3) as MU. pose proof (wmono_refl usegs m3) as WM.
    pose proof U_memset_spec as SPs. unfold memset_stmt in SPs.
    eapply aevtM_cut_evt; [ exact MK2 | eapply SPs; rewrite ?unsigned_lit by lia; [ exact HNEW | assumption ] | ].
    clear SPs HNEW. unfold memset_post. rewrite !unsigned_lit by lia. post_call usegs m3.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
    match goal with H : rw_cells usegs m4 A _ |- _ => rename H into PZ end.
    assert (PZ' : rw_cells usegs m4 A [C4 (Z_to_bv 64 0)]).
    { eapply rw_cells_reshape; [exact PZ| cbn; (flsplit; repeat split); reflexivity | cbn -[le4]; reflexivity]. }
    clear PZ.
    assert (HH4 : HEAP usegs L HI h2 ((A, 1 * 4) :: LB) m4 mo2).
    { eapply (Asn1AuxA.HEAP_munch usegs L HI) with (SP := lo); [exact HH3| exact ACL| exact MU| exact WM|].
      intros a Ha NO. cbn in NO. right; right. exists (A, 1 * 4). split; [left; reflexivity| cbn; lia]. }
    assert (HPX4 : heap_presx usegs L LB (bv_unsigned sp) (mpd_ivs (mkMPD X sg 0 0 [] pad LNull)) m m4).
    { eapply heap_presx_trans; [exact HPX3|]. eapply heap_presx_of_munch; [exact MU| exact WM|].
      intros a Ha Hc Ho. cbn. split; [| exact I].
      destruct Hc as [C|[C|([B k] & Hb & R)]]; [flia| destruct DIMG; lia| pose proof (HAPA B k Hb); cbn in R; lia]. }
    assert (MOx : forall sg' limbs', mpd_out LB (mkMPD X sg 0 0 [] pad LNull) ((A, 1 * 4) :: LB) (mkMPD X sg' 1 A limbs' pad LHeap)).
    { intros sg' limbs'. cbn [md_addr md_own mpd_blk md_p md_n]. split; [reflexivity|]. split; [discriminate|].
      split. { intros b [<-|Hb]; [right; left; reflexivity| left; exact Hb]. }
      split. { intros b Hb Hn. right. exact Hb. }
      intros b []. }
    clear HH3 HPX3 MU WM.
    try lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    lazymatch goal with Hc : rw_cells _ m4 X _, Hf : rw_cells _ m4 (bv_unsigned sp + -32) _ |- _ =>
    eapply L_TAIL_v; [exact HH4| exact HT2| exact MF2| assumption| exact HPX4| exact XCW5| exact XD| exact HTOP| exact ACL| flia| flia| exact HBR| exact DHI
      | exact ZB| assumption| assumption| exact Hf| exact Hc| exact XAL| exact X0| cbn [md_addr]; flia| exact PZ'
      | exact A16| left; reflexivity| lia| cbn [md_n]; lia| exact A0| lia| destruct DIMG; lia| cbn [md_addr]; lia| exact XS
      | intros a Ha Hc' Ho; destruct Hc' as [C|[C|([B k] & Hb & R)]]; [lia| destruct DIMG; lia| pose proof (HAPA B k Hb); cbn in R; lia]
      | intros m5 w PZ5 MU5 WM5; eapply u32arr_of_cells; [exact PZ5|]; cbn; rewrite ?app_nil_r; reflexivity
      | exact MOx
      | cbn [mpd_blk md_own md_p md_n]; right; intros Hin; pose proof (HAPA A 4 Hin); lia ] end.
  Qed.
End LSV.
