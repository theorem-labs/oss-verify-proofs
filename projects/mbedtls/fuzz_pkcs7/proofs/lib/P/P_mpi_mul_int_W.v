(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Asn1Aux Asn1AuxA MpiCoreAux HeapIface ZBridge.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts MpiJourney.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import PImg P_string P_platform_zeroize P_mpi_free P_mpi_addsub P_mpi_cmp
     P_mpi_core_mla P_mpi_add_abs_W.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_mpi_mul_int_W () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.Spec.MpiVal.mpd_val"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.Spec.MpiVal.md_n"; "Stdlib.ZArith.BinInt.Z.max"; "Stdlib.ZArith.BinInt.Z.add"; "OSSVerify.KrLib.P.P_mpi_addsub.MBEDTLS_ERR_MPI_ALLOC_FAILED"; "OSSVerify.KrLib.P.P_mpi_addsub.binop_keep"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "OSSVerify.KrLib.Lib.HeapIface.HST"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "OSSVerify.KrLib.Spec.MpiVal.mpd"; "OSSVerify.KrLib.Lib.HeapIface.HEAP"; "OSSVerify.KrLib.Spec.MpiVal.mpd_at"; "OSSVerify.KrLib.Spec.MpiVal.mpd_sep"; "Corelib.Init.Logic.not"; "OSSVerify.KrLib.Spec.Rep.limb_own"; "OSSVerify.KrLib.Spec.MpiVal.md_own"; "OSSVerify.KrLib.Spec.Rep.LStatic"; "OSSVerify.KrLib.P.P_mpi_addsub.opnd_sep"; "stdpp.bitvector.definitions.bv_unsigned"; "OSSVerify.KrLib.Lib.HeapIface.client_range"; "OSSVerify.KrLib.Spec.MpiVal.md_addr"; "OSSVerify.KrLib.Spec.Rep.LHeap"; "OSSVerify.KrLib.Spec.MpiVal.md_p"; "OSSVerify.KrLib.P.P_mpi_addsub.mpd_writable"; "OSSVerify.KrLib.Lib.HeapIface.heap_top"; "OSSVerify.KrLib.Spec.Rep.LNull"; "OSSVerify.KrLib.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.Lib.HeapIface.hl_stack"; "OSSVerify.KrLib.Lib.HeapIface.alloc_ceiling"; "Stdlib.ZArith.BinInt.Z.modulo"; "OSSVerify.KrLib.Lib.HeapIface.hl_data_hi"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.Lib.HeapIface.hl_tp"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.Lib.AStep.statics_ok"; "OSSVerify.KrLib.Lib.AStep.const_at"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.iff"; "OSSVerify.KrLib.Lib.AEvt.aevtM"; "OSSVerify.KrLib.P.P_mpi_addsub.mpi_binop_post"; "mul_int_R"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "OSSVerify.KrLib.Lib.MState.ret_pc"; "OSSVerify.KrLib.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "OSSVerify.KrLib.P.P_mpi_core_mla.MPI_CORE_MLA_STACK"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Frame.wmono"; "OSSVerify.KrLib.Lib.Arr.u32arr"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "Corelib.Lists.ListDef.skipn"; "Stdlib.ZArith.BinInt.Z.to_nat"; "OSSVerify.KrLib.Lib.MpiCoreAux.lval"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "OSSVerify.KrLib.Lib.Arr.u32s"; "Stdlib.ZArith.BinInt.Z.of_nat"; "OSSVerify.KrLib.Lib.Exec.evt"; "mpi_core_mla_vpost"; "OSSVerify.KrLib.P.PImg.psegs"; "OSSVerify.KrLib.Spec.MpiVal.mkMPD"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "W.MI_FRAME"; "OSSVerify.KrLib.Lib.Frame.ivl"; "OSSVerify.KrLib.Spec.MpiJourney.XJ"; "W.MI_POST"; "OSSVerify.KrLib.Spec.MpiJourney.BJ"; "OSSVerify.KrLib.Spec.MpiVal.md_sg"; "OSSVerify.KrLib.Spec.Rep.limbs_val"; "OSSVerify.KrLib.Spec.MpiVal.md_limbs"; "W.KC_stmt"; "OSSVerify.KrLib.Spec.MpiJourney.JB"].


Definition P_MPI_MUL_INT : Z := 0x1f3cc.
Definition P_MPI_COPY : Z := 0x1ef9c.

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
Definition mi_frame (j0 : list byte) (ra s0 s1 s2 s3 s4 s5 : word) : list cell :=
  [CB 8 j0; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

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
  Variable HI : heap_iface psegs L.
  Hypothesis HFREE : hl_free L = P_FREE.
  Hypothesis HCALLOC : hl_calloc L = P_CALLOC.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m : mem) (mo : Model) (h : HST psegs L HI) (LB : list blk) (dA : mpd) (b lo : Z) (MSF : Z) (j0 : list byte)
            (X sX nX pX : Z) (xs0 : list word) (padX : word) (ownX : limb_own).
  Local Notation dX := (mkMPD X sX nX pX xs0 padX ownX).
  Hypothesis MSFE : MSF = P_MEMSET_FUNC.
  Hypothesis CA : const_at L MSF 8.
  Hypothesis TP : tp = Z_to_bv 64 (hl_tp L).
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SLO2 : lo <= bv_unsigned sp - 160 - hl_stack L.
  Hypothesis BB : 0 <= b < 2^32.
  Variable wb : word.
  Hypothesis WB1 : bv_unsigned wb mod 2^32 = b.
  Hypothesis WB0 : bv_unsigned wb = 0 <-> b = 0.
  Definition MI_FRAME := mi_frame j0 ra s0 s1 s2 s3 s4 s5.
  Hypothesis JCX : JC psegs L HI h LB m mo dX sp lo 64 MI_FRAME.
  Definition MI_POST := ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_int_W ()) "(33.$4>.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,(4?.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(34.Vb,VLB,(4?.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,)Vlo,Vm,Vmo,)")
(* [comment removed for export] *).

  Local Ltac jc_open := pose proof JCX as [HLS SW DIMG HND ROIMG DHI HH MX NST XW XLS ACL FS0 SLO HTOP FSZ].
  Local Notation XJ0 := (XJ psegs L HI h LB m mo dX sp lo 64 MI_FRAME []).
  Local Notation XJ1 An cnt := (XJ psegs L HI h LB m mo dX sp lo 64 MI_FRAME [(An, 4 * cnt)]).
  Local Notation FB0 := (FB psegs L LB dX).
  Local Notation JBE dE := (JB psegs L LB m dX sp lo dE).
  Local Notation BJE dE := (BJ psegs sp dE).
  Local Ltac xj_open J := pose proof J as [MI1 ST1 FR1 HH1 HT1 MF1 SOK1 MX1 AD1 PD1 NS1 OUT1 FRS1 HPX1 XP1 NM1]; cbn [app] in HH1.

  (* [comment removed for export] *)
  #[using="L HI m mo h LB b lo X sX nX pX xs0 padX ownX wb WB0 JCX"] Lemma mi_epilogue : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_int_W ()) "Pt0,(<.&40.)Pt1,(<.&40.)Pt2,(<.&40.)Praj,(<.&40.)Px8,(<.&40.)Px9,(<.&40.)Pa0,(<.&40.)Pa1,(<.&40.)Pa2,(<.&40.)Pa3,(<.&40.)Pa4,(<.&40.)Pa5,(<.&40.)Pa6,(<.&40.)Pa7,(<.&40.)Px18,(<.&40.)Px19,(<.&40.)Px20,(<.&40.)Px21,(<.&40.)Pt3,(<.&40.)Pt4,(<.&40.)Pt5,(<.&40.)Pt6,(<.&40.)Pm1,P,(<.&40.)(>.(<.&8.))P,(50.$4>.R1.(25.(1<.&40.Vsp,)+40.)$51.)P,(2<.$4>.R2.)(4<.$4>.Lms',$39.(0.(2.$39.R1.(35.(36.Vra,Vsp,Vgp,Vtp,R1:.R19.R18.Vs0,Vs1,R14.R13.R12.R11.R10.R?.R>.R=.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R8.R7.R6.R5.)VF,(3;.Vra,)Vfc,(37.(<.&40.))R4.(38.$4>.)))(0.(3<.(41.$52.)R4.R4.)(0.(42.$4>.R4.R4.)(2<.$4>.R4.))))(35.(36.R16.(2:.&40.(25.(1<.&40.Vsp,)+40.))Vgp,Vtp,R19.R18.R17.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R7.R6.R5.R4.)VF,(2:.&40.+1?540.)Vfc,(37.(<.&40.))R3.(38.$4>.)))")
(* [comment removed for export] *).
  Proof.
    jc_open. intros until m1. intros FR MI. pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    unfold MI_FRAME, mi_frame in FR.
    pose proof (munch_refl ([] : list ivl) m1) as MU. pose proof (wmono_refl psegs m1) as WM.
    do 9 zstep.
    replace (Z_to_bv 64 (bv_unsigned sp - 64 + 64)) with (Z_to_bv 64 (bv_unsigned sp)) by (f_equal; lia). rewrite Z_to_bv_bv_unsigned.
    finish.
  Qed.

  (* [comment removed for export] *)
  #[using="wb WB0 JCX"] Lemma mi_ret : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_int_W ()) "Pt0,(<.&40.)Pt1,(<.&40.)Pt2,(<.&40.)Praj,(<.&40.)Px8,(<.&40.)Px9,(<.&40.)Pa1,(<.&40.)Pa2,(<.&40.)Pa3,(<.&40.)Pa4,(<.&40.)Pa5,(<.&40.)Pa6,(<.&40.)Pa7,(<.&40.)Px18,(<.&40.)Px19,(<.&40.)Px20,(<.&40.)Px21,(<.&40.)Pt3,(<.&40.)Pt4,(<.&40.)Pt5,(<.&40.)Pt6,(<.&40.)Phc,(10.$4>.VL,VHI,)PLBc,(11.$12.)Pmc,P,(<.&40.)(>.(<.&8.))Pmoc,$?.PdXc,$13.Pr,$3.P,(53.$4>.VL,VHI,Vh,VLB,Vm,Vmo,(4?.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+40.$51.(41.$12.)R6.R5.R4.R3.R2.)P,(1.(0.(2.$3.R2.=)(0.(2.$3.(4.R3.)(5.(4.VdA,)Vb,))(6.(7.R3.)(8.VnX,(9.(7.VdA,)+1.)))))(2.$3.R2.$:.))(32.$4>.R5.$54.(35.(36.R1:.(2:.&40.(25.(1<.&40.Vsp,)+40.))Vgp,Vtp,R1=.R1<.R1;.R19.R18.(2:.&40.R3.)R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R<.R;.R:.R9.)VF,(2:.&40.+1?540.)Vfc,(37.(<.&40.))R6.(38.$4>.)))")
(* [comment removed for export] *).
  Proof.
    intros until r. intros J HR. pose proof (xj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ J) as (_ & _ & _ & MK & _).
    eapply aevtM_cut_evt; [exact MK| eapply mi_epilogue; [exact (xj_fr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J)| exact (xj_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J)]|].
    cbv beta. intros ms' (-> & _). apply aevtM_done. unfold MI_POST. eapply xj_post; [exact JCX| exact J|].
    split; [exact HR|]. split; [exact (xj_addr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J)|]. split; [exact (xj_pad _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J)|].
    split; [exact (xj_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J)| exact (xj_nmono _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J)].
  Qed.

  #[using="wb WB0 JCX"] Lemma mi_retm16 : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_int_W ()) "Pt0,(<.&40.)Pt1,(<.&40.)Pt2,(<.&40.)Praj,(<.&40.)Px8,(<.&40.)Px9,(<.&40.)Pa0,(<.&40.)Pa1,(<.&40.)Pa2,(<.&40.)Pa3,(<.&40.)Pa4,(<.&40.)Pa5,(<.&40.)Pa6,(<.&40.)Pa7,(<.&40.)Px18,(<.&40.)Px19,(<.&40.)Px20,(<.&40.)Px21,(<.&40.)Pt3,(<.&40.)Pt4,(<.&40.)Pt5,(<.&40.)Pt6,(<.&40.)Phc,(10.$4>.VL,VHI,)PLBc,(11.$12.)Pmc,P,(<.&40.)(>.(<.&8.))Pmoc,$?.PdXc,$13.P,(53.$4>.VL,VHI,Vh,VLB,Vm,Vmo,(4?.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+40.$51.(41.$12.)R5.R4.R3.R2.R1.)(32.$4>.R3.$54.(35.(36.R19.(2:.&40.(25.(1<.&40.Vsp,)+40.))Vgp,Vtp,R1<.R1;.R1:.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R:.R9.R8.R7.)VF,(2:.&40.+1?564.)Vfc,(37.(<.&40.))R4.(38.$4>.)))")
(* [comment removed for export] *).
  Proof.
    intros until dXc. intros J. pose proof (xj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ J) as (_ & _ & _ & MK & _).
    pose proof (xj_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J) as MI.
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl psegs mc) as WM.
    zstep. zstep. eapply mi_ret; [exact J|]. right. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition KC_stmt (n : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_int_W ()) "Pt0,(<.&40.)Pt1,(<.&40.)Pt2,(<.&40.)Praj,(<.&40.)Pa0,(<.&40.)Pa2,(<.&40.)Pa3,(<.&40.)Pa4,(<.&40.)Pa5,(<.&40.)Pa6,(<.&40.)Pa7,(<.&40.)Px18,(<.&40.)Px19,(<.&40.)Px21,(<.&40.)Pt3,(<.&40.)Pt4,(<.&40.)Pt5,(<.&40.)Pt6,(<.&40.)Phc,(10.$4>.VL,VHI,)PLBc,(11.$12.)Pmc,P,(<.&40.)(>.(<.&8.))Pmoc,$?.PdXc,$13.P,(53.$4>.VL,VHI,Vh,VLB,Vm,Vmo,(4?.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+40.$51.(41.$12.)R5.R4.R3.R2.R1.)P,P,(17.(2.$3.(1>.VdA,)VX,))(55.$4>.Vsp,VdA,R6.R5.R3.)P,(2.$18.(19.R3.)$1?.)P,(6.(9.O1.+1.)(7.R4.))P,(6.(7.R5.)(8.VnX,(9.O1.+1.)))P,(2.$3.(56.R6.)VsX,)P,(2.$3.(57.(58.R7.))(57.Vxs0,))P,(2.$3.(48.(58.R8.)O1.)(57.Vxs0,))(32.$4>.R:.$54.(35.(36.R1<.(2:.&40.(25.(1<.&40.Vsp,)+40.))Vgp,Vtp,R1?.R1>.R1=.(2:.&40.VX,)(2:.&40.O1.)R1;.(2:.&40.(1>.VdA,))R1:.R19.R18.R17.R16.R15.R14.R13.Vwb,R12.Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R11.R10.R?.R>.)VF,(2:.&40.+1?494.)Vfc,(37.(<.&40.))R;.(38.$4>.)))")
(* [comment removed for export] *).

  #[using="HFREE HCALLOC MSF MSFE CA TP SPA BB WB0 JCX"] Lemma mi_G : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_int_W ()) "Pn,$3.Pt0,(<.&40.)Pt1,(<.&40.)Pt2,(<.&40.)Praj,(<.&40.)Pa0,(<.&40.)Pa2,(<.&40.)Pa3,(<.&40.)Pa4,(<.&40.)Pa5,(<.&40.)Pa6,(<.&40.)Pa7,(<.&40.)Px18,(<.&40.)Px19,(<.&40.)Px21,(<.&40.)Pt3,(<.&40.)Pt4,(<.&40.)Pt5,(<.&40.)Pt6,(<.&40.)Phc,(10.$4>.VL,VHI,)PLBc,(11.$12.)Pmc,P,(<.&40.)(>.(<.&8.))Pmoc,$?.PdXc,$13.P,(59.R18.)P,(53.$4>.VL,VHI,Vh,VLB,Vm,Vmo,(4?.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+40.$51.(41.$12.)R6.R5.R4.R3.R2.)P,P,(17.(2.$3.(1>.VdA,)VX,))(0.(5:.$4>.VL,VLB,Vm,(4?.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,VdA,)(55.$4>.Vsp,VdA,R7.R6.R4.))P,(0.(6.(7.R4.)R1;.)(2?.R1;.+2710.))P,(6.+1.R1<.)P,(2.$3.(56.R6.)VsX,)P,(2.(11.(<.&40.))(58.R7.)Vxs0,)P,(2.$3.(48.Vxs0,R1?.)(57.Vxs0,))(32.$4>.R:.$54.(35.(36.R1<.(2:.&40.(25.(1<.&40.Vsp,)+40.))Vgp,Vtp,R1?.R1>.R1=.(2:.&40.VX,)(2:.&40.R20.)R1;.(2:.&40.(1>.VdA,))R1:.R19.R18.R17.R16.R15.R14.R13.Vwb,R12.Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R11.R10.R?.R>.)VF,(2:.&40.+1?440.)Vfc,(37.(<.&40.))R;.(38.$4>.)))")
(* [comment removed for export] *).
  Proof.
    intros until dXc. intros K1 J AJ CNT N1 SG1 LE HV. jc_open. unfold KC_stmt in K1.
    destruct dA as [Aa sA nA pA ys padA ownA]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in K1, AJ.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof alloc_ceiling_bounds as ACV.
    pose proof (xj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ J) as (HBR1 & HAP1 & ND1 & MK1 & XS & X0 & X16 & XAL & LEN1 & NR1 & OWN0 & OWN1). cbn [app] in HBR1, HAP1, ND1.
    xj_open J.
    destruct dXc as [X' sg nXc pXc xs pad' own]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. subst X' pad' sg xs.
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl psegs mc) as WM.
    zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    replace (Z_to_bv 64 0x3c268) with (Z_to_bv 64 (hl_calloc L)) by (rewrite HCALLOC; reflexivity).
    eapply aevtM_cut; [ eapply (heap_calloc psegs L HI) with (cnt := n + 1) (sz := 4) (lo := lo);
      rewrite ?(unsigned_lit (bv_unsigned sp - 64)) by (clear - SPB SLO HLS ACL ACP; lia); try eassumption; try reflexivity;
      clear - SLO HLS ACL ACP HTOP HT1 CNT NR1 SPB; try lia | ].
    intros ms' mo' PO. unfold call_post in PO. destruct_exs PO. destruct PO as [E PO]. injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp - 64)) in PO by (clear - SPB SLO HLS ACL ACP; lia).
    ddestruct PO as (MI2 & ST2 & MF2 & HPc & h2 & HT2 & RES2).
    replace (ret_pc (Z_to_bv 64 128084)) with (Z_to_bv 64 128084) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m2; rename mox into mo2 end.
    clear MU WM.
    destruct RES2 as [[-> HH2] | (An & -> & HBA & HH2 & HNEW)].
    { (* [comment removed for export] *)
      pose proof (xj_calloc_fail _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ J MI2 ST2 MF2 HPc HT2 HH2) as J2.
      pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
      pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl psegs m2) as WM.
      zstep. zstep. zstep. if_cases KZ; zify_cond KZ; [| exfalso; apply KZ; reflexivity].
      eapply mi_ret; [exact J2| right; reflexivity]. }
    (* [comment removed for export] *)
    replace ((n + 1) * 4) with (4 * (n + 1)) in * by (clear; lia).
    destruct (xj_calloc_ok _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ _ J MI2 ST2 MF2 HPc HT2 HH2 HBA HNEW ltac:(cbn [md_n]; clear - CNT; lia)) as [J2 F2].
    assert (AJ2 : Aa <> X -> JBE (mkMPD Aa sA nA pA ys padA ownA) /\ BJE (mkMPD Aa sA nA pA ys padA ownA) LBc m2 (mkMPD X sX nXc pXc xs0 padX own)).
    { intros NE. destruct (AJ NE) as [DBJ B]. split; [exact DBJ|]. eapply (bj_heap_pres _ _ _ _ _ _ _ _ _ _ _ _ JCX _ DBJ); [exact J| exact B| exact HPc| exact MI2]. }
    dpose HBA as (An0 & An16 & _ & AnC & AnI). pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
    clear HPc J AJ MI1 ST1 FR1 HH1 HT1 MF1 SOK1 MX1 NS1 OUT1 FRS1 HPX1 XP1 NM1.
    xj_open J2. pose proof MX1 as [(CX2 & _) _]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX2. unfold mpi_cells in CX2.
    pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl psegs m2) as WM.
    zstep. zstep. zstep. if_cases KZ; zify_cond KZ; [exfalso; clear - KZ An0 AnC ACV CNT NR1; lia|].
    zstep. zstep. if_cases KP; zify_cond KP.
    { (* [comment removed for export] *)
      assert (EO : own = LNull).
      { destruct own; [reflexivity| | exfalso; exact (NS1 eq_refl)]. exfalso. ddestruct (OWN1 ltac:(discriminate)) as (_ & N1' & _ & _ & _ & P0 & PC & _). rewrite Z.mod_small in KP by (clear - N1' P0 PC ACV; lia). clear - KP P0. lia. }
      subst own. pose proof (xg_null _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ J2 F2 eq_refl) as D2.
      destruct (OWN0 eq_refl) as [EP EN]. cbn [md_p md_n] in EP, EN. subst pXc nXc.
      clear MU WM. pose proof (munch_refl [(X, X + 16)] m2) as MU. pose proof (wmono_refl psegs m2) as WM.
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
    zstep. rewrite zx16_small by (clear - NR1; lia). zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep. zstep.
    pose proof P_memcpy_spec as SPc. unfold memcpy_stmt in SPc.
    assert (U1 : bv_unsigned (Z_to_bv 64 An) = An) by (apply unsigned_lit; clear - An0 AnC ACV CNT NR1; lia).
    assert (U2 : bv_unsigned (Z_to_bv 64 pXc) = pXc) by (apply unsigned_lit; clear - P0 PC ACV N1'; lia).
    assert (U3 : bv_unsigned (Z_to_bv 64 (nXc * 4)) = nXc * 4) by (apply unsigned_lit; clear - N1' CNT; lia).
    eapply aevtM_cut_evt; [ exact MK2 | eapply SPc with (src := u32s xs0); rewrite ?U1, ?U2, ?U3;
      [ exact SBY | rewrite SLEN; clear; lia | replace (Z.to_nat (nXc * 4)) with (4 * length (firstn (Z.to_nat nXc) (repeat (Z_to_bv 64 0) (Z.to_nat (n + 1)))))%nat by (rewrite DLEN; clear; lia); exact DST
      | clear - SEP; lia | exact MI2 ] | ].
    clear SPc. unfold memcpy_post. cbv beta. intros ms' PO.
    ddestruct PO as (z0 & z1 & z2 & za1 & za2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & m3 & E & MUd & WMd & MI3 & PA3 & _). subst ms'.
    rewrite ?U1, ?U2, ?U3 in MUd. rewrite ?U1, ?U2, ?U3 in PA3.
    replace (ret_pc (Z_to_bv 64 128120)) with (Z_to_bv 64 128120) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    replace (An + nXc * 4) with (An + 4 * nXc) in MUd by (clear; lia). replace (Z.to_nat (nXc * 4)) with (Z.to_nat (4 * nXc)) in PA3 by (clear; lia).
    destruct (xg_memcpy_post _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ J2 F2 eq_refl MUd WMd MI3 PA3) as [J3 F3]. cbn [md_limbs md_n] in F3.
    assert (AJ3 : Aa <> X -> JBE (mkMPD Aa sA nA pA ys padA ownA) /\ BJE (mkMPD Aa sA nA pA ys padA ownA) LBc m3 (mkMPD X sX nXc pXc xs0 padX LHeap)).
    { intros NE. destruct (AJ2 NE) as [DBJ B2]. split; [exact DBJ|].
      pose proof (bj_fb_apart _ _ _ _ _ _ _ _ _ _ _ _ JCX _ DBJ _ _ _ _ _ _ _ _ J2 F2 B2) as [ESA ELA]. cbn [md_addr md_own md_p md_n] in ESA, ELA.
      exact (bj_munch _ _ _ _ _ _ _ _ _ _ _ _ JCX _ DBJ _ _ _ _ _ B2 MUd WMd ltac:(cbn; clear - ESA CNT; lia) ltac:(intros BN; cbn; pose proof (ELA BN); clear - H CNT; lia)). }
    clear J2 F2 AJ2 MU WM DST SBY CX2 ST2 MI2 MK2 MI1 ST1 HT1 MF1 MX1 NS1 OUT1 FRS1 XP1 AD1 PD1 NM1.
    pose proof (munch_refl ([] : list ivl) m3) as MU. pose proof (wmono_refl psegs m3) as WM.
    xj_open J3. pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK3.
    destruct (xg_zfree_pre _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ J3 F3 eq_refl) as (ZIN & ZCH & ZLEN & ZB). cbn [md_p md_n md_limbs] in ZIN, ZCH, ZLEN, ZB.
    (* [comment removed for export] *)
    pose proof MX1 as [(CX3 & _) _]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX3. unfold mpi_cells in CX3.
    zstep. rewrite zx16_small by (clear - NR1; lia). zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep.
    eapply aevtM_cut.
    { eapply (P_zeroize_and_free_spec L HI HFREE HLS SW DIMG) with (buf := pXc) (len := 4 * nXc) (lo := lo) (junk := u32s xs0);
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
    replace (ret_pc (Z_to_bv 64 128136)) with (Z_to_bv 64 128136) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    pose proof (xg_zfree_post _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ _ _ J3 F3 eq_refl MI4 ST4 MF4 HT4 HH4 PX4 SOK4) as D4.
    assert (AJ4 : Aa <> X -> JBE (mkMPD Aa sA nA pA ys padA ownA) /\ BJE (mkMPD Aa sA nA pA ys padA ownA) (lb_remove pXc LBc) m4 (mkMPD X sX nXc pXc xs0 padX LHeap)).
    { intros NE. destruct (AJ3 NE) as [DBJ B3]. split; [exact DBJ|].
      pose proof (bj_zfree _ _ _ _ _ _ _ _ _ _ _ _ JCX _ DBJ _ _ _ _ _ _ _ _ _ J3 F3 B3 eq_refl PX4 MI4) as B4. cbn [md_p] in B4. exact B4. }
    pose proof (heap_mok _ _ HI _ _ _ _ HH4) as MK4.
    clear J3 F3 AJ3 MI1 ST1 FR1 HH1 HT1 MF1 SOK1 MX1 NS1 OUT1 FRS1 HPX1 XP1 AD1 PD1 NM1 MU WM MK3 HH4 PX4 ZCH PA3 MUd WMd MI3 SOK4.
    pose proof (xd_struct _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D4) as CX4. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX4. unfold mpi_cells in CX4.
    pose proof (munch_refl [(X, X + 16)] m4) as MU. pose proof (wmono_refl psegs m4) as WM.
    zstep. zstep.
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
