(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Arr MpiCoreAux MpiWalkAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_mpi_core_mla U_ct_memcpy_if.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Export LxSum LxSoundSum.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr LxDec LxMem LxStep LxRun LxDenot LxSoundRun LxTac LxDex.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_LxP_SumsArr () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32s"; "Corelib.Init.Peano.le"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Lists.ListDef.skipn"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "Corelib.Init.Logic.eq"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.LX.LxSum.SUMG"; "Corelib.Init.Datatypes.false"; "Corelib.Numbers.BinNums.positive"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.mfact"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.MArr"; "q"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.LBase"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.pfact"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FEq"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.ELit"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FLe"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FAl"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.EAdd"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.EMulC"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FLt"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.expr"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_core_mla.U_MPI_CORE_MLA"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FSep"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.EZv"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FOr2"; "Stdlib.ZArith.BinInt.Z.opp"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_core_mla.MPI_CORE_MLA_STACK"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.two64"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.MStk"; "RocqVerifyHarness.AgentSubmission.U.U_ct_memcpy_if.U_CT_MEMCPY_IF"; "RocqVerifyHarness.AgentSubmission.U.U_ct_memcpy_if.CT_MEMCPY_IF_STACK"].


Definition q (i : positive) : expr := EZv i.
Notation "a .+ b" := (EAdd a b) (at level 50, left associativity).
Notation "a .- b" := (EAdd a (EMulC (-1) b)) (at level 50, left associativity).

(* [comment removed for export] *)
Ltac lxp_pows :=
  try change (2 ^ Z.of_N 1)%Z with 2%Z in *; try change (2 ^ Z.of_N 2)%Z with 4%Z in *;
  try change (2 ^ Z.of_N 3)%Z with 8%Z in *; try change (2 ^ Z.of_N 4)%Z with 16%Z in *.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lxp_uw64 : forall z, 0 <= z -> z <= two64 - 1 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z A B. apply unsigned_lit. unfold two64 in B. lia. Qed.

Lemma lxp_u32ro_skipn : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsArr ()) "Psegs,(0.$1.)Pm,P,(2.&40.)(3.(2.&8.))PA,$4.Pws,(0.(2.&40.))Pi,$5.P,(6.R5.R4.R3.(7.R2.))P,(8.R2.(9.(2.&40.)R3.))(6.R7.R6.(:.R5.(;.+4.(<.R3.)))(7.(=.(2.&40.)R3.R4.)))")
(* [comment removed for export] *).
Proof.
  intros segs m A ws i H Hi. rewrite <- (firstn_skipn i ws) in H. rewrite u32s_app in H.
  apply bytes_at_app in H. destruct H as [_ H]. rewrite u32s_length, firstn_length in H.
  replace (A + Z.of_nat (4 * Nat.min i (length ws))) with (A + 4 * Z.of_nat i) in H by lia. exact H.
Qed.

(* [comment removed for export] *)
Lemma lxp_memset_limbs : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsArr ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(>.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PX,$4.Pws,(0.(2.&40.))Pi,$4.Pk,$4.P,(?.$10.R5.R4.R3.)P,(11.=R5.)P,(12.=R4.)P,(12.=R4.)P,(12.(:.R6.R5.)(<.(9.(2.&40.)R7.)))P,(11.(:.R9.(;.+4.R7.))(13.+2.+40.))P,(14.$10.R;.)P,(15.(2.&40.)R24.(16.&40.(:.R;.(;.+4.R9.))))P,(15.(2.&40.)R24.(16.&40.=))P,(15.(2.&40.)R24.(16.&40.(;.+4.R:.)))(17.$10.Lms',$18.(19.(2.&40.)Lt0',(2.&40.)(19.(2.&40.)Lt1',(2.&40.)(19.(2.&40.)Lt2',(2.&40.)(19.(2.&40.)La1',(2.&40.)(19.(2.&40.)La2',(2.&40.)(19.(2.&40.)La3',(2.&40.)(19.(2.&40.)La4',(2.&40.)(19.(2.&40.)La5',(2.&40.)(19.(2.&40.)La6',(2.&40.)(19.(2.&40.)La7',(2.&40.)(19.(2.&40.)Lt3',(2.&40.)(19.(2.&40.)Lt4',(2.&40.)(19.(2.&40.)Lt5',(2.&40.)(19.(2.&40.)Lt6',(2.&40.)(19.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(19.(0.(2.&40.))Lws',(0.(2.&40.))(1:.(15.$18.R11.(1;.(1<.R41.R40.R3?.R3>.R10.R?.R>.R3:.R39.R38.R=.R<.R;.R:.R9.R8.R7.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R6.R5.R4.R3.)R22.(1=.R41.)R21.(1>.(2.&40.))R2.(1?.$10.)))(1:.(20.(21.(22.$4.$4.)(23.$4.$4.(:.R1?.(;.+4.R1=.))(:.(:.R1?.(;.+4.R1=.))(;.+4.R1<.)))(24.(22.$4.$4.)))R20.R2.)(1:.(25.$10.R20.R2.)(1:.(14.$10.R2.)(1:.(?.$10.R2.R1?.R1.)(15.$5.(9.(2.&40.)R1.)(9.(2.&40.)R1>.)))))))))))))))))))))))(1;.(1<.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.)R11.(16.&40.+46>44.)R10.(1>.(2.&40.))R?.(1?.$10.)))")
(* [comment removed for export] *).
Proof.
  intros until k. intros U XP Hi Hk Hik XT MI -> -> ->.
  pose proof (u32arr_bound _ _ _ _ U) as UB.
  destruct (split3 ws (Z.to_nat i) (Z.to_nat (i + k)) ltac:(lia) ltac:(lia)) as (EY & LA & LB).
  set (A := firstn (Z.to_nat i) ws) in *. set (Bm := firstn _ (skipn _ ws)) in *. set (C := skipn (Z.to_nat (i + k)) ws) in *.
  assert (LC : length C = (length ws - Z.to_nat (i + k))%nat) by (subst C; rewrite skipn_length; lia).
  pose proof U as U0. rewrite EY in U. apply u32arr_app in U. destruct U as [UA U]. apply u32arr_app in U. destruct U as [UBm UC].
  rewrite LA in UBm, UC. rewrite LB in UC. apply u32arr_cells in UBm. rewrite LB in UBm.
  replace (X + 4 * Z.of_nat (Z.to_nat i)) with (X + 4 * i) in UBm, UC by lia.
  pose proof U_memset_spec as SP. unfold memset_stmt in SP.
  eapply evt_mono.
  { eapply SP; [| exact MI]. rewrite !unsigned_lit by lia.
    replace (Z.to_nat (4 * k)) with (4 * (Z.to_nat (i + k) - Z.to_nat i))%nat by lia. exact UBm. }
  clear SP. intros ms' PO. unfold memset_post in PO. rewrite !unsigned_lit in PO by lia.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m' & -> & MU & WM & MI' & HZ).
  apply (u32arr_of_cells usegs m' _ _ _ (repeat (Z_to_bv 64 0) (Z.to_nat k))) in HZ;
    [| rewrite u32s_repeat0; replace (bv_unsigned (Z_to_bv 64 0) mod 256) with 0 by reflexivity; f_equal; lia ].
  do 15 eexists. exists (A ++ (repeat (Z_to_bv 64 0) (Z.to_nat k) ++ C)).
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split.
  - apply u32arr_app. split.
    + eapply u32arr_transport; [exact UA| exact MU| exact WM| cbn; rewrite LA; lia].
    + rewrite LA. apply u32arr_app. split.
      * replace (X + 4 * Z.of_nat (Z.to_nat i)) with (X + 4 * i) by lia. exact HZ.
      * rewrite repeat_length. replace (X + 4 * Z.of_nat (Z.to_nat i) + 4 * Z.of_nat (Z.to_nat k)) with (X + 4 * i + 4 * Z.of_nat (Z.to_nat (i + k) - Z.to_nat i)) by lia.
        eapply u32arr_transport; [exact UC| exact MU| exact WM| cbn; rewrite LC; lia].
  - rewrite !app_length, repeat_length, LA, LC. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SUM_memsetWP (k : nat) : summary := ltac2:(CDefT.buildp (gd_tbl_LxP_SumsArr ()) "(26.+46>44.$27.#5.#>.#0.(21.(22.$4.$28.)(23.$4.$28.+:.^2.)(21.(22.$4.$28.)(23.$4.$28.+;.^3.)(21.(22.$4.$28.)(23.$4.$28.+<.^4.)(24.(22.$4.$28.)))))(21.(22.$28.$5.)(23.$28.$5.^1.O1.)(24.(22.$28.$5.)))(1>.$28.)(21.$29.(2:.(2;.^1.)&4.(2<.^1.)(2;.^5.)$2=.)(24.$29.))(1>.(22.$28.$28.))(24.(22.(22.$28.$28.)$28.))(24.$29.)(21.$2>.(2?.(2;.^3.)(30.=))(21.$2>.(31.(2;.^1.)(2;.^2.))(21.$2>.(32.(33.(2;.^2.)(34.-1.(2;.^1.)))&2.)(21.$2>.(32.(2;.^4.)&2.)(21.$2>.(31.(30.=)(2;.^4.))(21.$2>.(31.(33.(2;.^2.)(2;.^4.))(33.(2;.^1.)(34.+4.(2;.^5.))))(21.$2>.(35.(30.=)(2;.^1.))(21.$2>.(35.(2;.^2.)(30.(13.+2.+40.)))(24.$2>.)))))))))(21.(22.$36.$36.)(23.$36.$36.(2;.^2.)(33.(2;.^2.)(2;.^4.)))(24.(22.$36.$36.)))(21.(22.$4.$28.)(23.$4.$28.+5.^6.)(21.(22.$4.$28.)(23.$4.$28.+6.^7.)(21.(22.$4.$28.)(23.$4.$28.+7.^8.)(21.(22.$4.$28.)(23.$4.$28.+;.^9.)(21.(22.$4.$28.)(23.$4.$28.+<.^:.)(21.(22.$4.$28.)(23.$4.$28.+=.^;.)(21.(22.$4.$28.)(23.$4.$28.+>.^<.)(21.(22.$4.$28.)(23.$4.$28.+?.^=.)(21.(22.$4.$28.)(23.$4.$28.+10.^>.)(21.(22.$4.$28.)(23.$4.$28.+11.^?.)(21.(22.$4.$28.)(23.$4.$28.+1<.^10.)(21.(22.$4.$28.)(23.$4.$28.+1=.^11.)(21.(22.$4.$28.)(23.$4.$28.+1>.^12.)(21.(22.$4.$28.)(23.$4.$28.+1?.^13.)(24.(22.$4.$28.))))))))))))))))(21.$29.(2:.(2;.^1.)&4.(2<.^2.)(2;.^5.)$2=.)(24.$29.))(24.$2>.))")
(* [comment removed for export] *).

Lemma sum_memsetWP_valid : forall AL GS k, summary_validG usegs AL GS (SUM_memsetWP k).
Proof.
  intros AL GS k. unfold SUM_memsetWP, q. lx_sum_unfold.
  intros X p v n NX xs CS F fc m.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
  intros ALLCS _ MI GB R10 R11 R12 _ [HX LX] PR1 PR2 PR3 PR4 PR5 PR6 PR7 PR8.
  lxp_pows.
  apply (evt_evtA_all usegs AL CS _ _ ALLCS).
  pose proof (u32arr_bound _ _ _ _ HX) as XB.
  set (i := (p - X) / 4). set (kk := n / 4).
  assert (Ep : p = X + 4 * i) by (subst i; lia). assert (En : n = 4 * kk) by (subst kk; lia).
  rewrite Ep in R10. rewrite En in R12. subst v.
  eapply evt_cut.
  { eapply (lxp_memset_limbs x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
                                 x24 x25 x26 x27 x28 x29 x30 x31 F fc m X xs i kk);
      first [exact HX | exact MI | exact R10 | exact R11 | exact R12 | lia]. }
  cbv beta. intros ms' PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & xs' & -> & MU & WM & MI' & HX' & LEN').
  apply evt_done. rewrite <- Ep in MU. replace (p + 4 * kk) with (p + n) in MU by lia.
  lx_sum_post.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SUM_mlaWP (k : nat) : summary := ltac2:(CDefT.buildp (gd_tbl_LxP_SumsArr ()) "(26.$37.$27.#:.#?.#0.(21.(22.$4.$28.)(23.$4.$28.+:.^2.)(21.(22.$4.$28.)(23.$4.$28.+;.^3.)(21.(22.$4.$28.)(23.$4.$28.+<.^4.)(21.(22.$4.$28.)(23.$4.$28.+=.^5.)(21.(22.$4.$28.)(23.$4.$28.+2.^8.)(21.(22.$4.$28.)(23.$4.$28.+1.^:.)(24.(22.$4.$28.))))))))(21.(22.$28.$5.)(23.$28.$5.^1.O1.)(24.(22.$28.$5.)))(1>.$28.)(21.$29.(2:.(2;.^1.)&4.(2<.^1.)(2;.^6.)$2=.)(21.$29.(2:.(2;.^4.)&4.(2<.^2.)(2;.^7.)$27.)(24.$29.)))(38.(22.$28.$28.)(23.$28.$28.^9.^8.))(24.(22.(22.$28.$28.)$28.))(24.$29.)(21.$2>.(31.(2;.^1.)(2;.^2.))(21.$2>.(32.(33.(2;.^2.)(34.-1.(2;.^1.)))&2.)(21.$2>.(31.(30.=)(2;.^3.))(21.$2>.(31.(2;.^3.)(30.+2710.))(21.$2>.(31.(30.=)(2;.^5.))(21.$2>.(31.(2;.^5.)(30.+2710.))(21.$2>.(31.(33.(2;.^2.)(34.+4.(2;.^3.)))(33.(2;.^1.)(34.+4.(2;.^6.))))(21.$2>.(31.(2;.^5.)(2;.^7.))(21.$2>.(39.(2;.^4.)(34.+4.(2;.^7.))(2;.^1.)(34.+4.(2;.^6.)))(21.$2>.(32.(3:.^1.)&2.)(21.$2>.(32.(3:.^4.)&2.)(21.$2>.(35.(30.=)(2;.^1.))(21.$2>.(3;.(2;.^5.)(30.=)(30.+1.)(2;.^4.))(21.$2>.(35.(33.(2;.^1.)(34.+4.(2;.^6.)))(30.(13.+2.+40.)))(21.$2>.(35.(33.(2;.^4.)(34.+4.(2;.^7.)))(30.(13.+2.+40.)))(21.$2>.(31.(2;.^9.)(33.(2;.^8.)(30.(3<.$3=.))))(21.$2>.(32.(3:.^8.)&4.)(21.$2>.(3;.(33.(2;.^1.)(34.+4.(2;.^6.)))(2;.^9.)(2;.^8.)(2;.^1.))(21.$2>.(3;.(33.(2;.^4.)(34.+4.(2;.^7.)))(2;.^9.)(2;.^8.)(2;.^4.))(21.$2>.(32.(3:.^:.)&1.)(21.$2>.(31.(30.=)(2;.^8.))(21.$2>.(31.(2;.^8.)(30.(3>.$3?.+1.)))(21.$2>.(31.(30.=)(2;.^:.))(21.$2>.(31.(2;.^:.)(30.(3>.$3?.+1.)))(24.$2>.)))))))))))))))))))))))))(21.(22.$36.$36.)(23.$36.$36.(2;.^2.)(33.(2;.^2.)(34.+4.(2;.^3.))))(21.(22.$36.$36.)(23.$36.$36.(33.(2;.^8.)(30.(3<.$3=.)))(2;.^8.))(24.(22.$36.$36.))))(21.(22.$4.$28.)(23.$4.$28.+5.^;.)(21.(22.$4.$28.)(23.$4.$28.+6.^<.)(21.(22.$4.$28.)(23.$4.$28.+7.^=.)(21.(22.$4.$28.)(23.$4.$28.+:.^>.)(21.(22.$4.$28.)(23.$4.$28.+;.^?.)(21.(22.$4.$28.)(23.$4.$28.+<.^10.)(21.(22.$4.$28.)(23.$4.$28.+=.^11.)(21.(22.$4.$28.)(23.$4.$28.+>.^12.)(21.(22.$4.$28.)(23.$4.$28.+?.^13.)(21.(22.$4.$28.)(23.$4.$28.+10.^14.)(21.(22.$4.$28.)(23.$4.$28.+11.^15.)(21.(22.$4.$28.)(23.$4.$28.+1<.^16.)(21.(22.$4.$28.)(23.$4.$28.+1=.^17.)(21.(22.$4.$28.)(23.$4.$28.+1>.^18.)(21.(22.$4.$28.)(23.$4.$28.+1?.^19.)(24.(22.$4.$28.)))))))))))))))))(21.$29.(2:.(2;.^1.)&4.(2<.^3.)(2;.^6.)$2=.)(21.$29.(40.(2;.^9.)(2;.^8.))(24.$29.)))(24.$2>.))")
(* [comment removed for export] *).

Lemma sum_mlaWP_valid : forall AL GS k, summary_validG usegs AL GS (SUM_mlaWP k).
Proof.
  intros AL GS k. unfold SUM_mlaWP, q, MPI_CORE_MLA_STACK. lx_sum_unfold.
  intros T p DL S SL NT NS SPu LO RA ts ss CS F fc m.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
  intros ALLCS _ MI GB R10 R11 R12 R13 R2 R1 ST [HT LT] [HS LS].
  intros PR1 PR2 PR3 PR4 PR5 PR6 PR7 PR8 PR9 PR10 PR11 PR12 PR13 PR14 PR15 PR16 PR17 PR18 PR19 PR20 PR21 PR22 PR23 PR24.
  lxp_pows.
  apply (evt_evtA_all usegs AL CS _ _ ALLCS).
  assert (U2 : bv_unsigned x2 = SPu) by (rewrite R2; apply lxp_uw64; assumption).
  assert (U1 : bv_unsigned x1 = RA) by (rewrite R1; apply lxp_uw64; assumption).
  set (i := (p - T) / 4). assert (Ep : p = T + 4 * i) by (subst i; lia).
  rewrite Ep in R10.
  pose proof (mla_window usegs U_MPI_CORE_MLA U_mpi_core_mla_spec) as SP. unfold MPI_CORE_MLA_STACK in SP.
  eapply evt_cut.
  { eapply (SP x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m T i DL S SL LO ts ss);
      rewrite ?U2, ?U1; first [eassumption | lia | idtac]. }
  clear SP. cbv beta. intros ms' POST. unfold mla_window_post, MPI_CORE_MLA_STACK in POST.
  destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & ts' & -> & MU & WM & MI' & HT' & LEN' & FI & SK & ST').
  apply evt_done. rewrite U2 in MU, ST'. rewrite <- Ep in MU.
  lx_sum_post.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SUM_ctcpyWP (k : nat) : summary := ltac2:(CDefT.buildp (gd_tbl_LxP_SumsArr ()) "(26.$41.$27.#9.#?.#0.(21.(22.$4.$28.)(23.$4.$28.+;.^1.)(21.(22.$4.$28.)(23.$4.$28.+<.^3.)(21.(22.$4.$28.)(23.$4.$28.+=.^4.)(21.(22.$4.$28.)(23.$4.$28.+>.^5.)(21.(22.$4.$28.)(23.$4.$28.+2.^6.)(24.(22.$4.$28.)))))))(21.(22.$28.$5.)(23.$28.$5.^2.O1.)(24.(22.$28.$5.)))(1>.$28.)(21.$29.(2:.(2;.^1.)&4.(2<.^1.)(2;.^8.)$2=.)(21.$29.(2:.(2;.^2.)&4.(2<.^2.)(2;.^9.)$27.)(24.$29.)))(38.(22.$28.$28.)(23.$28.$28.^7.^6.))(24.(22.(22.$28.$28.)$28.))(24.$29.)(21.$2>.(2?.(2;.^4.)(30.=))(21.$2>.(2?.(2;.^5.)(34.+4.(2;.^8.)))(21.$2>.(31.(30.=)(2;.^5.))(21.$2>.(31.(2;.^5.)(30.+9<40.))(21.$2>.(31.(2;.^2.)(2;.^3.))(21.$2>.(32.(33.(2;.^3.)(34.-1.(2;.^2.)))&2.)(21.$2>.(31.(33.(2;.^3.)(2;.^5.))(33.(2;.^2.)(34.+4.(2;.^9.))))(21.$2>.(39.(2;.^2.)(34.+4.(2;.^9.))(2;.^1.)(34.+4.(2;.^8.)))(21.$2>.(35.(30.=)(2;.^1.))(21.$2>.(35.(30.=)(2;.^2.))(21.$2>.(35.(33.(2;.^1.)(34.+4.(2;.^8.)))(30.(13.+2.+40.)))(21.$2>.(35.(33.(2;.^2.)(34.+4.(2;.^9.)))(30.(13.+2.+40.)))(21.$2>.(31.(2;.^7.)(33.(2;.^6.)(30.(3<.$42.))))(21.$2>.(32.(3:.^6.)&4.)(21.$2>.(3;.(33.(2;.^1.)(34.+4.(2;.^8.)))(2;.^7.)(2;.^6.)(2;.^1.))(21.$2>.(3;.(33.(2;.^2.)(34.+4.(2;.^9.)))(2;.^7.)(2;.^6.)(2;.^2.))(21.$2>.(31.(30.=)(2;.^6.))(21.$2>.(31.(2;.^6.)(30.(3>.$3?.+1.)))(24.$2>.)))))))))))))))))))(21.(22.$36.$36.)(23.$36.$36.(2;.^1.)(33.(2;.^1.)(2;.^5.)))(21.(22.$36.$36.)(23.$36.$36.(33.(2;.^6.)(30.(3<.$42.)))(2;.^6.))(24.(22.$36.$36.))))(21.(22.$4.$28.)(23.$4.$28.+5.^:.)(21.(22.$4.$28.)(23.$4.$28.+6.^;.)(21.(22.$4.$28.)(23.$4.$28.+7.^<.)(21.(22.$4.$28.)(23.$4.$28.+:.^=.)(21.(22.$4.$28.)(23.$4.$28.+;.^>.)(21.(22.$4.$28.)(23.$4.$28.+<.^?.)(21.(22.$4.$28.)(23.$4.$28.+=.^10.)(21.(22.$4.$28.)(23.$4.$28.+>.^11.)(21.(22.$4.$28.)(23.$4.$28.+?.^12.)(21.(22.$4.$28.)(23.$4.$28.+10.^13.)(21.(22.$4.$28.)(23.$4.$28.+11.^14.)(21.(22.$4.$28.)(23.$4.$28.+1<.^15.)(21.(22.$4.$28.)(23.$4.$28.+1=.^16.)(21.(22.$4.$28.)(23.$4.$28.+1>.^17.)(21.(22.$4.$28.)(23.$4.$28.+1?.^18.)(24.(22.$4.$28.)))))))))))))))))(21.$29.(2:.(2;.^1.)&4.(2<.^3.)(2;.^8.)$2=.)(21.$29.(40.(2;.^7.)(2;.^6.))(24.$29.)))(24.$2>.))")
(* [comment removed for export] *).

Lemma sum_ctcpyWP_valid : forall AL GS k, summary_validG usegs AL GS (SUM_ctcpyWP k).
Proof.
  intros AL GS k. unfold SUM_ctcpyWP, q, CT_MEMCPY_IF_STACK. lx_sum_unfold.
  intros D T p s2 n SPu LO ND NT ds ts CS F fc m.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
  intros ALLCS _ MI GB R11 R12 R13 R14 R2 ST [HD LD] [HT LT].
  intros PR1 PR2 PR3 PR4 PR5 PR6 PR7 PR8 PR9 PR10 PR11 PR12 PR13 PR14 PR15 PR16 PR17 PR18.
  lxp_pows.
  apply (evt_evtA_all usegs AL CS _ _ ALLCS).
  assert (U2 : bv_unsigned x2 = SPu) by (rewrite R2; apply lxp_uw64; assumption).
  set (i := (p - T) / 4). assert (Ep : p = T + 4 * i) by (subst i; lia).
  assert (HS : bytes_at usegs m p (u32s (skipn (Z.to_nat i) ts))).
  { replace p with (T + 4 * Z.of_nat (Z.to_nat i)) by lia. apply lxp_u32ro_skipn; [exact HT | lia]. }
  pose proof (u8arr_of_u32arr _ _ _ _ HD) as HD8.
  subst s2.
  pose proof U_ct_memcpy_if_spec as SP. unfold ct_memcpy_if_stmt, CT_MEMCPY_IF_STACK in SP.
  eapply evt_cut.
  { eapply (SP x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m
               D p 0 n LO (u32s ds) (u32s (skipn (Z.to_nat i) ts)));
      rewrite ?U2, ?u32s_length, ?skipn_length; first [eassumption | lia | idtac]. }
  clear SP. cbv beta. intros ms' POST. unfold ct_memcpy_if_post, CT_MEMCPY_IF_STACK in POST.
  destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & dbs' & -> & MU & WM & MI' & HD' & LEN' & SK & ST').
  apply evt_done. rewrite U2 in MU, ST'.
  rewrite u32s_length in LEN'.
  destruct (u32arr_of_u8arr usegs _ _ _ (length ds) HD' ltac:(lia)) as (ds' & HDD & LDD).
  lx_sum_post.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SUMSARR : list summary := [SUM_memsetWP 0; SUM_mlaWP 0; SUM_ctcpyWP 0].
Lemma sumsarr_ok : forall GS AL, Forall (summary_okG usegs AL GS) SUMSARR.
Proof.
  intros GS AL. unfold SUMSARR. repeat constructor; apply apply_summary_soundG;
    auto using sum_memsetWP_valid, sum_mlaWP_valid, sum_ctcpyWP_valid.
Qed.
