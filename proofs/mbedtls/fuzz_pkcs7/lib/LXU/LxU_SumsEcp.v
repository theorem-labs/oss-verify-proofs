(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Arr MpiCoreAux MpiWalkAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_mpi_core_mla U_mpi_core_add U_mpi_core_mul U_ecp_red.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Export LxSum LxSoundSum.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr LxDec LxMem LxStep LxRun LxDenot LxSoundRun LxTac LxDex.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXU Require Export LxU_SumsArr.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac lxp_pows :=
  try change (2 ^ Z.of_N 1)%Z with 2%Z in *; try change (2 ^ Z.of_N 2)%Z with 4%Z in *;
  try change (2 ^ Z.of_N 3)%Z with 8%Z in *; try change (2 ^ Z.of_N 4)%Z with 16%Z in *.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_LxP_SumsEcp () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.LX.LxSum.SUM"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_core_mla.U_MPI_CORE_MLA"; "Corelib.Init.Datatypes.false"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Numbers.BinNums.positive"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.mfact"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.MArr"; "RocqVerifyHarness.AgentSubmission.LXU.LxU_SumsArr.q"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.LBase"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.pfact"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FEq"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.EAdd"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.EMulC"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FLe"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.ELit"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FAl"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.EZv"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FLt"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.opp"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_core_mla.MPI_CORE_MLA_STACK"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FOr2"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.two64"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.expr"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.MStk"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_core_add.U_MPI_CORE_ADD"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_core_add.MPI_CORE_ADD_STACK"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FSep"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_core_mul.U_MPI_CORE_MUL"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_core_mul.MPI_CORE_MUL_STACK"].


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SUM_mlaHiLoP : summary := ltac2:(CDefT.buildp (gd_tbl_LxP_SumsEcp ()) "(0.$1.$2.#8.#?.#0.(3.(4.$5.$6.)(7.$5.$6.+:.^1.)(3.(4.$5.$6.)(7.$5.$6.+;.^2.)(3.(4.$5.$6.)(7.$5.$6.+<.^3.)(3.(4.$5.$6.)(7.$5.$6.+=.^4.)(3.(4.$5.$6.)(7.$5.$6.+2.^6.)(3.(4.$5.$6.)(7.$5.$6.+1.^8.)(8.(4.$5.$6.))))))))(9.$6.)(3.$:.(;.(<.^1.)&4.(=.^1.)(<.^5.)$>.)(8.$:.))(?.(4.$6.$6.)(7.$6.$6.^7.^6.))(8.(4.(4.$6.$6.)$6.))(8.$:.)(3.$10.(11.(<.^3.)(12.(<.^1.)(13.+4.(<.^2.))))(3.$10.(14.(15.+1.)(<.^2.))(3.$10.(14.(<.^2.)(15.+2710.))(3.$10.(14.(15.=)(<.^4.))(3.$10.(14.(<.^4.)(15.+2710.))(3.$10.(14.(12.(<.^2.)(<.^4.))(<.^5.))(3.$10.(16.(17.^1.)&2.)(3.$10.(18.(15.=)(<.^1.))(3.$10.(18.(12.(<.^1.)(13.+4.(<.^5.)))(15.(19.+2.+40.)))(3.$10.(14.(<.^7.)(12.(<.^6.)(15.(1:.$1;.))))(3.$10.(16.(17.^6.)&4.)(3.$10.(1<.(12.(<.^1.)(13.+4.(<.^5.)))(<.^7.)(<.^6.)(<.^1.))(3.$10.(16.(17.^8.)&1.)(3.$10.(14.(15.=)(<.^6.))(3.$10.(14.(<.^6.)(15.(1=.$1>.+1.)))(3.$10.(14.(15.=)(<.^8.))(3.$10.(14.(<.^8.)(15.(1=.$1>.+1.)))(8.$10.))))))))))))))))))(3.(4.$1?.$1?.)(7.$1?.$1?.(<.^1.)(12.(<.^1.)(13.+4.(<.^2.))))(3.(4.$1?.$1?.)(7.$1?.$1?.(12.(<.^6.)(15.(1:.$1;.)))(<.^6.))(8.(4.$1?.$1?.))))(3.(4.$5.$6.)(7.$5.$6.+5.^9.)(3.(4.$5.$6.)(7.$5.$6.+6.^:.)(3.(4.$5.$6.)(7.$5.$6.+7.^;.)(3.(4.$5.$6.)(7.$5.$6.+:.^<.)(3.(4.$5.$6.)(7.$5.$6.+;.^=.)(3.(4.$5.$6.)(7.$5.$6.+<.^>.)(3.(4.$5.$6.)(7.$5.$6.+=.^?.)(3.(4.$5.$6.)(7.$5.$6.+>.^10.)(3.(4.$5.$6.)(7.$5.$6.+?.^11.)(3.(4.$5.$6.)(7.$5.$6.+10.^12.)(3.(4.$5.$6.)(7.$5.$6.+11.^13.)(3.(4.$5.$6.)(7.$5.$6.+1<.^14.)(3.(4.$5.$6.)(7.$5.$6.+1=.^15.)(3.(4.$5.$6.)(7.$5.$6.+1>.^16.)(3.(4.$5.$6.)(7.$5.$6.+1?.^17.)(8.(4.$5.$6.)))))))))))))))))(3.$:.(;.(<.^1.)&4.(=.^2.)(<.^5.)$>.)(3.$:.(20.(<.^7.)(<.^6.))(8.$:.)))(8.$10.))")
(* [comment removed for export] *).

Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L18576355811.77L2834776497.77 L42786954347.77L45542131645.77L55973127642.99L7753404694.77 00000Q01;01]02B02l03US1X1W3SPu2RA2ws3PR23PR34PR144PR16S1X1W2SL2NX3SPu2RA2ws2LX3PR63PR84PR144PR16S1X2SL3SPu2RA2ws3PR43PR54PR144PR16S1X2NX3SPu2RA2ws2LX3PR83PR94PR144PR16S1X2NX3SPu2RA2ws2LX3PR84PR144PR163ws'4LEN'S1X2NX3SPu2LO2RA2ws2LX3PR84PR124PR144PR16". (* [comment removed for export] *)
Lemma sum_mlaHiLoP_valid : forall AL, summary_valid usegs AL SUM_mlaHiLoP.
Proof.
  intros AL. unfold SUM_mlaHiLoP, q, MPI_CORE_MLA_STACK. lx_sum_unfold.
  intros X W S SL NX SPu LO RA ws CS F fc m.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
  intros ALLCS _ MI R10 R11 R12 R13 R2 R1 ST [HX LX].
  intros PR1 PR2 PR3 PR4 PR5 PR6 PR7 PR8 PR9 PR10 PR11 PR12 PR13 PR14 PR15 PR16 PR17.
  lxp_pows.
  apply (evt_evtA_all usegs AL CS _ _ ALLCS).
  assert (U2 : bv_unsigned x2 = SPu) by (rewrite R2; apply lxp_uw64; assumption).
  assert (U1 : bv_unsigned x1 = RA) by (rewrite R1; apply lxp_uw64; assumption).
  subst S.
  pose proof (mla_hi_into_lo usegs _ U_mpi_core_mla_spec) as SP. unfold MPI_CORE_MLA_STACK in SP.
  eapply evt_cut.
  { eapply (SP x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m X ws W SL LO);
      rewrite ?U2, ?U1; first [eassumption | lia | idtac]. }
  clear SP. cbv beta. intros ms' POST. unfold arrcall_post, MPI_CORE_MLA_STACK in POST.
  destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & ws' & -> & MU & WM & MI' & HX' & LEN' & ST').
  apply evt_done. rewrite U2 in MU, ST'.
  lx_sum_post.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SUM_coreaddHiLoP : summary := ltac2:(CDefT.buildp (gd_tbl_LxP_SumsEcp ()) "(0.$21.$2.#6.#?.#0.(3.(4.$5.$6.)(7.$5.$6.+:.^1.)(3.(4.$5.$6.)(7.$5.$6.+;.^1.)(3.(4.$5.$6.)(7.$5.$6.+<.^2.)(3.(4.$5.$6.)(7.$5.$6.+=.^3.)(3.(4.$5.$6.)(7.$5.$6.+2.^5.)(8.(4.$5.$6.)))))))(9.$6.)(3.$:.(;.(<.^1.)&4.(=.^1.)(<.^4.)$>.)(8.$:.))(?.(4.$6.$6.)(7.$6.$6.^6.^5.))(8.(4.(4.$6.$6.)$6.))(8.$:.)(3.$10.(16.(12.(<.^2.)(13.-1.(<.^1.)))&2.)(3.$10.(14.(15.=)(<.^3.))(3.$10.(14.(<.^3.)(15.+2710.))(3.$10.(14.(12.(<.^1.)(13.+4.(<.^3.)))(<.^2.))(3.$10.(14.(12.(<.^2.)(13.+4.(<.^3.)))(12.(<.^1.)(13.+4.(<.^4.))))(3.$10.(16.(17.^1.)&2.)(3.$10.(18.(15.=)(<.^1.))(3.$10.(14.(<.^6.)(12.(<.^5.)(15.(1:.$22.))))(3.$10.(16.(17.^5.)&4.)(3.$10.(1<.(12.(<.^1.)(13.+4.(<.^4.)))(<.^6.)(<.^5.)(<.^1.))(3.$10.(14.(15.=)(<.^5.))(3.$10.(14.(<.^5.)(15.(1=.$1>.+1.)))(8.$10.)))))))))))))(3.(4.$1?.$1?.)(7.$1?.$1?.(<.^1.)(12.(<.^1.)(13.+4.(<.^3.))))(3.(4.$1?.$1?.)(7.$1?.$1?.(12.(<.^5.)(15.(1:.$22.)))(<.^5.))(8.(4.$1?.$1?.))))(3.(4.$5.$6.)(7.$5.$6.+5.^7.)(3.(4.$5.$6.)(7.$5.$6.+6.^8.)(3.(4.$5.$6.)(7.$5.$6.+7.^9.)(3.(4.$5.$6.)(7.$5.$6.+:.^:.)(3.(4.$5.$6.)(7.$5.$6.+;.^;.)(3.(4.$5.$6.)(7.$5.$6.+<.^<.)(3.(4.$5.$6.)(7.$5.$6.+=.^=.)(3.(4.$5.$6.)(7.$5.$6.+>.^>.)(3.(4.$5.$6.)(7.$5.$6.+?.^?.)(3.(4.$5.$6.)(7.$5.$6.+10.^10.)(3.(4.$5.$6.)(7.$5.$6.+11.^11.)(3.(4.$5.$6.)(7.$5.$6.+1<.^12.)(3.(4.$5.$6.)(7.$5.$6.+1=.^13.)(3.(4.$5.$6.)(7.$5.$6.+1>.^14.)(3.(4.$5.$6.)(7.$5.$6.+1?.^15.)(8.(4.$5.$6.)))))))))))))))))(3.$:.(;.(<.^1.)&4.(=.^2.)(<.^4.)$>.)(3.$:.(20.(<.^6.)(<.^5.))(8.$:.)))(8.$10.))")
(* [comment removed for export] *).

Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L29544356464.72L47266574087.72L55973127642.94L5837511117.69 L7753404694.72 00000T01:01c02F038S1X1S1n3SPu2ws1W3PR23PR43PR74PR112ESS1X1S1n2NX3SPu2ws1W2LX3PR53PR74PR112ESS1X1S2NX3SPu2ws1W2LX3PR74PR112ES3ws'4LEN'S1X1S1n3SPu2ws3PR13PR23PR43PR74PR11S1X1S1n2NX3SPu2LO2ws1W2LX3PR23PR43PR74PR104PR112ES". (* [comment removed for export] *)
Lemma sum_coreaddHiLoP_valid : forall AL, summary_valid usegs AL SUM_coreaddHiLoP.
Proof.
  intros AL. unfold SUM_coreaddHiLoP, q, MPI_CORE_ADD_STACK. lx_sum_unfold.
  intros X S n NX SPu LO ws CS F fc m.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
  intros ALLCS _ MI R10 R11 R12 R13 R2 ST [HX LX].
  intros PR1 PR2 PR3 PR4 PR5 PR6 PR7 PR8 PR9 PR10 PR11 PR12.
  lxp_pows.
  apply (evt_evtA_all usegs AL CS _ _ ALLCS).
  assert (U2 : bv_unsigned x2 = SPu) by (rewrite R2; apply lxp_uw64; assumption).
  set (W := (S - X) / 4). assert (ES : S = X + 4 * W) by (subst W; lia). rewrite ES in R12.
  pose proof (core_add_hi_into_lo usegs _ U_mpi_core_add_spec) as SP. unfold MPI_CORE_ADD_STACK in SP.
  eapply evt_cut.
  { eapply (SP x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m X ws W n LO);
      rewrite ?U2; first [eassumption | lia | idtac]. }
  clear SP. cbv beta. intros ms' POST. unfold arrcall_post, MPI_CORE_ADD_STACK in POST.
  destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & ws' & -> & MU & WM & MI' & HX' & LEN' & ST').
  apply evt_done. rewrite U2 in MU, ST'.
  lx_sum_post.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SUM_coreaddXXBP : summary := ltac2:(CDefT.buildp (gd_tbl_LxP_SumsEcp ()) "(0.$21.$2.#7.#?.#0.(3.(4.$5.$6.)(7.$5.$6.+:.^1.)(3.(4.$5.$6.)(7.$5.$6.+;.^1.)(3.(4.$5.$6.)(7.$5.$6.+<.^2.)(3.(4.$5.$6.)(7.$5.$6.+=.^3.)(3.(4.$5.$6.)(7.$5.$6.+2.^6.)(8.(4.$5.$6.)))))))(9.$6.)(3.$:.(;.(<.^1.)&4.(=.^1.)(<.^4.)$>.)(3.$:.(;.(<.^2.)&4.(=.^2.)(<.^5.)$2.)(8.$:.)))(?.(4.$6.$6.)(7.$6.$6.^7.^6.))(8.(4.(4.$6.$6.)$6.))(8.$:.)(3.$10.(14.(15.=)(<.^3.))(3.$10.(14.(<.^3.)(15.+2710.))(3.$10.(14.(<.^3.)(<.^4.))(3.$10.(14.(<.^3.)(<.^5.))(3.$10.(23.(<.^2.)(13.+4.(<.^5.))(<.^1.)(13.+4.(<.^4.)))(3.$10.(16.(17.^1.)&2.)(3.$10.(16.(17.^2.)&2.)(3.$10.(18.(15.=)(<.^1.))(3.$10.(18.(15.=)(<.^2.))(3.$10.(14.(<.^7.)(12.(<.^6.)(15.(1:.$22.))))(3.$10.(16.(17.^6.)&4.)(3.$10.(1<.(12.(<.^1.)(13.+4.(<.^4.)))(<.^7.)(<.^6.)(<.^1.))(3.$10.(1<.(12.(<.^2.)(13.+4.(<.^5.)))(<.^7.)(<.^6.)(<.^2.))(3.$10.(14.(15.=)(<.^6.))(3.$10.(14.(<.^6.)(15.(1=.$1>.+1.)))(8.$10.))))))))))))))))(3.(4.$1?.$1?.)(7.$1?.$1?.(<.^1.)(12.(<.^1.)(13.+4.(<.^3.))))(3.(4.$1?.$1?.)(7.$1?.$1?.(12.(<.^6.)(15.(1:.$22.)))(<.^6.))(8.(4.$1?.$1?.))))(3.(4.$5.$6.)(7.$5.$6.+:.^8.)(3.(4.$5.$6.)(7.$5.$6.+5.^9.)(3.(4.$5.$6.)(7.$5.$6.+6.^:.)(3.(4.$5.$6.)(7.$5.$6.+7.^;.)(3.(4.$5.$6.)(7.$5.$6.+;.^<.)(3.(4.$5.$6.)(7.$5.$6.+<.^=.)(3.(4.$5.$6.)(7.$5.$6.+=.^>.)(3.(4.$5.$6.)(7.$5.$6.+>.^?.)(3.(4.$5.$6.)(7.$5.$6.+?.^10.)(3.(4.$5.$6.)(7.$5.$6.+10.^11.)(3.(4.$5.$6.)(7.$5.$6.+11.^12.)(3.(4.$5.$6.)(7.$5.$6.+1<.^13.)(3.(4.$5.$6.)(7.$5.$6.+1=.^14.)(3.(4.$5.$6.)(7.$5.$6.+1>.^15.)(3.(4.$5.$6.)(7.$5.$6.+1?.^16.)(8.(4.$5.$6.)))))))))))))))))(3.$:.(;.(<.^1.)&4.(=.^3.)(<.^4.)$>.)(3.$:.(20.(<.^7.)(<.^6.))(8.$:.)))(3.$10.(14.(15.=)(<.^8.))(3.$10.(14.(<.^8.)(15.+1.))(8.$10.))))")
(* [comment removed for export] *).

Local Ltac2 Set LiaOrc.tbl := fun () => "00;0@L11228561286.77 L1282180577.77  L230325526.103  L23346143008.103L379047126.77   L38481954273.77 L50891006907.102L60448205867.77 L68388506558.102L68390507378.103L7753404694.77  00000d01L02902]03V04>04b05@05d06H07AS1X1B2NX2NB3SPu2xs2zs2LX2LB3PR53PR63PR73PR83PR94PR14S1X1B1n2NX3SPu2xs2zs2LX3PR33PR83PR94PR14S1X1B1n2NX3SPu2xs2zs2LX3PR83PR94PR143xs'4LEN'S1X1B1n3SPu2xs2zs4PR141c3xs'2Hc4LEN'S1X1B2NX2NB3SPu2LO2xs2zs2LX2LB3PR73PR83PR94PR114PR134PR14S1X1B1n2NB3SPu2xs2zs2LB3PR43PR83PR94PR14S1X1B1n3SPu2xs2zs4PR141c3xs'2Hc4LEN'S1X1B1n3SPu2xs2zs3PR13PR24PR14S1X1B1n3SPu2xs2zs4PR141c3xs'2Hc4LEN'S1X1B1n3SPu2xs2zs4PR141c3xs'2Hc4LEN'S1X1B2NX2NB3SPu2LO2xs2zs2LX2LB3PR63PR83PR94PR114PR124PR14". (* [comment removed for export] *)
Lemma sum_coreaddXXBP_valid : forall AL, summary_valid usegs AL SUM_coreaddXXBP.
Proof.
  intros AL. unfold SUM_coreaddXXBP, q, MPI_CORE_ADD_STACK. lx_sum_unfold.
  intros X B n NX NB SPu LO xs zs CS F fc m.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
  intros ALLCS _ MI R10 R11 R12 R13 R2 ST [HX LX] [HB LB].
  intros PR1 PR2 PR3 PR4 PR5 PR6 PR7 PR8 PR9 PR10 PR11 PR12 PR13 PR14 PR15.
  lxp_pows.
  apply (evt_evtA_all usegs AL CS _ _ ALLCS).
  assert (U2 : bv_unsigned x2 = SPu) by (rewrite R2; apply lxp_uw64; assumption).
  pose proof U_mpi_core_add_spec as SP. unfold mpi_core_add_stmt, MPI_CORE_ADD_STACK in SP.
  eapply evt_cut.
  { eapply (SP x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m X X B n LO xs xs zs);
      rewrite ?U2; first [eassumption | apply u32arr_ro; eassumption | left; split; reflexivity | lia | idtac]. }
  clear SP. cbv beta. intros ms' POST. unfold mpi_core_add_post, MPI_CORE_ADD_STACK in POST.
  destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & c & xs' & -> & MU & WM & MI' & -> & Hc & HX' & LEN' & SK & VAL & ST').
  apply evt_done. rewrite U2 in MU, ST'.
  pose proof (lxp_uw64 c ltac:(lia) ltac:(unfold two64; lia)) as Uc.
  lx_sum_post.
  all: rewrite ?Uc; lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SUM_coremulP : summary := ltac2:(CDefT.buildp (gd_tbl_LxP_SumsEcp ()) "(0.$24.$2.#;.#?.#0.(3.(4.$5.$6.)(7.$5.$6.+:.^1.)(3.(4.$5.$6.)(7.$5.$6.+;.^2.)(3.(4.$5.$6.)(7.$5.$6.+<.^3.)(3.(4.$5.$6.)(7.$5.$6.+=.^4.)(3.(4.$5.$6.)(7.$5.$6.+>.^5.)(3.(4.$5.$6.)(7.$5.$6.+2.^9.)(3.(4.$5.$6.)(7.$5.$6.+1.^;.)(8.(4.$5.$6.)))))))))(9.$6.)(3.$:.(;.(<.^1.)&4.(=.^1.)(<.^6.)$>.)(3.$:.(;.(<.^2.)&4.(=.^2.)(<.^7.)$2.)(3.$:.(;.(<.^4.)&4.(=.^3.)(<.^8.)$2.)(8.$:.))))(?.(4.$6.$6.)(7.$6.$6.^:.^9.))(8.(4.(4.$6.$6.)$6.))(8.$:.)(3.$10.(14.(15.=)(<.^3.))(3.$10.(14.(15.=)(<.^5.))(3.$10.(14.(12.(<.^3.)(<.^5.))(15.+2710.))(3.$10.(14.(12.(<.^3.)(<.^5.))(<.^6.))(3.$10.(14.(<.^3.)(<.^7.))(3.$10.(14.(<.^5.)(<.^8.))(3.$10.(23.(<.^2.)(13.+4.(<.^7.))(<.^1.)(13.+4.(<.^6.)))(3.$10.(23.(<.^4.)(13.+4.(<.^8.))(<.^1.)(13.+4.(<.^6.)))(3.$10.(16.(17.^1.)&2.)(3.$10.(16.(17.^2.)&2.)(3.$10.(16.(17.^4.)&2.)(3.$10.(18.(15.=)(<.^1.))(3.$10.(1<.(<.^3.)(15.=)(15.+1.)(<.^2.))(3.$10.(1<.(<.^5.)(15.=)(15.+1.)(<.^4.))(3.$10.(18.(12.(<.^1.)(13.+4.(<.^6.)))(15.(19.+2.+40.)))(3.$10.(18.(12.(<.^2.)(13.+4.(<.^7.)))(15.(19.+2.+40.)))(3.$10.(18.(12.(<.^4.)(13.+4.(<.^8.)))(15.(19.+2.+40.)))(3.$10.(14.(<.^:.)(12.(<.^9.)(15.(1:.$25.))))(3.$10.(16.(17.^9.)&4.)(3.$10.(1<.(12.(<.^1.)(13.+4.(<.^6.)))(<.^:.)(<.^9.)(<.^1.))(3.$10.(1<.(12.(<.^2.)(13.+4.(<.^7.)))(<.^:.)(<.^9.)(<.^2.))(3.$10.(1<.(12.(<.^4.)(13.+4.(<.^8.)))(<.^:.)(<.^9.)(<.^4.))(3.$10.(16.(17.^;.)&1.)(3.$10.(14.(15.=)(<.^9.))(3.$10.(14.(<.^9.)(15.(1=.$1>.+1.)))(3.$10.(14.(15.=)(<.^;.))(3.$10.(14.(<.^;.)(15.(1=.$1>.+1.)))(8.$10.))))))))))))))))))))))))))))(3.(4.$1?.$1?.)(7.$1?.$1?.(<.^1.)(12.(<.^1.)(13.+4.(12.(<.^3.)(<.^5.)))))(3.(4.$1?.$1?.)(7.$1?.$1?.(12.(<.^9.)(15.(1:.$25.)))(<.^9.))(8.(4.$1?.$1?.))))(3.(4.$5.$6.)(7.$5.$6.+5.^<.)(3.(4.$5.$6.)(7.$5.$6.+6.^=.)(3.(4.$5.$6.)(7.$5.$6.+7.^>.)(3.(4.$5.$6.)(7.$5.$6.+:.^?.)(3.(4.$5.$6.)(7.$5.$6.+;.^10.)(3.(4.$5.$6.)(7.$5.$6.+<.^11.)(3.(4.$5.$6.)(7.$5.$6.+=.^12.)(3.(4.$5.$6.)(7.$5.$6.+>.^13.)(3.(4.$5.$6.)(7.$5.$6.+?.^14.)(3.(4.$5.$6.)(7.$5.$6.+10.^15.)(3.(4.$5.$6.)(7.$5.$6.+11.^16.)(3.(4.$5.$6.)(7.$5.$6.+1<.^17.)(3.(4.$5.$6.)(7.$5.$6.+1=.^18.)(3.(4.$5.$6.)(7.$5.$6.+1>.^19.)(3.(4.$5.$6.)(7.$5.$6.+1?.^1:.)(8.(4.$5.$6.)))))))))))))))))(3.$:.(;.(<.^1.)&4.(=.^4.)(<.^6.)$>.)(3.$:.(20.(<.^:.)(<.^9.))(8.$:.)))(8.$10.))")
(* [comment removed for export] *).

Local Ltac2 Set LiaOrc.tbl := fun () => "00>0?L11200866206.99L15028896074.99L15199003533.99L17017932370.99L1820788193.99 L18684245632.99L19743573473.99L228320730.122 L379047126.99  L45542131645.99L5198038747.99 L53147742195.99L55672721719.99L7753404694.99 00000a01N02;03103d05Z06M07B08b09S0:D0;H0<L0>1S1X1A1B2NA3SPu2RA2xs2ys2zs2LA4PR124PR164PR244PR26S1X1A2an1B3SPu2RA2xs2ys2zs3PR14PR134PR244PR26S1X1A1B2bn3SPu2RA2xs2ys2zs3PR24PR144PR244PR26S1X1A2an1B2bn2NX3SPu2RA2xs2ys2zs2LX3PR44PR124PR244PR26S1X1A1B2bn2NB3SPu2RA2xs2ys2zs2LB3PR64PR124PR244PR26S1X1A2an1B2bn2NX2NA2NB3SPu2LO2RA2xs2ys2zs2LX2LA2LB3PR13PR23PR43PR63PR73PR83PR94PR104PR114PR124PR194PR204PR214PR244PR26S1X1A2an1B2NA3SPu2RA2xs2ys2zs2LA3PR54PR124PR244PR26S1X1A1B2NX3SPu2RA2xs2ys2zs2LX4PR124PR244PR263xs'4LEN'S1X1A1B2NX2NA2NB3SPu2LO2RA2xs2ys2zs2LX2LA2LB3PR73PR83PR94PR104PR114PR124PR194PR204PR224PR244PR26S1X1A1B2NX3SPu2RA2xs2ys2zs2LX4PR124PR154PR244PR26S1X1A1B2NB3SPu2RA2xs2ys2zs2LB4PR124PR174PR244PR26S1X1A1B2NX2NA3SPu2RA2xs2ys2zs2LX2LA3PR73PR94PR104PR114PR124PR244PR26S1X1A1B2NX2NB3SPu2RA2xs2ys2zs2LX2LB3PR83PR94PR104PR114PR124PR244PR26S1X1A1B2NX2NA2NB3SPu2LO2RA2xs2ys2zs2LX2LA2LB3PR73PR83PR94PR104PR114PR124PR194PR204PR214PR224PR244PR26". (* [comment removed for export] *)
Lemma sum_coremulP_valid : forall AL, summary_valid usegs AL SUM_coremulP.
Proof.
  intros AL. unfold SUM_coremulP, q, MPI_CORE_MUL_STACK. lx_sum_unfold.
  intros X A an B bn NX NA NB SPu LO RA xs ys zs CS F fc m.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
  intros ALLCS _ MI R10 R11 R12 R13 R14 R2 R1 ST [HX LX] [HA LA] [HB LB].
  intros PR1 PR2 PR3 PR4 PR5 PR6 PR7 PR8 PR9 PR10 PR11 PR12 PR13 PR14 PR15 PR16 PR17 PR18 PR19 PR20 PR21 PR22 PR23 PR24 PR25 PR26 PR27.
  lxp_pows.
  apply (evt_evtA_all usegs AL CS _ _ ALLCS).
  assert (U2 : bv_unsigned x2 = SPu) by (rewrite R2; apply lxp_uw64; assumption).
  assert (U1 : bv_unsigned x1 = RA) by (rewrite R1; apply lxp_uw64; assumption).
  pose proof U_mpi_core_mul_spec as SP. unfold mpi_core_mul_stmt, MPI_CORE_MUL_STACK in SP.
  eapply evt_cut.
  { eapply (SP x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m X A an B bn LO xs ys zs);
      rewrite ?U2, ?U1; first [eassumption | lia | idtac]. }
  clear SP. cbv beta. intros ms' POST. unfold mpi_core_mul_post, MPI_CORE_MUL_STACK in POST.
  destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & xs' & -> & MU & WM & MI' & HX' & LEN' & SK & ST').
  apply evt_done. rewrite U2 in MU, ST'.
  lx_sum_post.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SUMSECP : list summary := [SUM_memsetWP 0; SUM_memsetWP 1; SUM_mlaHiLoP; SUM_coreaddHiLoP; SUM_coreaddXXBP; SUM_coremulP].
Lemma sumsecp_ok : forall GS AL, Forall (summary_okG usegs AL GS) SUMSECP.
Proof.
  intros GS AL. unfold SUMSECP. repeat constructor; apply apply_summary_soundG;
    first [ apply sum_memsetWP_valid
          | apply (summary_validG_ext usegs AL [] GS); [reflexivity|];
            first [apply sum_mlaHiLoP_valid | apply sum_coreaddHiLoP_valid | apply sum_coreaddXXBP_valid | apply sum_coremulP_valid] ].
Qed.
