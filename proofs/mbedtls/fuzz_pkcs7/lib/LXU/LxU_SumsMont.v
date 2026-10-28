(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Arr MpiCoreAux MpiWalkAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_mpi_core_montmul.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Export LxSum LxSoundSum.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr LxDec LxMem LxStep LxRun LxDenot LxSoundRun LxTac LxDex.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_LxP_SumsMont () : Init.string Init.list := ["Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.pfact"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FLe"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.ELit"; "q"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.EAdd"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.EMulC"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FSep"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FAl"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.EZv"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FLt"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.opp"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_core_montmul.MPI_CORE_MONTMUL_STACK"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FOr2"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.two64"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Numbers.BinNums.positive"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.LX.LxSum.SUM"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_core_montmul.U_MPI_CORE_MONTMUL"; "Corelib.Init.Datatypes.false"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.mfact"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.MArr"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.LBase"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Datatypes.Some"; "montmul_pre"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.expr"; "montmul_clob"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.MStk"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.MRw"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.cellx"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.XZ"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FEq"].


Definition q (i : positive) : expr := EZv i.
Notation "a .+ b" := (EAdd a b) (at level 50, left associativity).
Local Ltac lxp_pows :=
  try change (2 ^ Z.of_N 1)%Z with 2%Z in *; try change (2 ^ Z.of_N 2)%Z with 4%Z in *;
  try change (2 ^ Z.of_N 3)%Z with 8%Z in *; try change (2 ^ Z.of_N 4)%Z with 16%Z in *.
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L38559550480.3000007S1z1A1B". (* [comment removed for export] *)
Lemma lxp_uw64 : forall z, 0 <= z -> z <= two64 - 1 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z A B. apply unsigned_lit. unfold two64 in B. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition montmul_pre : list pfact := ltac2:(CDefT.buildp (gd_tbl_LxP_SumsMont ()) "(0.$1.(2.(3.+1.)(4.^6.))(0.$1.(2.(4.^6.)(3.+1387.))(0.$1.(2.(3.+1.)(4.^4.))(0.$1.(2.(4.^4.)(3.+2710.))(0.$1.(2.(4.^6.)(4.^8.))(0.$1.(2.(4.^6.)(4.^9.))(0.$1.(2.(4.^4.)(4.^:.))(0.$1.(2.(4.^6.)(4.^;.))(0.$1.(2.(5.(6.+2.(4.^6.))(3.+1.))(4.^<.))(0.$1.(7.(4.^1.)(6.+4.(4.^8.))(4.^7.)(6.+4.(4.^<.)))(0.$1.(7.(4.^2.)(6.+4.(4.^9.))(4.^7.)(6.+4.(4.^<.)))(0.$1.(7.(4.^3.)(6.+4.(4.^:.))(4.^7.)(6.+4.(4.^<.)))(0.$1.(7.(4.^5.)(6.+4.(4.^;.))(4.^7.)(6.+4.(4.^<.)))(0.$1.(7.(4.^5.)(6.+4.(4.^;.))(4.^1.)(6.+4.(4.^8.)))(0.$1.(8.(9.^1.)&2.)(0.$1.(8.(9.^2.)&2.)(0.$1.(8.(9.^3.)&2.)(0.$1.(8.(9.^5.)&2.)(0.$1.(8.(9.^7.)&2.)(0.$1.(:.(3.=)(4.^1.))(0.$1.(:.(3.=)(4.^2.))(0.$1.(:.(3.=)(4.^3.))(0.$1.(:.(3.=)(4.^5.))(0.$1.(:.(3.=)(4.^7.))(0.$1.(:.(5.(4.^1.)(6.+4.(4.^8.)))(3.(;.+2.+40.)))(0.$1.(:.(5.(4.^2.)(6.+4.(4.^9.)))(3.(;.+2.+40.)))(0.$1.(:.(5.(4.^3.)(6.+4.(4.^:.)))(3.(;.+2.+40.)))(0.$1.(:.(5.(4.^5.)(6.+4.(4.^;.)))(3.(;.+2.+40.)))(0.$1.(:.(5.(4.^7.)(6.+4.(4.^<.)))(3.(;.+2.+40.)))(0.$1.(2.(4.^>.)(5.(4.^=.)(3.(<.$=.))))(0.$1.(8.(9.^=.)&4.)(0.$1.(>.(5.(4.^1.)(6.+4.(4.^8.)))(4.^>.)(4.^=.)(4.^1.))(0.$1.(>.(5.(4.^2.)(6.+4.(4.^9.)))(4.^>.)(4.^=.)(4.^2.))(0.$1.(>.(5.(4.^3.)(6.+4.(4.^:.)))(4.^>.)(4.^=.)(4.^3.))(0.$1.(>.(5.(4.^5.)(6.+4.(4.^;.)))(4.^>.)(4.^=.)(4.^5.))(0.$1.(>.(5.(4.^7.)(6.+4.(4.^<.)))(4.^>.)(4.^=.)(4.^7.))(0.$1.(8.(9.^?.)&1.)(0.$1.(2.(3.=)(4.^=.))(0.$1.(2.(4.^=.)(3.(?.$10.+1.)))(0.$1.(2.(3.=)(4.^?.))(0.$1.(2.(4.^?.)(3.(?.$10.+1.)))(11.$1.))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).
Definition montmul_clob : list (Z * positive) := ltac2:(CDefT.buildp (gd_tbl_LxP_SumsMont ()) "(0.(12.$13.$14.)(15.$13.$14.+5.^10.)(0.(12.$13.$14.)(15.$13.$14.+6.^11.)(0.(12.$13.$14.)(15.$13.$14.+7.^12.)(0.(12.$13.$14.)(15.$13.$14.+:.^13.)(0.(12.$13.$14.)(15.$13.$14.+;.^14.)(0.(12.$13.$14.)(15.$13.$14.+<.^15.)(0.(12.$13.$14.)(15.$13.$14.+=.^16.)(0.(12.$13.$14.)(15.$13.$14.+>.^17.)(0.(12.$13.$14.)(15.$13.$14.+?.^18.)(0.(12.$13.$14.)(15.$13.$14.+10.^19.)(0.(12.$13.$14.)(15.$13.$14.+11.^1:.)(0.(12.$13.$14.)(15.$13.$14.+1<.^1;.)(0.(12.$13.$14.)(15.$13.$14.+1=.^1<.)(0.(12.$13.$14.)(15.$13.$14.+1>.^1=.)(0.(12.$13.$14.)(15.$13.$14.+1?.^1>.)(11.(12.$13.$14.)))))))))))))))))")
(* [comment removed for export] *).

Definition SUM_montmulP : summary := ltac2:(CDefT.buildp (gd_tbl_LxP_SumsMont ()) "(16.$17.$18.#?.#?.#0.(0.(12.$13.$14.)(15.$13.$14.+:.^1.)(0.(12.$13.$14.)(15.$13.$14.+;.^2.)(0.(12.$13.$14.)(15.$13.$14.+<.^3.)(0.(12.$13.$14.)(15.$13.$14.+=.^4.)(0.(12.$13.$14.)(15.$13.$14.+>.^5.)(0.(12.$13.$14.)(15.$13.$14.+?.^6.)(0.(12.$13.$14.)(15.$13.$14.+11.^7.)(0.(12.$13.$14.)(15.$13.$14.+2.^=.)(0.(12.$13.$14.)(15.$13.$14.+1.^?.)(11.(12.$13.$14.)))))))))))(19.$14.)(0.$1:.(1;.(4.^1.)&4.(1<.^1.)(4.^8.)$1=.)(0.$1:.(1;.(4.^2.)&4.(1<.^2.)(4.^9.)$18.)(0.$1:.(1;.(4.^3.)&4.(1<.^3.)(4.^:.)$18.)(0.$1:.(1;.(4.^5.)&4.(1<.^4.)(4.^;.)$18.)(0.$1:.(1;.(4.^7.)&4.(1<.^5.)(4.^<.)$1=.)(11.$1:.))))))(1>.(12.$14.$14.)(15.$14.$14.^>.^=.))(11.(12.(12.$14.$14.)$14.))(11.$1:.)$1?.(0.(12.$20.$20.)(15.$20.$20.(4.^1.)(5.(4.^1.)(6.+4.(4.^6.))))(0.(12.$20.$20.)(15.$20.$20.(4.^7.)(5.(4.^7.)(6.+4.(5.(6.+2.(4.^6.))(3.+1.)))))(0.(12.$20.$20.)(15.$20.$20.(5.(4.^=.)(3.(<.$=.)))(4.^=.))(11.(12.$20.$20.)))))$21.(0.$1:.(1;.(4.^1.)&4.(1<.^6.)(4.^8.)$1=.)(0.$1:.(1;.(4.^7.)&4.(1<.^7.)(4.^<.)$1=.)(0.$1:.(22.(4.^>.)(4.^=.))(11.$1:.))))(11.$1.))")
(* [comment removed for export] *).

Local Ltac2 Set LiaOrc.tbl := fun () => "00H0@L10384330990.152L11200866206.125L11373369465.125L15372568033.125L1599111918.125 L1820788193.125 L18684245632.125L19743573473.125L228320730.152  L2481198071.125 L24955814843.125L35493463521.125L379047126.125  L38342170558.125L42463266511.125L45542131645.125L46132584567.125L47582620807.125L50184005215.125L51271919159.125L5198038747.125 L5203049907.125 L68259315013.125L7753404694.125 00001J02Y03h05908<09M0<L0=]0?70?m0Ao0C@0F50I50Jl0L;0MJ0N@0PM0RO0S^0Uk0W<0Z;S1X1A1B1N1T2NT3SPu2RA2xs2ys2zs2ns2ts2LT4PR204PR214PR224PR234PR244PR384PR403xs'3ts'3LX'3LT'S1X1A1B1N1T2NA3SPu2RA2xs2ys2zs2ns2ts2LA4PR204PR214PR224PR234PR244PR264PR384PR40S1X1A1B1N1T2NT3SPu2RA2xs2ys2zs2ns2ts2LT4PR204PR214PR224PR234PR244PR294PR384PR40S1X1A1B1N2an1T2NN3SPu2RA2xs2ys2zs2ns2ts2LN3PR84PR204PR214PR224PR234PR244PR384PR40S1X1A1B2bn1N2an1T2NX2NA2NB2NN2NT3SPu2LO2RA2xs2ys2zs2ns2ts2LX2LA2LB2LN2LT3PR13PR33PR53PR63PR73PR83PR94PR104PR114PR124PR134PR144PR194PR204PR214PR224PR234PR244PR314PR324PR334PR344PR354PR364PR384PR40S1X1A1B2bn1N1T2NB3SPu2RA2xs2ys2zs2ns2ts2LB3PR74PR204PR214PR224PR234PR244PR384PR40S1X1A1B2bn1N2an1T2NX2NA2NB2NN2NT3SPu2LO2RA2xs2ys2zs2ns2ts2LX2LA2LB2LN2LT3PR13PR33PR53PR73PR83PR94PR104PR114PR124PR134PR144PR164PR204PR214PR224PR234PR244PR314PR324PR334PR344PR354PR364PR384PR40S1X1A1B1N2an1T2NA3SPu2RA2xs2ys2zs2ns2ts2LA3PR64PR204PR214PR224PR234PR244PR384PR40S1X1A1B1N1T2NX3SPu2RA2xs2ys2zs2ns2ts2LX4PR204PR214PR224PR234PR244PR384PR403xs'3ts'3LX'3LT'S1X1A1B1N2an1T3SPu2RA2xs2ys2zs2ns2ts3PR13PR24PR384PR40S1X1A1B1N2an1T2NX2NN2NT3SPu2RA2xs2ys2zs2ns2ts2LX2LN2LT3PR13PR53PR83PR94PR104PR134PR144PR154PR194PR204PR214PR224PR234PR244PR384PR40S1X1A1B1N2an1T2NX3SPu2RA2xs2ys2zs2ns2ts2LX3PR54PR204PR214PR224PR234PR244PR384PR40S1X1A1B1N2an1T2NX2NA2NB2NN2NT3SPu2LO2RA2xs2ys2zs2ns2ts2LX2LA2LB2LN3PR13PR53PR63PR83PR94PR104PR114PR124PR134PR144PR174PR204PR214PR224PR234PR244PR314PR324PR334PR344PR354PR364PR384PR40S1X1A1B2bn1N2an1T2NX2NA2NB2NN2NT3SPu2LO2RA2xs2ys2zs2ns2ts2LX2LA2LB2LN3PR13PR33PR53PR63PR73PR83PR94PR104PR114PR124PR134PR144PR184PR204PR214PR224PR234PR244PR314PR324PR334PR344PR354PR364PR384PR40S1X1A1B1N2an1T2NX2NN2NT3SPu2RA2xs2ys2zs2ns2ts2LX2LN3PR13PR94PR104PR134PR144PR154PR184PR204PR214PR224PR234PR244PR384PR40S1X1A1B1N1T2NX3SPu2RA2xs2ys2zs2ns2ts2LX4PR204PR214PR224PR234PR244PR254PR384PR40S1X1A1B1N1T2NN3SPu2RA2xs2ys2zs2ns2ts2LN4PR204PR214PR224PR234PR244PR284PR384PR40S1X1A1B2bn1N1T3SPu2RA2xs2ys2zs2ns2ts3PR33PR44PR384PR40S1X1A1B1N2an1T2NX2NB2NN2NT3SPu2RA2xs2ys2zs2ns2ts2LX2LB2LN2LT3PR13PR53PR83PR94PR104PR124PR134PR144PR174PR194PR204PR214PR224PR234PR244PR384PR40S1X1A1B1N2an1T2NX2NN2NT3SPu2RA2xs2ys2zs2ns2ts2LX2LN2LT3PR13PR53PR83PR94PR104PR134PR144PR184PR194PR204PR214PR224PR234PR244PR384PR40S1X1A1B1N1T2NB3SPu2RA2xs2ys2zs2ns2ts2LB4PR204PR214PR224PR234PR244PR274PR384PR40S1X1A1B1N2an1T2NX2NA2NN2NT3SPu2RA2xs2ys2zs2ns2ts2LX2LA2LN2LT3PR13PR53PR83PR94PR104PR114PR134PR144PR164PR194PR204PR214PR224PR234PR244PR384PR40S1X1A1B1N2an1T2NT3SPu2RA2xs2ys2zs2ns2ts2LT3PR94PR204PR214PR224PR234PR244PR384PR40S1X1A1B2bn1N2an1T2NX2NA2NB2NN2NT3SPu2LO2RA2xs2ys2zs2ns2ts2LX2LA2LB2LN2LT3PR13PR33PR63PR73PR83PR94PR104PR114PR124PR134PR144PR154PR204PR214PR224PR234PR244PR314PR324PR334PR344PR354PR364PR384PR40". (* [comment removed for export] *)
Lemma sum_montmulP_valid : forall AL, summary_valid usegs AL SUM_montmulP.
Proof.
  intros AL. unfold SUM_montmulP, montmul_pre, montmul_clob, q, MPI_CORE_MONTMUL_STACK. lx_sum_unfold.
  intros X A B bn N an T NX NA NB NN NT SPu LO RA xs ys zs ns ts CS F fc m.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
  intros ALLCS _ MI R10 R11 R12 R13 R14 R15 R17 R2 R1 ST [HX LX] [HA LA] [HB LB] [HN LN] [HT LT].
  intros PR1 PR2 PR3 PR4 PR5 PR6 PR7 PR8 PR9 PR10 PR11 PR12 PR13 PR14 PR15 PR16 PR17 PR18 PR19 PR20 PR21 PR22 PR23 PR24 PR25 PR26 PR27 PR28 PR29
         PR30 PR31 PR32 PR33 PR34 PR35 PR36 PR37 PR38 PR39 PR40 PR41.
  lxp_pows.
  apply (evt_evtA_all usegs AL CS _ _ ALLCS).
  assert (U2 : bv_unsigned x2 = SPu) by (rewrite R2; apply lxp_uw64; assumption).
  assert (U1 : bv_unsigned x1 = RA) by (rewrite R1; apply lxp_uw64; assumption).
  pose proof U_mpi_core_montmul_spec as SP. unfold mpi_core_montmul_stmt, U_MPI_CORE_MONTMUL, MPI_CORE_MONTMUL_STACK in SP.
  eapply evt_cut.
  { eapply (SP x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m
               X A B bn N an T LO xs ys zs ns ts);
      rewrite ?U2, ?U1; first [eassumption | apply u32arr_ro; eassumption | lia | idtac]. }
  clear SP. cbv beta. intros ms' POST. unfold mpi_core_montmul_post, MPI_CORE_MONTMUL_STACK in POST.
  destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & xs' & ts' & -> & MU & WM & MI' & HX' & LX' & SKX & HT' & LT' & SKT & ST').
  apply evt_done. rewrite U2 in MU, ST'.
  lx_sum_post.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Definition SUM_montmulXAP : summary := ltac2:(CDefT.buildp (gd_tbl_LxP_SumsMont ()) "(16.$17.$18.#=.#?.#0.(0.(12.$13.$14.)(15.$13.$14.+:.^1.)(0.(12.$13.$14.)(15.$13.$14.+;.^1.)(0.(12.$13.$14.)(15.$13.$14.+<.^2.)(0.(12.$13.$14.)(15.$13.$14.+=.^3.)(0.(12.$13.$14.)(15.$13.$14.+>.^4.)(0.(12.$13.$14.)(15.$13.$14.+?.^5.)(0.(12.$13.$14.)(15.$13.$14.+11.^6.)(0.(12.$13.$14.)(15.$13.$14.+2.^;.)(0.(12.$13.$14.)(15.$13.$14.+1.^=.)(11.(12.$13.$14.)))))))))))(19.$14.)(0.$1:.(1;.(4.^1.)&4.(1<.^1.)(4.^7.)$1=.)(0.$1:.(1;.(4.^2.)&4.(1<.^2.)(4.^8.)$18.)(0.$1:.(1;.(4.^4.)&4.(1<.^3.)(4.^9.)$18.)(0.$1:.(1;.(4.^6.)&4.(1<.^4.)(4.^:.)$1=.)(11.$1:.)))))(1>.(12.$14.$14.)(15.$14.$14.^<.^;.))(11.(12.(12.$14.$14.)$14.))(11.$1:.)(0.$1.(2.(3.+1.)(4.^5.))(0.$1.(2.(4.^5.)(3.+1387.))(0.$1.(2.(3.+1.)(4.^3.))(0.$1.(2.(4.^3.)(3.+2710.))(0.$1.(2.(4.^5.)(4.^7.))(0.$1.(2.(4.^3.)(4.^8.))(0.$1.(2.(4.^5.)(4.^9.))(0.$1.(2.(5.(6.+2.(4.^5.))(3.+1.))(4.^:.))(0.$1.(7.(4.^1.)(6.+4.(4.^7.))(4.^6.)(6.+4.(4.^:.)))(0.$1.(7.(4.^2.)(6.+4.(4.^8.))(4.^6.)(6.+4.(4.^:.)))(0.$1.(7.(4.^4.)(6.+4.(4.^9.))(4.^6.)(6.+4.(4.^:.)))(0.$1.(7.(4.^4.)(6.+4.(4.^9.))(4.^1.)(6.+4.(4.^7.)))(0.$1.(8.(9.^1.)&2.)(0.$1.(8.(9.^2.)&2.)(0.$1.(8.(9.^4.)&2.)(0.$1.(8.(9.^6.)&2.)(0.$1.(:.(3.=)(4.^1.))(0.$1.(:.(3.=)(4.^2.))(0.$1.(:.(3.=)(4.^4.))(0.$1.(:.(3.=)(4.^6.))(0.$1.(:.(5.(4.^1.)(6.+4.(4.^7.)))(3.(;.+2.+40.)))(0.$1.(:.(5.(4.^2.)(6.+4.(4.^8.)))(3.(;.+2.+40.)))(0.$1.(:.(5.(4.^4.)(6.+4.(4.^9.)))(3.(;.+2.+40.)))(0.$1.(:.(5.(4.^6.)(6.+4.(4.^:.)))(3.(;.+2.+40.)))(0.$1.(2.(4.^<.)(5.(4.^;.)(3.(<.$=.))))(0.$1.(8.(9.^;.)&4.)(0.$1.(>.(5.(4.^1.)(6.+4.(4.^7.)))(4.^<.)(4.^;.)(4.^1.))(0.$1.(>.(5.(4.^2.)(6.+4.(4.^8.)))(4.^<.)(4.^;.)(4.^2.))(0.$1.(>.(5.(4.^4.)(6.+4.(4.^9.)))(4.^<.)(4.^;.)(4.^4.))(0.$1.(>.(5.(4.^6.)(6.+4.(4.^:.)))(4.^<.)(4.^;.)(4.^6.))(0.$1.(8.(9.^=.)&1.)(0.$1.(2.(3.=)(4.^;.))(0.$1.(2.(4.^;.)(3.(?.$10.+1.)))(0.$1.(2.(3.=)(4.^=.))(0.$1.(2.(4.^=.)(3.(?.$10.+1.)))(11.$1.))))))))))))))))))))))))))))))))))))(0.(12.$20.$20.)(15.$20.$20.(4.^1.)(5.(4.^1.)(6.+4.(4.^5.))))(0.(12.$20.$20.)(15.$20.$20.(4.^6.)(5.(4.^6.)(6.+4.(5.(6.+2.(4.^5.))(3.+1.)))))(0.(12.$20.$20.)(15.$20.$20.(5.(4.^;.)(3.(<.$=.)))(4.^;.))(11.(12.$20.$20.)))))(0.(12.$13.$14.)(15.$13.$14.+5.^>.)(0.(12.$13.$14.)(15.$13.$14.+6.^?.)(0.(12.$13.$14.)(15.$13.$14.+7.^10.)(0.(12.$13.$14.)(15.$13.$14.+:.^11.)(0.(12.$13.$14.)(15.$13.$14.+;.^12.)(0.(12.$13.$14.)(15.$13.$14.+<.^13.)(0.(12.$13.$14.)(15.$13.$14.+=.^14.)(0.(12.$13.$14.)(15.$13.$14.+>.^15.)(0.(12.$13.$14.)(15.$13.$14.+?.^16.)(0.(12.$13.$14.)(15.$13.$14.+10.^17.)(0.(12.$13.$14.)(15.$13.$14.+11.^18.)(0.(12.$13.$14.)(15.$13.$14.+1<.^19.)(0.(12.$13.$14.)(15.$13.$14.+1=.^1:.)(0.(12.$13.$14.)(15.$13.$14.+1>.^1;.)(0.(12.$13.$14.)(15.$13.$14.+1?.^1<.)(11.(12.$13.$14.)))))))))))))))))(0.$1:.(1;.(4.^1.)&4.(1<.^5.)(4.^7.)$1=.)(0.$1:.(1;.(4.^6.)&4.(1<.^6.)(4.^:.)$1=.)(0.$1:.(22.(4.^<.)(4.^;.))(11.$1:.))))(11.$1.))")
(* [comment removed for export] *).

Local Ltac2 Set LiaOrc.tbl := fun () => "00D0@L10384330990.141L11373369465.114L15372568033.114L1599111918.114 L1820788193.114 L228320730.141  L2481198071.114 L24955814843.114L35493463521.114L379047126.114  L38342170558.114L42463266511.114L45542131645.114L46132584567.114L47582620807.114L50184005215.114L51271919159.114L5198038747.114 L68259315013.114L7753404694.114 00001@02E03L06007708G0980:e0;l0>B0@c0BO0CT0DY0EJ0GF0I=0JB0KI0MiS1X1B1N1T2NT3SPu2RA2xs2zs2ns2ts2LT4PR174PR184PR194PR204PR324PR343xs'3ts'3LX'3LT'S1X1B1N1T2NT3SPu2RA2xs2zs2ns2ts2LT4PR174PR184PR194PR204PR244PR324PR34S1X1B1N2an1T2NN3SPu2RA2xs2zs2ns2ts2LN3PR74PR174PR184PR194PR204PR324PR34S1X1B2bn1N2an1T2NX2NB2NN2NT3SPu2LO2RA2xs2zs2ns2ts2LX2LB2LN2LT3PR13PR33PR53PR63PR73PR83PR94PR104PR114PR124PR164PR174PR184PR194PR204PR264PR274PR284PR294PR304PR324PR34S1X1B2bn1N1T2NB3SPu2RA2xs2zs2ns2ts2LB3PR64PR174PR184PR194PR204PR324PR34S1X1B1N1T2NX3SPu2RA2xs2zs2ns2ts2LX4PR174PR184PR194PR204PR324PR343xs'3ts'3LX'3LT'S1X1B1N2an1T3SPu2RA2xs2zs2ns2ts3PR13PR24PR324PR34S1X1B1N2an1T2NX2NN2NT3SPu2RA2xs2zs2ns2ts2LX2LN2LT3PR13PR53PR73PR83PR94PR134PR164PR174PR184PR194PR204PR324PR34S1X1B1N2an1T2NX3SPu2RA2xs2zs2ns2ts2LX3PR54PR174PR184PR194PR204PR324PR34S1X1B1N2an1T2NX2NB2NN2NT3SPu2LO2RA2xs2zs2ns2ts2LX2LB2LN3PR13PR53PR73PR83PR94PR104PR114PR124PR144PR174PR184PR194PR204PR264PR274PR284PR294PR304PR324PR34S1X1B2bn1N2an1T2NX2NB2NN2NT3SPu2LO2RA2xs2zs2ns2ts2LX2LB2LN3PR13PR33PR53PR63PR73PR83PR94PR104PR114PR124PR154PR174PR184PR194PR204PR264PR274PR284PR294PR304PR324PR34S1X1B1N2an1T2NX2NN2NT3SPu2RA2xs2zs2ns2ts2LX2LN3PR13PR83PR94PR114PR124PR134PR154PR174PR184PR194PR204PR324PR34S1X1B1N1T2NX3SPu2RA2xs2zs2ns2ts2LX4PR174PR184PR194PR204PR214PR324PR34S1X1B1N1T2NN3SPu2RA2xs2zs2ns2ts2LN4PR174PR184PR194PR204PR234PR324PR34S1X1B2bn1N1T3SPu2RA2xs2zs2ns2ts3PR33PR44PR324PR34S1X1B1N2an1T2NX2NB2NN2NT3SPu2RA2xs2zs2ns2ts2LB2LT3PR13PR53PR73PR83PR94PR104PR114PR124PR144PR164PR174PR184PR194PR204PR324PR34S1X1B1N2an1T2NX2NN2NT3SPu2RA2xs2zs2ns2ts2LX2LN2LT3PR13PR53PR73PR83PR94PR114PR124PR154PR164PR174PR184PR194PR204PR324PR34S1X1B1N1T2NB3SPu2RA2xs2zs2ns2ts2LB4PR174PR184PR194PR204PR224PR324PR34S1X1B1N2an1T2NT3SPu2RA2xs2zs2ns2ts2LT3PR84PR174PR184PR194PR204PR324PR34S1X1B2bn1N2an1T2NX2NB2NN2NT3SPu2LO2RA2xs2zs2ns2ts2LX2LB2LN2LT3PR13PR33PR63PR73PR83PR94PR104PR114PR124PR134PR174PR184PR194PR204PR264PR274PR284PR294PR304PR324PR34". (* [comment removed for export] *)
Lemma sum_montmulXAP_valid : forall AL, summary_valid usegs AL SUM_montmulXAP.
Proof.
  intros AL. unfold SUM_montmulXAP, q, MPI_CORE_MONTMUL_STACK. lx_sum_unfold.
  intros X B bn N an T NX NB NN NT SPu LO RA xs zs ns ts CS F fc m.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
  intros ALLCS _ MI R10 R11 R12 R13 R14 R15 R17 R2 R1 ST [HX LX] [HB LB] [HN LN] [HT LT].
  intros PR1 PR2 PR3 PR4 PR5 PR6 PR7 PR8 PR9 PR10 PR11 PR12 PR13 PR14 PR15 PR16 PR17 PR18 PR19 PR20 PR21 PR22 PR23 PR24 PR25 PR26 PR27 PR28 PR29
         PR30 PR31 PR32 PR33 PR34 PR35.
  lxp_pows.
  apply (evt_evtA_all usegs AL CS _ _ ALLCS).
  assert (U2 : bv_unsigned x2 = SPu) by (rewrite R2; apply lxp_uw64; assumption).
  assert (U1 : bv_unsigned x1 = RA) by (rewrite R1; apply lxp_uw64; assumption).
  pose proof U_mpi_core_montmul_spec as SP. unfold mpi_core_montmul_stmt, U_MPI_CORE_MONTMUL, MPI_CORE_MONTMUL_STACK in SP.
  eapply evt_cut.
  { eapply (SP x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m
               X X B bn N an T LO xs xs zs ns ts);
      rewrite ?U2, ?U1; first [eassumption | apply u32arr_ro; eassumption | lia | idtac]. }
  clear SP. cbv beta. intros ms' POST. unfold mpi_core_montmul_post, MPI_CORE_MONTMUL_STACK in POST.
  destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & xs' & ts' & -> & MU & WM & MI' & HX' & LX' & SKX & HT' & LT' & SKT & ST').
  apply evt_done. rewrite U2 in MU, ST'.
  lx_sum_post.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SUM_montmulB1P : summary := ltac2:(CDefT.buildp (gd_tbl_LxP_SumsMont ()) "(16.$17.$18.#?.#?.#0.(0.(12.$13.$14.)(15.$13.$14.+:.^1.)(0.(12.$13.$14.)(15.$13.$14.+;.^2.)(0.(12.$13.$14.)(15.$13.$14.+<.^3.)(0.(12.$13.$14.)(15.$13.$14.+=.^4.)(0.(12.$13.$14.)(15.$13.$14.+>.^5.)(0.(12.$13.$14.)(15.$13.$14.+?.^6.)(0.(12.$13.$14.)(15.$13.$14.+11.^7.)(0.(12.$13.$14.)(15.$13.$14.+2.^=.)(0.(12.$13.$14.)(15.$13.$14.+1.^?.)(11.(12.$13.$14.)))))))))))(19.$14.)(0.$1:.(1;.(4.^1.)&4.(1<.^1.)(4.^8.)$1=.)(0.$1:.(1;.(4.^2.)&4.(1<.^2.)(4.^9.)$18.)(0.$1:.(23.(4.^3.)(0.$24.(25.&4.(4.^:.))(11.$24.)))(0.$1:.(1;.(4.^5.)&4.(1<.^3.)(4.^;.)$18.)(0.$1:.(1;.(4.^7.)&4.(1<.^4.)(4.^<.)$1=.)(11.$1:.))))))(1>.(12.$14.$14.)(15.$14.$14.^>.^=.))(11.(12.(12.$14.$14.)$14.))(11.$1:.)(0.$1.(26.(4.^4.)(3.+1.))(0.$1.(2.(3.+1.)(4.^6.))(0.$1.(2.(4.^6.)(3.+1387.))(0.$1.(2.(4.^6.)(4.^8.))(0.$1.(2.(4.^6.)(4.^9.))(0.$1.(2.(4.^6.)(4.^;.))(0.$1.(2.(5.(6.+2.(4.^6.))(3.+1.))(4.^<.))(0.$1.(7.(4.^1.)(6.+4.(4.^8.))(4.^7.)(6.+4.(4.^<.)))(0.$1.(7.(4.^2.)(6.+4.(4.^9.))(4.^7.)(6.+4.(4.^<.)))(0.$1.(7.(4.^3.)(3.+4.)(4.^7.)(6.+4.(4.^<.)))(0.$1.(7.(4.^5.)(6.+4.(4.^;.))(4.^7.)(6.+4.(4.^<.)))(0.$1.(7.(4.^5.)(6.+4.(4.^;.))(4.^1.)(6.+4.(4.^8.)))(0.$1.(8.(9.^1.)&2.)(0.$1.(8.(9.^2.)&2.)(0.$1.(8.(9.^3.)&2.)(0.$1.(8.(9.^5.)&2.)(0.$1.(8.(9.^7.)&2.)(0.$1.(:.(3.=)(4.^1.))(0.$1.(:.(3.=)(4.^2.))(0.$1.(:.(3.=)(4.^3.))(0.$1.(:.(3.=)(4.^5.))(0.$1.(:.(3.=)(4.^7.))(0.$1.(:.(5.(4.^1.)(6.+4.(4.^8.)))(3.(;.+2.+40.)))(0.$1.(:.(5.(4.^2.)(6.+4.(4.^9.)))(3.(;.+2.+40.)))(0.$1.(:.(5.(4.^3.)(3.+4.))(3.(;.+2.+40.)))(0.$1.(:.(5.(4.^5.)(6.+4.(4.^;.)))(3.(;.+2.+40.)))(0.$1.(:.(5.(4.^7.)(6.+4.(4.^<.)))(3.(;.+2.+40.)))(0.$1.(2.(4.^>.)(5.(4.^=.)(3.(<.$=.))))(0.$1.(8.(9.^=.)&4.)(0.$1.(>.(5.(4.^1.)(6.+4.(4.^8.)))(4.^>.)(4.^=.)(4.^1.))(0.$1.(>.(5.(4.^2.)(6.+4.(4.^9.)))(4.^>.)(4.^=.)(4.^2.))(0.$1.(>.(5.(4.^3.)(3.+4.))(4.^>.)(4.^=.)(4.^3.))(0.$1.(>.(5.(4.^5.)(6.+4.(4.^;.)))(4.^>.)(4.^=.)(4.^5.))(0.$1.(>.(5.(4.^7.)(6.+4.(4.^<.)))(4.^>.)(4.^=.)(4.^7.))(0.$1.(8.(9.^?.)&1.)(0.$1.(2.(3.=)(4.^=.))(0.$1.(2.(4.^=.)(3.(?.$10.+1.)))(0.$1.(2.(3.=)(4.^?.))(0.$1.(2.(4.^?.)(3.(?.$10.+1.)))(0.$1.(2.(3.=)(4.^:.))(0.$1.(2.(4.^:.)(3.(?.$10.+1.)))(11.$1.))))))))))))))))))))))))))))))))))))))))))(0.(12.$20.$20.)(15.$20.$20.(4.^1.)(5.(4.^1.)(6.+4.(4.^6.))))(0.(12.$20.$20.)(15.$20.$20.(4.^7.)(5.(4.^7.)(6.+4.(5.(6.+2.(4.^6.))(3.+1.)))))(0.(12.$20.$20.)(15.$20.$20.(5.(4.^=.)(3.(<.$=.)))(4.^=.))(11.(12.$20.$20.)))))$21.(0.$1:.(1;.(4.^1.)&4.(1<.^5.)(4.^8.)$1=.)(0.$1:.(1;.(4.^7.)&4.(1<.^6.)(4.^<.)$1=.)(0.$1:.(22.(4.^>.)(4.^=.))(11.$1:.))))(11.$1.))")
(* [comment removed for export] *).

Lemma lxp_cell4_u32s : forall segs m B (w : word), rw_cells segs m B [C4 w] -> bytes_at segs m B (u32s [w]).
Proof.
  intros segs m B w [[_ HB] _]. cbn -[le4] in HB. rewrite app_nil_r in HB.
  change (u32s [w]) with (le4 w ++ []). rewrite app_nil_r. exact HB.
Qed.

Local Ltac2 Set LiaOrc.tbl := fun () => "00F0@L10384330990.149L11200866206.122L11373369465.122L15372568033.122L1599111918.122 L18684245632.122L19743573473.122L228320730.149  L2481198071.122 L24955814843.122L3148860727.122 L35493463521.122L38342170558.122L42463266511.122L45542131645.122L46132584567.122L50184005215.122L51271919159.122L5203049907.122 L55062996503.122L68259315013.122L7753404694.122 00001G02S03_04m07\0:D0;R0<i0=\0?[0@C0AQ0D=0F90GE0HQ0Ig0Kf0N00NX0Of0RRS1X1A1B1N1T2NT3SPu2RA2xs2ys2ns2ts2LT4PR204PR214PR224PR234PR244PR384PR403xs'3ts'3LX'3LT'S1X1A1B1N1T2NA3SPu2RA2xs2ys2ns2ts2LA4PR204PR214PR224PR234PR244PR264PR384PR40S1X1A1B1N1T2NT3SPu2RA2xs2ys2ns2ts2LT4PR204PR214PR224PR234PR244PR294PR384PR40S1X1A1B1N2an1T2NN3SPu2RA2xs2ys2ns2ts2LN3PR84PR204PR214PR224PR234PR244PR384PR40S1X1A1B1N2an1T2NX2NA2NN2NT3SPu2LO2RA2xs2ys2ns2ts2LX2LA2LN2LT3PR13PR53PR63PR83PR94PR104PR114PR124PR134PR144PR194PR204PR214PR224PR234PR244PR314PR324PR334PR344PR354PR364PR384PR40S1X1A1B1N2an1T2NX2NA2NN2NT3SPu2LO2RA2xs2ys2ns2ts2LX2LA2LN3PR13PR53PR83PR94PR104PR114PR124PR134PR144PR164PR204PR214PR224PR234PR244PR314PR324PR334PR344PR354PR364PR384PR40S1X1A1B1N2an1T2NA3SPu2RA2xs2ys2ns2ts2LA3PR64PR204PR214PR224PR234PR244PR384PR40S1X1A1B1N1T2NX3SPu2RA2xs2ys2ns2ts2LX4PR204PR214PR224PR234PR244PR384PR403xs'3ts'3LX'3LT'S1X1A1B1N2an1T3SPu2RA2xs2ys2ns2ts3PR13PR24PR384PR40S1X1A1B1N2an1T2NX2NN2NT3SPu2RA2xs2ys2ns2ts2LX2LN2LT3PR13PR53PR83PR94PR104PR134PR144PR154PR194PR204PR214PR224PR234PR244PR384PR40S1X1A1B1N1T3SPu2RA2xs2ys2ns2ts4PR384PR40S1X1A1B1N2an1T2NX3SPu2RA2xs2ys2ns2ts2LX3PR54PR204PR214PR224PR234PR244PR384PR40S1X1A1B1N2an1T2NX2NA2NN2NT3SPu2LO2RA2xs2ys2ns2ts2LX2LA2LN3PR13PR53PR63PR83PR94PR104PR114PR124PR134PR144PR184PR204PR214PR224PR234PR244PR314PR324PR334PR344PR354PR364PR384PR40S1X1A1B1N2an1T2NX2NN2NT3SPu2RA2xs2ys2ns2ts2LX2LN3PR13PR53PR83PR94PR104PR134PR144PR154PR184PR204PR214PR224PR234PR244PR384PR40S1X1A1B1N1T2NX3SPu2RA2xs2ys2ns2ts2LX4PR204PR214PR224PR234PR244PR254PR384PR40S1X1A1B1N1T2NN3SPu2RA2xs2ys2ns2ts2LN4PR204PR214PR224PR234PR244PR284PR384PR40S1X1A1B1N1T2NT3SPu2RA2xs2ys2ns2ts2LT4PR124PR174PR194PR204PR214PR224PR234PR244PR384PR40S1X1A1B1N2an1T2NX2NN2NT3SPu2RA2xs2ys2ns2ts2LX2LN2LT3PR13PR53PR83PR94PR104PR134PR144PR184PR194PR204PR214PR224PR234PR244PR384PR40S1X1A1B1N2an1T2NX2NA2NN2NT3SPu2RA2xs2ys2ns2ts2LX2LA2LN2LT3PR13PR53PR83PR94PR104PR114PR134PR144PR164PR194PR204PR214PR224PR234PR244PR384PR40S1X1A1B1N1T3SPu2RA2xs2ys2ns2ts4PR384PR40S1X1A1B1N2an1T2NT3SPu2RA2xs2ys2ns2ts2LT3PR94PR204PR214PR224PR234PR244PR384PR40S1X1A1B1N2an1T2NX2NA2NN2NT3SPu2LO2RA2xs2ys2ns2ts2LX2LA2LN3PR13PR53PR63PR83PR94PR104PR114PR124PR134PR144PR154PR204PR214PR224PR234PR244PR314PR324PR334PR344PR354PR364PR384PR40". (* [comment removed for export] *)
Lemma sum_montmulB1P_valid : forall AL, summary_valid usegs AL SUM_montmulB1P.
Proof.
  intros AL. unfold SUM_montmulB1P, montmul_clob, q, MPI_CORE_MONTMUL_STACK. lx_sum_unfold.
  intros X A B bn N an T NX NA vB NN NT SPu LO RA xs ys ns ts CS F fc m.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
  intros ALLCS _ MI R10 R11 R12 R13 R14 R15 R17 R2 R1 ST [HX LX] [HA LA] HBc [HN LN] [HT LT].
  intros PR0 PR1 PR2 PR5 PR6 PR8 PR9 PR10 PR11 PR12 PR13 PR14 PR15 PR16 PR17 PR18 PR19 PR20 PR21 PR22 PR23 PR24 PR25 PR26 PR27 PR28 PR29
         PR30 PR31 PR32 PR33 PR34 PR35 PR36 PR37 PR38 PR39 PR40 PR41 PR42 PR43.
  lxp_pows.
  apply (evt_evtA_all usegs AL CS _ _ ALLCS).
  assert (U2 : bv_unsigned x2 = SPu) by (rewrite R2; apply lxp_uw64; assumption).
  assert (U1 : bv_unsigned x1 = RA) by (rewrite R1; apply lxp_uw64; assumption).
  pose proof (lxp_cell4_u32s _ _ _ _ HBc) as HB. subst bn.
  pose proof U_mpi_core_montmul_spec as SP. unfold mpi_core_montmul_stmt, U_MPI_CORE_MONTMUL, MPI_CORE_MONTMUL_STACK in SP.
  eapply evt_cut.
  { eapply (SP x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m
               X A B 1 N an T LO xs ys [Z_to_bv 64 vB] ns ts);
      rewrite ?U2, ?U1; first [eassumption | apply u32arr_ro; eassumption | cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia | idtac]. }
  clear SP. cbv beta. intros ms' POST. unfold mpi_core_montmul_post, MPI_CORE_MONTMUL_STACK in POST.
  destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & xs' & ts' & -> & MU & WM & MI' & HX' & LX' & SKX & HT' & LT' & SKT & ST').
  apply evt_done. rewrite U2 in MU, ST'.
  lx_sum_post.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Definition SUMSMONT : list summary := [SUM_montmulP; SUM_montmulXAP; SUM_montmulB1P].
Lemma sumsmont_ok : forall GS AL, Forall (summary_okG usegs AL GS) SUMSMONT.
Proof.
  intros GS AL. unfold SUMSMONT.
  constructor; [| constructor; [| constructor; [| constructor]]]; apply apply_summary_soundG; apply (summary_validG_ext usegs AL [] GS); try reflexivity.
  - apply sum_montmulP_valid.
  - apply sum_montmulXAP_valid.
  - apply sum_montmulB1P_valid.
Qed.
