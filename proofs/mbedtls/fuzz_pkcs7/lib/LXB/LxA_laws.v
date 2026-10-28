(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_asn1_get_tag P_asn1_get_len P_asn1_get_bitstring P_oid P_asn1_get_mpi.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg A_asn1_get_len A_asn1_get_tag_stmt A_asn1_get_tag A_asn1_get_bool A_asn1_get_int_loops A_asn1_get_int A_asn1_get_bitstring_null A_asn1_get_bitstring.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_rt_facts A_asn1_get_alg_A A_oid A_x509_get_time_A A_asn1_get_alg_null_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_x509_get_time P_x509_get_dates.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface Arr CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxSum LxSoundSum.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt LxA_sums.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac qlia ::= orc_qlia. (* [comment removed for export] *)
Local Ltac pqlia ::= orc_pqlia. (* [comment removed for export] *)
Local Ltac lia1 D ::= orc_lia1 D. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Local Ltac clear_mods ::= fc_clear_mods. (* [comment removed for export] *)
Local Ltac keep_disj1 D ::= fc_keep_disj1 D. (* [comment removed for export] *)
Ltac2 gd_tbl_LxA_laws () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.LX.LxSum.SUMXL"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Numbers.BinNums.positive"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.mfact"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.MRw"; "RocqVerifyHarness.AgentSubmission.LXB.LxA_sums.q"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.cellx"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.XZ"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.XB"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.MAobj"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.ELit"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.pfact"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FEq"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FLe"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.EAdd"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FLt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FSep"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FSep0"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FAl"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.EZv"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.two64"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.EMulC"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.expr"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.MStk"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FOr2"; "RocqVerifyHarness.AgentSubmission.B.A_x509_get_time_A.x509_get_time_stmtA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "Corelib.Lists.ListDef.nth"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_smalloc"; "stdpp.bitvector.definitions.bv_unsigned"; "stdpp.bitvector.definitions.bv"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_tp"; "Corelib.Init.Peano.lt"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.LX.LxSoundSum.summary_okL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "SUM_gettimeA_L"; "RocqVerifyHarness.AgentSubmission.B.A_asn1_get_alg_null_A.asn1_get_alg_null_stmtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_amem"; "SUM_algnullA_L"].


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SUM_gettimeA_L (pc : Z) (kp kt kb kbl klo kslo ksm ktp kspv : nat) : summary := ltac2:(CDefT.buildp (gd_tbl_LxA_laws ()) "(0.O:.$1.#11.#16.#2.(2.(3.$4.$5.)(6.$4.$5.+:.^?.)(2.(3.$4.$5.)(6.$4.$5.+;.^2.)(2.(3.$4.$5.)(6.$4.$5.+<.^10.)(2.(3.$4.$5.)(6.$4.$5.+2.^7.)(2.(3.$4.$5.)(6.$4.$5.+4.^=.)(7.(3.$4.$5.)))))))(2.(3.$5.$8.)(6.$5.$8.^1.O9.)(2.(3.$5.$8.)(6.$5.$8.^3.O8.)(2.(3.$5.$8.)(6.$5.$8.^5.O7.)(2.(3.$5.$8.)(6.$5.$8.^6.O6.)(2.(3.$5.$8.)(6.$5.$8.^8.O5.)(2.(3.$5.$8.)(6.$5.$8.^9.#1.)(2.(3.$5.$8.)(6.$5.$8.^:.#3.)(2.(3.$5.$8.)(6.$5.$8.^;.O4.)(2.(3.$5.$8.)(6.$5.$8.^<.O3.)(2.(3.$5.$8.)(6.$5.$8.^>.O2.)(2.(3.$5.$8.)(6.$5.$8.^11.O1.)(7.(3.$5.$8.)))))))))))))(9.$5.)(2.$:.(;.(<.^1.)(2.$=.(>.&8.(<.^4.))(7.$=.)))(2.$:.(;.(<.^3.)(2.$=.(?.&18.^2.)(7.$=.)))(7.$:.)))(10.(3.$5.$5.)(6.$5.$5.^8.^7.))(2.(3.(3.$5.$5.)$5.)(6.(3.$5.$5.)$5.(6.$5.$5.^5.^6.)^1.)(7.(3.(3.$5.$5.)$5.)))(2.$:.(11.(<.^1.)(12.+8.))(2.$:.(11.(<.^3.)(12.+18.))(2.$:.(11.(<.^5.)(<.^6.))(7.$:.))))(2.$13.(14.(<.^?.)(<.^1.))(2.$13.(14.(<.^10.)(<.^3.))(2.$13.(14.(<.^=.)(<.^>.))(2.$13.(14.(<.^7.)(<.^11.))(2.$13.(15.(<.^5.)(<.^4.))(2.$13.(15.(<.^4.)(<.^2.))(2.$13.(15.(<.^2.)(16.(<.^5.)(<.^6.)))(2.$13.(17.(16.(<.^5.)(<.^6.))(12.(18.+2.+3?.)))(2.$13.(19.(<.^1.)(12.+8.)(<.^3.)(12.+18.))(2.$13.(1:.(<.^6.)(<.^1.)(12.+8.)(<.^5.)(<.^6.))(2.$13.(1:.(<.^6.)(<.^3.)(12.+18.)(<.^5.)(<.^6.))(2.$13.(1;.(1<.^1.)&3.)(2.$13.(1;.(1<.^3.)&2.)(2.$13.(17.(12.=)(<.^1.))(2.$13.(15.(16.(<.^1.)(12.+8.))(12.$1=.))(2.$13.(17.(12.=)(<.^3.))(2.$13.(15.(16.(<.^3.)(12.+18.))(12.$1=.))(2.$13.(17.(12.=)(<.^5.))(2.$13.(15.(<.^8.)(16.(<.^7.)(1>.-1.(12.+<0.))))(2.$13.(15.(<.^8.)(16.(16.(<.^7.)(1>.-1.(12.+;0.)))(1>.-1.(<.^<.))))(2.$13.(15.(12.=)(<.^<.))(2.$13.(15.(<.^:.)(<.^;.))(2.$13.(15.(<.^;.)(<.^8.))(2.$13.(1;.(1<.^7.)&4.)(2.$13.(15.(<.^7.)(<.^9.))(2.$13.(15.(<.^7.)(12.(18.+2.+2?.)))(2.$13.(19.(<.^1.)(12.+8.)(<.^8.)(16.(<.^7.)(1>.-1.(<.^8.))))(2.$13.(19.(<.^3.)(12.+18.)(<.^8.)(16.(<.^7.)(1>.-1.(<.^8.))))(2.$13.(1:.(<.^6.)(<.^5.)(<.^6.)(<.^8.)(16.(<.^7.)(1>.-1.(<.^8.))))(2.$13.(15.(12.=)(<.^7.))(2.$13.(15.(<.^7.)(12.(1?.$1=.+1.)))(7.$13.))))))))))))))))))))))))))))))))(2.(3.$20.$20.)(6.$20.$20.(<.^1.)(16.(<.^1.)(12.+8.)))(2.(3.$20.$20.)(6.$20.$20.(<.^3.)(16.(<.^3.)(12.+18.)))(7.(3.$20.$20.))))(2.(3.$4.$5.)(6.$4.$5.+:.^12.)(2.(3.$4.$5.)(6.$4.$5.+5.^1:.)(2.(3.$4.$5.)(6.$4.$5.+6.^1;.)(2.(3.$4.$5.)(6.$4.$5.+7.^1<.)(2.(3.$4.$5.)(6.$4.$5.+;.^1=.)(2.(3.$4.$5.)(6.$4.$5.+<.^1>.)(2.(3.$4.$5.)(6.$4.$5.+=.^1?.)(2.(3.$4.$5.)(6.$4.$5.+>.^20.)(2.(3.$4.$5.)(6.$4.$5.+?.^21.)(2.(3.$4.$5.)(6.$4.$5.+10.^22.)(2.(3.$4.$5.)(6.$4.$5.+11.^23.)(2.(3.$4.$5.)(6.$4.$5.+1<.^24.)(2.(3.$4.$5.)(6.$4.$5.+1=.^25.)(2.(3.$4.$5.)(6.$4.$5.+1>.^26.)(2.(3.$4.$5.)(6.$4.$5.+1?.^27.)(7.(3.$4.$5.)))))))))))))))))(2.$:.(;.(<.^1.)(2.$=.(>.&8.(<.^13.))(7.$=.)))(2.$:.(;.(<.^3.)(2.$=.(>.&4.(<.^14.))(2.$=.(>.&4.(<.^15.))(2.$=.(>.&4.(<.^16.))(2.$=.(>.&4.(<.^17.))(2.$=.(>.&4.(<.^18.))(2.$=.(>.&4.(<.^19.))(7.$=.))))))))(2.$:.(21.(<.^8.)(<.^7.))(7.$:.))))(2.$13.(17.(12.-3000.)(<.^12.))(2.$13.(15.(<.^12.)(12.=))(2.$13.(15.(<.^4.)(<.^13.))(2.$13.(15.(<.^13.)(<.^2.))(2.$13.(15.(12.=)(<.^14.))(2.$13.(15.(<.^14.)(12.(1?.$1=.+1.)))(2.$13.(15.(12.=)(<.^15.))(2.$13.(15.(<.^15.)(12.(1?.$1=.+1.)))(2.$13.(15.(12.=)(<.^16.))(2.$13.(15.(<.^16.)(12.(1?.$1=.+1.)))(2.$13.(15.(12.=)(<.^17.))(2.$13.(15.(<.^17.)(12.(1?.$1=.+1.)))(2.$13.(15.(12.=)(<.^18.))(2.$13.(15.(<.^18.)(12.(1?.$1=.+1.)))(2.$13.(15.(12.=)(<.^19.))(2.$13.(15.(<.^19.)(12.(1?.$1=.+1.)))(7.$13.)))))))))))))))))(2.$8.#0.(2.$8.#1.(2.$8.#2.(2.$8.#3.(7.$8.)))))(10.$8.#0.))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition SUM_algnullA_L (pc : Z) (kp ka kb kbl klo kslo ksm ktp kspv kam : nat) : summary := ltac2:(CDefT.buildp (gd_tbl_LxA_laws ()) "(0.O;.$1.#16.#14.#1.(2.(3.$4.$5.)(6.$4.$5.+:.^?.)(2.(3.$4.$5.)(6.$4.$5.+;.^2.)(2.(3.$4.$5.)(6.$4.$5.+<.^10.)(2.(3.$4.$5.)(6.$4.$5.+2.^7.)(2.(3.$4.$5.)(6.$4.$5.+4.^=.)(7.(3.$4.$5.)))))))(2.(3.$5.$8.)(6.$5.$8.^1.O:.)(2.(3.$5.$8.)(6.$5.$8.^3.O9.)(2.(3.$5.$8.)(6.$5.$8.^5.O8.)(2.(3.$5.$8.)(6.$5.$8.^6.O7.)(2.(3.$5.$8.)(6.$5.$8.^8.O6.)(2.(3.$5.$8.)(6.$5.$8.^9.#1.)(2.(3.$5.$8.)(6.$5.$8.^:.#3.)(2.(3.$5.$8.)(6.$5.$8.^;.O5.)(2.(3.$5.$8.)(6.$5.$8.^<.O4.)(2.(3.$5.$8.)(6.$5.$8.^>.O3.)(2.(3.$5.$8.)(6.$5.$8.^11.O2.)(2.(3.$5.$8.)(6.$5.$8.^12.O1.)(7.(3.$5.$8.))))))))))))))(9.$5.)(2.$:.(;.(<.^1.)(2.$=.(>.&8.(<.^4.))(7.$=.)))(2.$:.(;.(<.^3.)(2.$=.(>.&4.(<.^13.))(2.$=.(>.&4.(<.^14.))(2.$=.(>.&8.(<.^15.))(2.$=.(>.&8.(<.^16.))(7.$=.))))))(7.$:.)))(10.(3.$5.$5.)(6.$5.$5.^8.^7.))(2.(3.(3.$5.$5.)$5.)(6.(3.$5.$5.)$5.(6.$5.$5.^5.^6.)^1.)(7.(3.(3.$5.$5.)$5.)))(2.$:.(11.(<.^1.)(12.+8.))(2.$:.(11.(<.^3.)(12.+18.))(2.$:.(11.(<.^5.)(<.^6.))(7.$:.))))(2.$13.(14.(<.^?.)(<.^1.))(2.$13.(14.(<.^10.)(<.^3.))(2.$13.(14.(<.^=.)(<.^>.))(2.$13.(14.(<.^7.)(<.^11.))(2.$13.(15.(<.^5.)(<.^4.))(2.$13.(15.(<.^4.)(<.^2.))(2.$13.(15.(<.^2.)(16.(<.^5.)(<.^6.)))(2.$13.(17.(16.(<.^5.)(<.^6.))(12.(18.+2.+3?.)))(2.$13.(19.(<.^1.)(12.+8.)(<.^3.)(12.+18.))(2.$13.(1:.(<.^6.)(<.^1.)(12.+8.)(<.^5.)(<.^6.))(2.$13.(1:.(<.^6.)(<.^3.)(12.+18.)(<.^5.)(<.^6.))(2.$13.(1;.(1<.^1.)&3.)(2.$13.(1;.(1<.^3.)&3.)(2.$13.(17.(12.=)(<.^1.))(2.$13.(15.(16.(<.^1.)(12.+8.))(12.$1=.))(2.$13.(17.(12.=)(<.^3.))(2.$13.(15.(16.(<.^3.)(12.+18.))(12.$1=.))(2.$13.(17.(12.=)(<.^5.))(2.$13.(15.(<.^8.)(16.(<.^7.)(1>.-1.(12.+1070.))))(2.$13.(15.(<.^8.)(16.(16.(<.^7.)(1>.-1.(12.+130.)))(1>.-1.(<.^12.))))(2.$13.(15.(<.^8.)(16.(16.(<.^7.)(1>.-1.(12.+70.)))(1>.-1.(<.^<.))))(2.$13.(15.(12.=)(<.^12.))(2.$13.(15.(12.=)(<.^<.))(2.$13.(15.(<.^:.)(<.^;.))(2.$13.(15.(<.^;.)(<.^8.))(2.$13.(1;.(1<.^7.)&4.)(2.$13.(15.(<.^7.)(<.^9.))(2.$13.(15.(<.^7.)(12.(18.+2.+2?.)))(2.$13.(19.(<.^1.)(12.+8.)(<.^8.)(16.(<.^7.)(1>.-1.(<.^8.))))(2.$13.(19.(<.^3.)(12.+18.)(<.^8.)(16.(<.^7.)(1>.-1.(<.^8.))))(2.$13.(1:.(<.^6.)(<.^5.)(<.^6.)(<.^8.)(16.(<.^7.)(1>.-1.(<.^8.))))(2.$13.(15.(12.=)(<.^7.))(2.$13.(15.(<.^7.)(12.(1?.$1=.+1.)))(7.$13.))))))))))))))))))))))))))))))))))(2.(3.$20.$20.)(6.$20.$20.(<.^1.)(16.(<.^1.)(12.+8.)))(2.(3.$20.$20.)(6.$20.$20.(<.^3.)(16.(<.^3.)(12.+18.)))(7.(3.$20.$20.))))(2.(3.$4.$5.)(6.$4.$5.+:.^17.)(2.(3.$4.$5.)(6.$4.$5.+5.^1=.)(2.(3.$4.$5.)(6.$4.$5.+6.^1>.)(2.(3.$4.$5.)(6.$4.$5.+7.^1?.)(2.(3.$4.$5.)(6.$4.$5.+;.^20.)(2.(3.$4.$5.)(6.$4.$5.+<.^21.)(2.(3.$4.$5.)(6.$4.$5.+=.^22.)(2.(3.$4.$5.)(6.$4.$5.+>.^23.)(2.(3.$4.$5.)(6.$4.$5.+?.^24.)(2.(3.$4.$5.)(6.$4.$5.+10.^25.)(2.(3.$4.$5.)(6.$4.$5.+11.^26.)(2.(3.$4.$5.)(6.$4.$5.+1<.^27.)(2.(3.$4.$5.)(6.$4.$5.+1=.^28.)(2.(3.$4.$5.)(6.$4.$5.+1>.^29.)(2.(3.$4.$5.)(6.$4.$5.+1?.^2:.)(7.(3.$4.$5.)))))))))))))))))(2.$:.(;.(<.^1.)(2.$=.(>.&8.(<.^18.))(7.$=.)))(2.$:.(;.(<.^3.)(2.$=.(>.&4.(<.^19.))(2.$=.(>.&4.(<.^1:.))(2.$=.(>.&8.(<.^1;.))(2.$=.(>.&8.(<.^1<.))(7.$=.))))))(2.$:.(21.(<.^8.)(<.^7.))(7.$:.))))(2.$13.(17.(12.-7?.)(<.^17.))(2.$13.(15.(<.^17.)(12.=))(2.$13.(15.(<.^4.)(<.^18.))(2.$13.(15.(<.^18.)(<.^2.))(2.$13.(15.(12.=)(<.^19.))(2.$13.(15.(<.^19.)(12.(1?.$1=.+1.)))(2.$13.(15.(12.=)(<.^1:.))(2.$13.(15.(<.^1:.)(12.(1?.$1=.+1.)))(2.$13.(15.(12.=)(<.^1;.))(2.$13.(15.(<.^1;.)(12.(1?.$1=.+1.)))(2.$13.(15.(12.=)(<.^1<.))(2.$13.(15.(<.^1<.)(12.(1?.$1=.+1.)))(2.$13.(22.(16.(<.^17.)(12.+1.))(12.=)(<.^5.)(<.^1<.))(2.$13.(22.(16.(<.^17.)(12.+1.))(12.=)(16.(<.^1<.)(<.^1;.))(<.^18.))(7.$13.)))))))))))))))(2.$8.#0.(2.$8.#1.(2.$8.#2.(2.$8.#3.(7.$8.)))))(10.$8.#0.))")
(* [comment removed for export] *).


(* [comment removed for export] *)
Section SLAW.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Variables (h : HST asegs R HIA) (LB LF' LF0 : list blk) (spv SP0 SSP0 slo SHA SHB : Z) (W0 : list ivl) (m00 : mem).
  Variables (GSX : list Z) (OPS : list (mem -> Prop)) (LAWS : list (list (Z * Z) -> mem -> mem -> Prop)).
  Let GS : list Z := alloc_ceiling :: GSX.
  Let TOP : Z := hstkhi asegs R HIA h.
  Hypothesis G1 : nth 1 GS 0 = htop asegs R HIA h.
  Hypothesis G3 : nth 3 GS 0 = arl_stklo R.
  Hypothesis O0 : nth 0 OPS (fun _ => True) = (fun m => HMQ R HIA h LB LF' m).
  Hypothesis O1 : nth 1 OPS (fun _ => True) = (fun m => presW asegs R HIA h LB LF0 SP0 SSP0 W0 m00 m).
  Hypothesis O2 : nth 2 OPS (fun _ => True) = (fun m => sshad asegs (arl_AL R) m slo spv).
  Hypothesis O3 : nth 3 OPS (fun _ => True) = (fun m => sshad asegs (arl_AL R) m SHA SHB).
  Hypothesis L0 : nth 0 LAWS (fun _ _ _ => True) = LAWt R LB LF' spv TOP.
  (* [comment removed for export] *)
  Hypothesis SUBF : forall b, In b LF0 -> In b LF'.
  Hypothesis LE1 : spv <= SP0.
  Hypothesis LE2 : spv <= SSP0.
  Hypothesis LE3 : spv <= SHA.
  Hypothesis LE4 : SHB <= TOP.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00N0@L11328637265.214L12988280733.169L13574840046.214L14575328201.169L20628592539.214L22370296385.214L23849003374.169L2419504615.214 L26575136967.214L28752495968.214L30467899716.214L37291689093.169L42017090660.214L46826984742.214L48571418324.214L49544185813.214L50683335026.214L50691565517.214L5071631467.214 L50955812742.169L53109055006.214L56918115474.169L61137391145.169L61492628162.214L62774773597.169L64234434282.214L65516563957.169L67530929906.214L67588752385.214L8603275937.214 00000h01c02]03W04W05W06j06k07e07f08^09X0:P0;J0<C0<D0=<0>60>o0@W0@X0B@0CO0DG0EB0F;0Gc0Gd0H\0IUS1R3HIA1h3LF'3spv3TOP2PP2TM3LFL2bs3AL13AL24SPR03SPA1y2R1S1R3HIA1h3LF'3spv3TOP2PP2TM3LFL2bs3AL13AL23PP13PP04SPR03SPAS1R3HIA1h3LF'3spv3TOP2PP2TM3LFL2bs3AL13AL24SPR03SPA2mo3R2'S1R3HIA1h3LF'3spv3TOP2PP2TM2lo3LFL2bs3AL13AL24SPR03DS13SPAS1R3HIA1h3LF'3spv3TOP2PP2TM3LFL2bs3END1P3AL13AL24SPR03SPA2p'3Hp'S1R3HIA1h3LF'3spv3TOP2PP2TM3LFL2bs3END1P3AL13AL24SPR03SPA2p'3Hp'S1R3HIA1h3LF'3spv3TOP2PP2TM4BUFg5BLENg3LFL2bs3END4HLEN3BB33AL13AL23PP03TM04SPR03SPAFS1R3HIA1h3LF'3spv3TOP2PP2TM3LFL2bs3AL13AL24SPR03SPA2mo3R2'FS1R3HIA1h3LF'3spv3TOP2PP2TM3LFL2bs3AL13AL24SPR03SPA1r2HrS1R3HIA1h3LF'3spv3TOP2PP2TM2lo3LFL2bs3AL13AL24SPR03DS23SPAS1R3HIA1h3LF'3spv3TOP2PP2TM3LFL2bs3AL13AL24SPR03SPA1y2R1S1R3HIA1h3LF'3spv3TOP2PP2TM3LFL2bs3AL13AL24SPR03SPA2hh3R4'S1R3HIA1h3LF'3spv3TOP2PP2TM3LFL2bs3AL13AL24SPR03SPA2mi2R5FS1R3HIA1h3LF'3spv3TOP2PP2TM3LFL2bs3AL13AL24SPR03SPA1d2R3S1R3HIA1h3LF'3spv3TOP2PP2TM3LFL2bs3AL13AL24SPR03SPA2hh3R4'S1R3HIA1h3LF'3spv3TOP2PP2TM3LFL2bs3AL13AL24SPR03SPA2sc2R6S1R3HIA1h3LF'3spv3TOP2PP2TM4BUFg5BLENg2lo3LFL2bs4HLEN2D42D52D13AL13AL23PP03TM04SLO14SPR03DS13DS23DS43SPAFS1R3HIA1h3LF'3spv3TOP2PP2TM4BUFg5BLENg2lo3LFL2bs4HLEN2D42D52D13AL13AL23PP03TM04SLO14SPR03DS13DS23DS43SPAS1R3HIA1h3LF'3spv3TOP2PP2TM4BUFg5BLENg3LFL2bs4HLEN3BB43AL13AL23PP03TM04SPR03SPAS1R3HIA1h3LF'3spv3TOP2PP2TM3LFL2bs3AL13AL24SPR03SPA1r2HrS1R3HIA1h3LF'3spv3TOP2PP2TM3LFL2bs3AL13AL23TM13TM04SPR03SPAS1R3HIA1h3LF'3spv3TOP2PP2TM3LFL2bs3AL13AL24SPR03SPA2sc2R6S1R3HIA1h3LF'3spv3TOP2PP2TM4BUFg5BLENg2lo3LFL2bs4HLEN2D42D52D13AL13AL23PP03TM04SLO14SPR03DS13DS23DS43SPAFS1R3HIA1h3LF'3spv3TOP2PP2TM3LFL2bs3AL13AL24SPR03SPA1d2R3S1R3HIA1h3LF'3spv3TOP2PP2TM3LFL2bs3AL13AL24SPR03SPA2mi2R5". (* [comment removed for export] *)
  Lemma sum_gettimeA_okL (pc : Z) (kp kt kb kbl klo kslo ksm ktp kspv : nat) (PP TM BUFg BLENg lo : Z) (tp : word) (CS : Z -> Prop) : ltac2:(CDefT.buildp (gd_tbl_LxA_laws ()) "P,(23.$24.VR,VHIA,O11.)P,(25.P,$4.Sp(26.$24.VR,VHIA,Vh,)O1.)P,(25.$4.(27.$4.O10.VGS,=)O7.)P,(25.$4.(27.$4.O?.VGS,=)O6.)P,(25.$4.(27.$4.O>.VGS,=)O5.)P,(25.$4.(27.$4.O=.VGS,=)O4.)P,(25.$4.(27.$4.O<.VGS,=)O3.)P,(25.$4.(27.$4.O;.VGS,=)Vslo,)P,(25.$4.(27.$4.O:.VGS,=)(28.VR,))P,(25.$4.(27.$4.O9.VGS,=)(29.&40.O2.))P,(25.$4.(27.$4.O8.VGS,=)Vspv,)P,(25.(2:.&40.)O2.(2;.&40.(2<.VR,)))P,(2=.(2>.$2?.VLF',)#200.)P,(30.(31.VR,)(32.$2?.VLB,(33.VLF',))O3.O7.+8.)P,(30.(31.VR,)(32.$2?.VLB,(33.VLF',))O3.O6.+18.)P,(30.(31.VR,)(32.$2?.VLB,(33.VLF',))O3.O5.O4.)P,(34.(31.VR,)(32.$2?.VLB,(33.VLF',))O3.(35.$24.VR,VHIA,Vh,)O7.+8.)P,(34.(31.VR,)(32.$2?.VLB,(33.VLF',))O3.(35.$24.VR,VHIA,Vh,)O6.+18.)P,Px,$4.P,(36.VW0,R1.)(36.(2.(3.$4.$4.)(6.$4.$4.O7.(37.O7.+8.))(2.(3.$4.$4.)(6.$4.$4.O6.(37.O6.+18.))(7.(3.$4.$4.))))R2.)(38.$24.(39.VR,)VGS,VOPS,VLAWS,O1.(3:.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.))")
(* [comment removed for export] *).
  Proof.
    intros GT ECS GP GTM GB GBL GLO GSLO GSM GTP GSPV TPV LFL CR1 CR2 CR3 CW1 CW2 XW. subst CS. apply apply_summary_soundL.
    unfold SUM_gettimeA_L, q. lx_sum_unfold.
    intros PPp END TMp P BUF BLEN SPu LO HT SL SLOp NSM TPL TPG A0 A2 SPG bs tmb F fc m.
    intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
    intros [CSOK ALWF] _ MI GDp GDt GDb GDbl GDlo GHT GSL GDslo GDsm GDtp GDspv R10 R11 R12 R2 R4 ST HPP HTM [HBUF HLEN] OPP OTM OBUF.
    intros EA0 EA2 ETP ESP B1 B2 BB3 BB4 D1 D4 D5 AL1 AL2 PP0 PP1 TM0 TM1 BUF0 SLO1 SLO3 NSM0 SLOS SLOL SPA SPTOP SP47 DS1 DS2 DS4 SPR0 SPR1.
    intros OQ0 OQ1 OQ2 OQ3.
    change (PPp = nth kp GS 0) in GDp; change (TMp = nth kt GS 0) in GDt; change (BUF = nth kb GS 0) in GDb; change (BLEN = nth kbl GS 0) in GDbl;
    change (LO = nth klo GS 0) in GDlo; change (HT = nth 1 GS 0) in GHT;
    change (SL = nth 3 GS 0) in GSL; change (SLOp = nth kslo GS 0) in GDslo; change (NSM = nth ksm GS 0) in GDsm; change (TPG = nth ktp GS 0) in GDtp;
    change (SPG = nth kspv GS 0) in GDspv.
    change (nth 0 OPS (fun _ => True) m) in OQ0; change (nth 1 OPS (fun _ => True) m) in OQ1;
    change (nth 2 OPS (fun _ => True) m) in OQ2; change (nth 3 OPS (fun _ => True) m) in OQ3.
    rewrite GP in GDp; rewrite GTM in GDt; rewrite GB in GDb; rewrite GBL in GDbl; rewrite GLO in GDlo; rewrite G1 in GHT; rewrite G3 in GSL;
    rewrite GSLO in GDslo; rewrite GSM in GDsm; rewrite GTP in GDtp; rewrite GSPV in GDspv.
    rewrite O0 in OQ0; rewrite O1 in OQ1; rewrite O2 in OQ2; rewrite O3 in OQ3; cbv beta in OQ0, OQ1, OQ2, OQ3.
    subst PPp TMp LO HT SL SLOp NSM TPG SPG. subst A0 A2 TPL SPu. subst BUF BLEN.
    assert (U2 : bv_unsigned x2 = spv) by (rewrite R2; apply uw64; assumption).
    assert (X4 : x4 = Z_to_bv 64 (arl_tp R)) by (rewrite R4, lx_w64u; exact TPV).
    destruct OQ0 as (hq & HHq & Ecs & Etop & Estk & Ehk & Efl & Evol & Efr).
    destruct (time_of_blob _ _ _ _ HTM) as (y0 & mo0 & d0 & hh0 & mi0 & s00 & HTMc).
    pose proof GT as SP. unfold x509_get_time_stmtA in SP. specialize (SP hq LB LF'). rewrite Ecs, Etop in SP.
    rewrite <- HLEN in CR3, OBUF.
    eapply evtA_cut.
    { eapply (SP x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m PP TM P END BUFg lo slo bs
                y0 mo0 d0 hh0 mi0 s00);
        rewrite ?U2; first [ eassumption | exact X4 | unfold X509_GET_TIME_STACK_A, two64 in *; lia ]. }
    clear SP. cbv beta. intros ms' POST. unfold x509_get_time_postA in POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & h' & r & p' & y & mo & d & hh & mi & sc
                      & -> & HH' & E1 & E2 & E3 & E4 & E5 & E6 & E7 & PA & MI' & ST' & SS' & -> & Hr & HPP' & HTM' & Hp').
    apply evtA_done. rewrite U2 in PA, ST', SS'. unfold time_cells in HTM'.
    pose proof (lx_urange y) as R1. pose proof (lx_urange mo) as R2'. pose proof (lx_urange d) as R3. pose proof (lx_urange hh) as R4'.
    pose proof (lx_urange mi) as R5. pose proof (lx_urange sc) as R6.
    lx_sum_post.
    (* [comment removed for export] *)
    all: try (lazymatch goal with |- ?f 0%nat OPS ?dft ?mm => change (nth 0%nat OPS dft mm); rewrite O0; cbv beta;
              exists h'; split; [exact HH'|]; rewrite E1, E2, E3, E4, E5, E6, Ecs, Etop, Estk, Efl, Evol, Efr;
              split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
              split; [let mo := fresh "mo" in intros mo; rewrite E7; apply Ehk |]; repeat split; reflexivity end).
    all: try (lazymatch goal with |- ?f 1%nat OPS ?dft ?mm => change (nth 1%nat OPS dft mm); rewrite O1; cbv beta;
              eapply (presW_call asegs R HIA h LB LF0 SP0 SSP0 W0 m00 m m' LB LF' spv spv TOP);
              [ exact OQ1 | rewrite Estk in PA; exact PA | let b := fresh "b" in let Hb := fresh "Hb" in intros b Hb; exact Hb
              | exact SUBF | exact LE1 | exact LE2 | apply Z.le_refl | exact XW ] end).
    all: try (lazymatch goal with |- ?f 2%nat OPS ?dft ?mm => change (nth 2%nat OPS dft mm); rewrite O2; cbv beta; exact SS' end).
    all: try (lazymatch goal with |- ?f 3%nat OPS ?dft ?mm => change (nth 3%nat OPS dft mm); rewrite O3; cbv beta;
              eapply (presA_sshad asegs R LB LF' spv spv TOP); [ rewrite Estk in PA; exact PA | exact OQ3 | exact LE3 | exact LE4 ] end).
    all: try (lazymatch goal with |- ?f 0%nat LAWS ?dft ?X ?ma ?mb => change (nth 0%nat LAWS dft X ma mb); rewrite L0; unfold LAWt; rewrite Estk in PA; exact PA end).
    all: try exact MI'.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00P0@L12559207941.212L12988280733.169L13197380316.169L13950517904.212L14575328201.169L18611708242.212L20630219295.212L2188817181.169 L22371950533.212L22617612331.212L23665996118.212L23665996118.213L23849003374.169L2417084515.212 L25253394785.169L28755048676.212L35170103652.216L35170103652.217L37769198911.216L37769198911.217L38059009440.212L41732897654.212L49546738257.212L50711992578.212L53111202714.212L55626533115.212L56918115474.169L61137391145.169L61490100038.212L65516563957.169L67529296758.212L9915722491.212 00000m01i03R04K05F06B07C08>09?0:;0;70<30=G0=H0>D0>E0?S0@a0BM0D90E50F20F30Fo0G00Gl0IU0Je0K^0MG0MH0NDS1R3HIA1h3LF'3spv3TOP2PP3ALG3LFL2bs3AL13AL24SPR03SPA4apad3R2'S1R3HIA1h3LF'3spv3TOP2PP3ALG3LFL2bs3AL13AL23PP13PP04SPR03SPAS1R3HIA1h3LF'3spv3TOP2PP3ALG4BUFg5BLENg2lo3LFL2bs4HLEN2D42D52D13AL13AL23PP03TM04SLO14SPR03DS13DS23DS43SPAS1R3HIA1h3LF'3spv3TOP2PP3ALG3LFL2bs3AL13AL24SPR03SPA1r2HrS1R3HIA1h3LF'3spv3TOP2PP3ALG2lo3LFL2bs3AL13AL24SPR03DS13SPAS1R3HIA1h3LF'3spv3TOP2PP3ALG3LFL2bs3AL13AL24SPR03SPA3apw3R4'S1R3HIA1h3LF'3spv3TOP2PP3ALG3LFL2bs3END1P3AL13AL24SPR03SPA2p'3Hp'S1R3HIA1h3LF'3spv3TOP2PP3ALG2lo3LFL2bs3AL13AL24SPR03DS23SPAS1R3HIA1h3LF'3spv3TOP2PP3ALG3LFL2bs3END1P3AL13AL24SPR03SPA2p'3Hp'S1R3HIA1h3LF'3spv3TOP2PP3ALG3LFL2bs3AL13AL24SPR03SPA3apw3R4'S1R3HIA1h3LF'3spv3TOP2PP3ALG3LFL2bs3AL13AL24SPR03SPA1r2Hr2NES1R3HIA1h3LF'3spv3TOP2PP3ALG3LFL2bs3AL13AL24SPR03SPA1r2Hr2NES1R3HIA1h3LF'3spv3TOP2PP3ALG4BUFg5BLENg3LFL2bs3END4HLEN3BB33AL13AL23PP03TM04SPR03SPAFS1R3HIA1h3LF'3spv3TOP2PP3ALG3LFL2bs3AL13AL23TM13TM04SPR03SPAFS1R3HIA1h3LF'3spv3TOP2PP3ALG4BUFg3LFL2bs3AL13AL23PP03TM04BUF04SPR03SPA2ap4Hap1S1R3HIA1h3LF'3spv3TOP2PP3ALG4BUFg3LFL2bs3AL13AL23PP03TM04BUF04SPR03SPA2ap4Hap1S1R3HIA1h3LF'3spv3TOP2PP3ALG4BUFg5BLENg3LFL2bs3END1P3BB33BB43AL13AL23PP03TM04SPR03SPA2p'4alen3Hp'2R32ap4Hap2S1R3HIA1h3LF'3spv3TOP2PP3ALG4BUFg5BLENg3LFL2bs3END1P3BB33BB43AL13AL23PP03TM04SPR03SPA2p'4alen3Hp'2R32ap4Hap2S1R3HIA1h3LF'3spv3TOP2PP3ALG3LFL2bs3AL13AL24SPR03SPA4alen2R3S1R3HIA1h3LF'3spv3TOP2PP3ALG3LFL2bs3AL13AL24SPR03SPA4apad3R2'FS1R3HIA1h3LF'3spv3TOP2PP3ALG3LFL2bs3AL13AL24SPR03SPA4atag2R1FS1R3HIA1h3LF'3spv3TOP2PP3ALG3LFL2bs3AL13AL24SPR03SPA4atag2R1S1R3HIA1h3LF'3spv3TOP2PP3ALG4BUFg5BLENg2lo3LFL2bs4HLEN2D42D52D13AL13AL23PP03TM04SLO14SPR03DS13DS23DS43SPAS1R3HIA1h3LF'3spv3TOP2PP3ALG4BUFg5BLENg3LFL2bs4HLEN3BB43AL13AL23PP03TM04SPR03SPAS1R3HIA1h3LF'3spv3TOP2PP3ALG3LFL2bs3AL13AL24SPR03SPA1r2HrS1R3HIA1h3LF'3spv3TOP2PP3ALG4BUFg5BLENg2lo3LFL2bs4HLEN2D42D52D13AL13AL23PP03TM04SLO14SPR03DS13DS23DS43SPAFS1R3HIA1h3LF'3spv3TOP2PP3ALG3LFL2bs3AL13AL24SPR03SPA4alen2R3". (* [comment removed for export] *)
  Lemma sum_algnullA_okL (pc : Z) (kp ka kb kbl klo kslo ksm ktp kspv kam : nat) (PP ALG BUFg BLENg lo : Z) (tp : word) (CS : Z -> Prop) : ltac2:(CDefT.buildp (gd_tbl_LxA_laws ()) "P,(3;.$24.VR,VHIA,O12.)P,(25.P,$4.Sp(26.$24.VR,VHIA,Vh,)O1.)P,(25.$4.(27.$4.O11.VGS,=)O7.)P,(25.$4.(27.$4.O10.VGS,=)O6.)P,(25.$4.(27.$4.O?.VGS,=)O5.)P,(25.$4.(27.$4.O>.VGS,=)O4.)P,(25.$4.(27.$4.O=.VGS,=)O3.)P,(25.$4.(27.$4.O<.VGS,=)Vslo,)P,(25.$4.(27.$4.O;.VGS,=)(28.VR,))P,(25.$4.(27.$4.O:.VGS,=)(29.&40.O2.))P,(25.$4.(27.$4.O9.VGS,=)Vspv,)P,(25.$4.(27.$4.O8.VGS,=)(3<.VR,))P,(25.(2:.&40.)O2.(2;.&40.(2<.VR,)))P,(2=.(2>.$2?.VLF',)#200.)P,(30.(31.VR,)(32.$2?.VLB,(33.VLF',))O3.O7.+8.)P,(30.(31.VR,)(32.$2?.VLB,(33.VLF',))O3.O6.+18.)P,(30.(31.VR,)(32.$2?.VLB,(33.VLF',))O3.O5.O4.)P,(34.(31.VR,)(32.$2?.VLB,(33.VLF',))O3.(35.$24.VR,VHIA,Vh,)O7.+8.)P,(34.(31.VR,)(32.$2?.VLB,(33.VLF',))O3.(35.$24.VR,VHIA,Vh,)O6.+18.)P,Px,$4.P,(36.VW0,R1.)(36.(2.(3.$4.$4.)(6.$4.$4.O7.(37.O7.+8.))(2.(3.$4.$4.)(6.$4.$4.O6.(37.O6.+18.))(7.(3.$4.$4.))))R2.)(38.$24.(39.VR,)VGS,VOPS,VLAWS,O1.(3=.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.))")
(* [comment removed for export] *).
  Proof.
    intros GT ECS GP GTM GB GBL GLO GSLO GSM GTP GSPV GAM TPV LFL CR1 CR2 CR3 CW1 CW2 XW. subst CS. apply apply_summary_soundL.
    unfold SUM_algnullA_L, q. lx_sum_unfold.
    intros PPp END TMp P BUF BLEN SPu LO HT SL SLOp NSM TPL TPG A0 A2 SPG NAM otg opd oln opw bs F fc m.
    intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
    intros [CSOK ALWF] _ MI GDp GDt GDb GDbl GDlo GHT GSL GDslo GDsm GDtp GDspv GDam R10 R11 R12 R2 R4 ST HPP HTM [HBUF HLEN] OPP OTM OBUF.
    intros EA0 EA2 ETP ESP B1 B2 BB3 BB4 D1 D4 D5 AL1 AL2 PP0 PP1 TM0 TM1 BUF0 SLO1 SLO2 SLO3 NAM0 NSM0 SLOS SLOL SPA SPTOP SP47 DS1 DS2 DS4 SPR0 SPR1.
    intros OQ0 OQ1 OQ2 OQ3.
    change (PPp = nth kp GS 0) in GDp; change (TMp = nth ka GS 0) in GDt; change (BUF = nth kb GS 0) in GDb; change (BLEN = nth kbl GS 0) in GDbl;
    change (LO = nth klo GS 0) in GDlo; change (HT = nth 1 GS 0) in GHT;
    change (SL = nth 3 GS 0) in GSL; change (SLOp = nth kslo GS 0) in GDslo; change (NSM = nth ksm GS 0) in GDsm; change (TPG = nth ktp GS 0) in GDtp;
    change (SPG = nth kspv GS 0) in GDspv; change (NAM = nth kam GS 0) in GDam.
    change (nth 0 OPS (fun _ => True) m) in OQ0; change (nth 1 OPS (fun _ => True) m) in OQ1;
    change (nth 2 OPS (fun _ => True) m) in OQ2; change (nth 3 OPS (fun _ => True) m) in OQ3.
    rewrite GP in GDp; rewrite GTM in GDt; rewrite GB in GDb; rewrite GBL in GDbl; rewrite GLO in GDlo; rewrite G1 in GHT; rewrite G3 in GSL;
    rewrite GSLO in GDslo; rewrite GSM in GDsm; rewrite GTP in GDtp; rewrite GSPV in GDspv; rewrite GAM in GDam.
    rewrite O0 in OQ0; rewrite O1 in OQ1; rewrite O2 in OQ2; rewrite O3 in OQ3; cbv beta in OQ0, OQ1, OQ2, OQ3.
    subst PPp TMp LO HT SL SLOp NSM TPG SPG NAM. subst A0 A2 TPL SPu. subst BUF BLEN.
    assert (U2 : bv_unsigned x2 = spv) by (rewrite R2; apply uw64; assumption).
    assert (X4 : x4 = Z_to_bv 64 (arl_tp R)) by (rewrite R4, lx_w64u; exact TPV).
    destruct OQ0 as (hq & HHq & Ecs & Etop & Estk & Ehk & Efl & Evol & Efr).
    pose proof GT as SP. unfold asn1_get_alg_null_stmtA in SP. specialize (SP hq LB LF'). rewrite Ecs, Etop in SP.
    rewrite <- HLEN in CR3, OBUF.
    eapply evtA_cut.
    { eapply (SP x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m PP ALG P END BUFg lo slo bs
                (Z_to_bv 64 otg) (Z_to_bv 64 opd) (Z_to_bv 64 oln) (Z_to_bv 64 opw));
        rewrite ?U2; first [ eassumption | exact X4 | unfold ASN1_GET_ALG_NULL_STACK_A, two64 in *; lia ]. }
    clear SP. cbv beta. intros ms' POST. unfold asn1_get_alg_null_postA in POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & h' & r & p' & atag & apad & alen & apw
                      & -> & HH' & E1 & E2 & E3 & E4 & E5 & E6 & E7 & PA & MI' & ST' & SS' & -> & Hr & HPP' & HALG' & Hp' & HOK).
    apply evtA_done. rewrite U2 in PA, ST', SS'.
    pose proof (lx_urange atag) as R1. pose proof (lx_urange apad) as R2'. pose proof (lx_urange alen) as R3. pose proof (lx_urange apw) as R4'.
    (* [comment removed for export] *)
    assert (OK1 : r + 1 <= 0 \/ BUFg <= bv_unsigned apw).
    { destruct (Z.eq_dec r 0) as [E|NE]; [right | left; lia]. destruct (HOK E) as (ap & Eap & Hap1 & Hap2).
      rewrite Eap, uw64; [exact Hap1 | lia | unfold two64; lia]. }
    assert (OK2 : r + 1 <= 0 \/ bv_unsigned apw + bv_unsigned alen <= p').
    { destruct (Z.eq_dec r 0) as [E|NE]; [right | left; lia]. destruct (HOK E) as (ap & Eap & Hap1 & Hap2).
      rewrite Eap, uw64; [exact Hap2 | lia | unfold two64; lia]. }
    clear HOK.
    lx_sum_post.
    all: try (lazymatch goal with |- ?f 0%nat OPS ?dft ?mm => change (nth 0%nat OPS dft mm); rewrite O0; cbv beta;
              exists h'; split; [exact HH'|]; rewrite E1, E2, E3, E4, E5, E6, Ecs, Etop, Estk, Efl, Evol, Efr;
              split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
              split; [let mo := fresh "mo" in intros mo; rewrite E7; apply Ehk |]; repeat split; reflexivity end).
    all: try (lazymatch goal with |- ?f 1%nat OPS ?dft ?mm => change (nth 1%nat OPS dft mm); rewrite O1; cbv beta;
              eapply (presW_call asegs R HIA h LB LF0 SP0 SSP0 W0 m00 m m' LB LF' spv spv TOP);
              [ exact OQ1 | rewrite Estk in PA; exact PA | let b := fresh "b" in let Hb := fresh "Hb" in intros b Hb; exact Hb
              | exact SUBF | exact LE1 | exact LE2 | apply Z.le_refl | exact XW ] end).
    all: try (lazymatch goal with |- ?f 2%nat OPS ?dft ?mm => change (nth 2%nat OPS dft mm); rewrite O2; cbv beta; exact SS' end).
    all: try (lazymatch goal with |- ?f 3%nat OPS ?dft ?mm => change (nth 3%nat OPS dft mm); rewrite O3; cbv beta;
              eapply (presA_sshad asegs R LB LF' spv spv TOP); [ rewrite Estk in PA; exact PA | exact OQ3 | exact LE3 | exact LE4 ] end).
    all: try (lazymatch goal with |- ?f 0%nat LAWS ?dft ?X ?ma ?mb => change (nth 0%nat LAWS dft X ma mb); rewrite L0; unfold LAWt; rewrite Estk in PA; exact PA end).
    all: try exact MI'.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End SLAW.

(* [comment removed for export] *)
Ltac lxa_nth := cbn [List.nth].
Ltac lxa_side_le := lxa_nth; first [ assumption | lxr_lia | lia ].
Ltac lxa_sum1L :=
  lazymatch goal with
  | |- summary_okL _ _ _ _ _ _ (SUM_gettimeA_L _ _ _ _ _ _ _ _ _ _) =>
      eapply sum_gettimeA_okL;
      [> reflexivity | reflexivity                                   (* [comment removed for export] *)
       | reflexivity | reflexivity | reflexivity | reflexivity       (* [comment removed for export] *)
       | reflexivity                                                 (* [comment removed for export] *)
       | let b := fresh "b" in let Hb := fresh "Hb" in intros b Hb; first [ exact Hb | right; exact Hb | right; right; exact Hb ]   (* [comment removed for export] *)
       | lxa_side_le | lxa_side_le | lxa_side_le | lxa_side_le       (* [comment removed for export] *)
       | assumption                                                  (* [comment removed for export] *)
       | lxa_ecs
       | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity   (* [comment removed for export] *)
       | assumption                                                  (* [comment removed for export] *)
       | lxa_nth; first [ assumption | cbn [length] in *; lia ]      (* [comment removed for export] *)
       | lxa_nth; solve_client_range | lxa_nth; solve_client_range | lxa_nth; solve_client_range
       | lxa_cw | lxa_cw
       | lxa_nth; solve_outside_incl ]
  | |- summary_okL _ _ _ _ _ _ (SUM_algnullA_L _ _ _ _ _ _ _ _ _ _ _) =>
      eapply sum_algnullA_okL;
      [> reflexivity | reflexivity                                   (* [comment removed for export] *)
       | reflexivity | reflexivity | reflexivity | reflexivity       (* [comment removed for export] *)
       | reflexivity                                                 (* [comment removed for export] *)
       | let b := fresh "b" in let Hb := fresh "Hb" in intros b Hb; first [ exact Hb | right; exact Hb | right; right; exact Hb ]   (* [comment removed for export] *)
       | lxa_side_le | lxa_side_le | lxa_side_le | lxa_side_le       (* [comment removed for export] *)
       | assumption                                                  (* [comment removed for export] *)
       | lxa_ecs
       | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity   (* [comment removed for export] *)
       | assumption                                                  (* [comment removed for export] *)
       | lxa_nth; first [ assumption | cbn [length] in *; lia ]      (* [comment removed for export] *)
       | lxa_nth; solve_client_range | lxa_nth; solve_client_range | lxa_nth; solve_client_range
       | lxa_cw | lxa_cw
       | lxa_nth; solve_outside_incl ]
  | |- summary_okL _ _ _ _ _ _ _ => apply summary_okO_L; lxa_sum1
  end.
Ltac lxa_sumsL L GS OPS LAWS :=
  lazymatch goal with |- evtA ?segs ?AL ?CS _ _ =>
    let H := fresh "LXSUMS" in
    assert (H : List.Forall (summary_okL segs AL GS OPS LAWS CS) L) by (repeat (apply List.Forall_cons; [ lxa_sum1L | ]); apply List.Forall_nil)
  end.
Ltac lxa_auto_law SUMS OBJS :=
  lx_rw_merge;
  let mx := lazymatch goal with |- context [MS _ _ _ _ _ ?mx (seg_rom _)] => mx end in
  (* [comment removed for export] *)
  try match goal with H : lx_opq _ _ _ (fun m => HM _ _ _ _ _ _ m) _ _ mx |- _ => clear H end;
  lxr_pose_HMQ;
  lazymatch goal with
  | HQ : lx_opq ?segs ?AL ?CS (fun m => HMQ ?R ?HIA ?h ?LB ?LF' m) _ _ mx |- evtA _ _ _ _ (MS (mkR _ (Z_to_bv 64 ?spv) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      let TOP := constr:(hstkhi segs R HIA h) in
      let LAW := constr:(LAWt R LB LF' spv TOP) in
      lxr_law_tags LAW;
      let hmP := constr:(fun m => HMQ R HIA h LB LF' m) in
      let prP := lazymatch goal with H : lx_opq _ _ _ (fun m => presW ?sg ?R' ?HIA' ?h' ?LB0 ?LF0 ?SP ?SSP ?W ?m0 m) _ _ mx |- _ =>
                   constr:(fun m => presW sg R' HIA' h' LB0 LF0 SP SSP W m0 m)
                 | |- _ => fail 0 "lxa_auto_law: no presW fact at the goal memory" end in
      let sloP := lazymatch goal with H : lx_opq _ _ _ (fun m => sshad ?sg ?al m ?a spv) _ _ mx |- _ => constr:(fun m => sshad sg al m a spv)
                 | |- _ => fail 0 "lxa_auto_law: no sshad _ spv fact (the callee's poison window)" end in
      let shiP := match goal with
                  | H : lx_opq _ _ _ (fun m => sshad ?sg ?al m ?a ?b) _ _ mx |- _ =>
                      lazymatch b with spv => fail | _ => constr:(fun m => sshad sg al m a b) end
                  | _ => sloP end in
      let OPS := constr:(hmP :: prP :: sloP :: shiP :: nil) in
      let LAWS := constr:(LAW :: nil) in
      let GS := constr:(alloc_ceiling :: htop segs R HIA h :: arl_need_amem R :: arl_stklo R :: OBJS) in
      lxa_sumsL SUMS GS OPS LAWS
  | |- _ => fail "lxa_auto_law: expected the HMQ fact and sp = Z_to_bv 64 spv"
  end.
