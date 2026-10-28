(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_asn1_get_tag P_asn1_get_len P_asn1_get_bitstring P_oid P_asn1_get_mpi.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgGlobals A_asn1_get_len LxConv_getlen A_asn1_get_tag_stmt A_asn1_get_tag A_asn1_get_bool A_asn1_get_int_loops A_asn1_get_int A_asn1_get_bitstring_null A_asn1_get_bitstring.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_rt_facts A_asn1_get_alg_A A_oid.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface Arr CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxSum LxSoundSum.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt.
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
Ltac2 gd_tbl_LxA_sums () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.LX.LxSum.SUM"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Numbers.BinNums.positive"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.mfact"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.MRw"; "q"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.cellx"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.XZ"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.MAobj"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.ELit"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.MRo"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.pfact"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FLe"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.EAdd"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FLt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FSep"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FSep0"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FAl"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.EZv"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FCr"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.EMulC"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.two64"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.expr"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.MStk"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FOr2"; "RocqVerifyHarness.AgentSubmission.LX.LxSum.SUMG"; "Corelib.Init.Datatypes.nat"; "Corelib.Lists.ListDef.Forall"; "RocqVerifyHarness.AgentSubmission.LX.LxSum.summary"; "RocqVerifyHarness.AgentSubmission.LX.LxSoundSum.summary_okG"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "SUM_getlenA"; "SUM_gettagA"; "SUM_getboolA"; "SUM_getintA"; "SUM_bitstrnullA"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.XB"; "lxz1"; "RocqVerifyHarness.AgentSubmission.LX.LxSum.SUMX"; "Corelib.Init.Datatypes.None"; "Stdlib.ZArith.BinInt.Z.of_N"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FEq"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.XRep"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FOr3z"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "Corelib.Lists.ListDef.nth"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LX.LxSoundSum.summary_okO"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "SUM_amemsetA"; "SUM_amemset0A"; "lxz4"; "lxz8"; "lxbs0"; "SUM_getalgA"; "RocqVerifyHarness.AgentSubmission.B.A_oid.oid_lookup1_stmtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_bcmp"; "SUM_oidlook1A"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FProp"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_memcmp_i"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.True"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Corelib.Init.Datatypes.list"; "bcmp_prop"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.Lib.Image.ro_bytes_b"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "RocqVerifyHarness.AgentSubmission.B.AImgGlobals.img_cs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.B.AImgGlobals.img_shadow_ok"; "RocqVerifyHarness.AgentSubmission.B.AImgGlobals.img_norz"; "RocqVerifyHarness.AgentSubmission.LX.LxSoundSum.summary_okP"; "SUM_bcmpA"; "SUM_bcmp0A"].


Definition q (i : positive) : expr := EZv i.
Notation "a .+ b" := (EAdd a b) (at level 50, left associativity).
Notation "a .- b" := (EAdd a (EMulC (-1) b)) (at level 50, left associativity).

Notation SUM_getlenA := LxConv_getlen.SUM_getlenA (only parsing).

(* [comment removed for export] *)
Definition SUM_gettagA : summary := ltac2:(CDefT.buildp (gd_tbl_LxA_sums ()) "(0.+9990<.$1.#;.#11.#1.(2.(3.$4.$5.)(6.$4.$5.+:.^1.)(2.(3.$4.$5.)(6.$4.$5.+;.^2.)(2.(3.$4.$5.)(6.$4.$5.+<.^3.)(2.(3.$4.$5.)(6.$4.$5.+=.^;.)(2.(3.$4.$5.)(6.$4.$5.+2.^7.)(7.(3.$4.$5.)))))))(8.$5.^9.)(2.$9.(:.(;.^1.)(2.$<.(=.&8.(;.^4.))(7.$<.)))(2.$9.(:.(;.^3.)(2.$<.(=.&8.(;.^:.))(7.$<.)))(7.$9.)))(8.(3.$5.$5.)(6.$5.$5.^8.^7.))(2.(3.(3.$5.$5.)$5.)(6.(3.$5.$5.)$5.(6.$5.$5.^5.^6.)^1.)(7.(3.(3.$5.$5.)$5.)))(2.$9.(>.(;.^1.)(?.+8.))(2.$9.(>.(;.^3.)(?.+8.))(2.$9.(>.(;.^5.)(;.^6.))(2.$9.(10.(?.+?5>50.)(2.$<.(=.&8.(?.+1099?8.))(7.$<.)))(2.$9.(10.(?.+1099?8.)(2.$<.(=.&8.(;.^9.))(7.$<.)))(7.$9.))))))(2.$11.(12.(;.^5.)(;.^4.))(2.$11.(12.(;.^4.)(;.^2.))(2.$11.(12.(;.^2.)(13.(;.^5.)(;.^6.)))(2.$11.(14.(13.(;.^5.)(;.^6.))(?.(15.+2.+3?.)))(2.$11.(16.(;.^1.)(?.+8.)(;.^3.)(?.+8.))(2.$11.(17.(;.^6.)(;.^1.)(?.+8.)(;.^5.)(;.^6.))(2.$11.(17.(;.^6.)(;.^3.)(?.+8.)(;.^5.)(;.^6.))(2.$11.(18.(19.^1.)&3.)(2.$11.(18.(19.^3.)&3.)(2.$11.(14.(?.=)(;.^1.))(2.$11.(14.(?.=)(;.^3.))(2.$11.(14.(?.=)(;.^5.))(2.$11.(12.(;.^8.)(13.(;.^7.)(?.-10.)))(2.$11.(18.(19.^7.)&4.)(2.$11.(1:.(;.^8.)(13.(;.^7.)(1;.-1.(;.^8.))))(2.$11.(16.(;.^1.)(?.+8.)(13.(;.^7.)(?.-10.))(?.+10.))(2.$11.(16.(;.^3.)(?.+8.)(13.(;.^7.)(?.-10.))(?.+10.))(2.$11.(17.(;.^6.)(;.^5.)(;.^6.)(13.(;.^7.)(?.-10.))(?.+10.))(2.$11.(12.(?.=)(;.^7.))(2.$11.(12.(;.^7.)(?.(1<.$1=.+1.)))(7.$11.)))))))))))))))))))))(2.(3.$1>.$1>.)(6.$1>.$1>.(;.^1.)(13.(;.^1.)(?.+8.)))(2.(3.$1>.$1>.)(6.$1>.$1>.(;.^3.)(13.(;.^3.)(?.+8.)))(2.(3.$1>.$1>.)(6.$1>.$1>.(13.(;.^7.)(?.-10.))(;.^7.))(7.(3.$1>.$1>.)))))(2.(3.$4.$5.)(6.$4.$5.+:.^<.)(2.(3.$4.$5.)(6.$4.$5.+5.^?.)(2.(3.$4.$5.)(6.$4.$5.+6.^10.)(2.(3.$4.$5.)(6.$4.$5.+7.^11.)(2.(3.$4.$5.)(6.$4.$5.+;.^12.)(2.(3.$4.$5.)(6.$4.$5.+<.^13.)(2.(3.$4.$5.)(6.$4.$5.+=.^14.)(2.(3.$4.$5.)(6.$4.$5.+>.^15.)(2.(3.$4.$5.)(6.$4.$5.+?.^16.)(2.(3.$4.$5.)(6.$4.$5.+10.^17.)(2.(3.$4.$5.)(6.$4.$5.+11.^18.)(2.(3.$4.$5.)(6.$4.$5.+1<.^19.)(2.(3.$4.$5.)(6.$4.$5.+1=.^1:.)(2.(3.$4.$5.)(6.$4.$5.+1>.^1;.)(2.(3.$4.$5.)(6.$4.$5.+1?.^1<.)(7.(3.$4.$5.)))))))))))))))))(2.$9.(:.(;.^1.)(2.$<.(=.&8.(;.^=.))(7.$<.)))(2.$9.(:.(;.^3.)(2.$<.(=.&8.(;.^>.))(7.$<.)))(2.$9.(1?.(;.^8.)(;.^7.))(7.$9.))))(2.$11.(14.(?.-7?.)(;.^<.))(2.$11.(12.(;.^<.)(?.=))(2.$11.(12.(;.^4.)(;.^=.))(2.$11.(12.(;.^=.)(;.^2.))(2.$11.(20.(13.(;.^<.)(?.+1.))(?.=)(13.(;.^4.)(?.+2.))(;.^=.))(2.$11.(20.(13.(;.^<.)(?.+1.))(?.=)(;.^>.)(13.(;.^2.)(1;.-1.(;.^=.))))(2.$11.(12.(?.=)(;.^>.))(2.$11.(12.(;.^>.)(?.(1<.$1=.+1.)))(7.$11.))))))))))")
(* [comment removed for export] *).


(* [comment removed for export] *)
Definition SUM_valp4A (pc : Z) : summary := ltac2:(CDefT.buildp (gd_tbl_LxA_sums ()) "(21.O1.$1.#;.#11.#1.(2.(3.$4.$5.)(6.$4.$5.+:.^1.)(2.(3.$4.$5.)(6.$4.$5.+;.^2.)(2.(3.$4.$5.)(6.$4.$5.+<.^3.)(2.(3.$4.$5.)(6.$4.$5.+2.^7.)(7.(3.$4.$5.))))))(2.(3.$5.$22.)(6.$5.$22.^;.#0.)(7.(3.$5.$22.)))(8.$5.^9.)(2.$9.(:.(;.^1.)(2.$<.(=.&8.(;.^4.))(7.$<.)))(2.$9.(:.(;.^3.)(2.$<.(=.&4.(;.^:.))(7.$<.)))(7.$9.)))(8.(3.$5.$5.)(6.$5.$5.^8.^7.))(2.(3.(3.$5.$5.)$5.)(6.(3.$5.$5.)$5.(6.$5.$5.^5.^6.)^1.)(7.(3.(3.$5.$5.)$5.)))(2.$9.(>.(;.^1.)(?.+8.))(2.$9.(>.(;.^3.)(?.+4.))(2.$9.(>.(;.^5.)(;.^6.))(2.$9.(>.(13.(;.^7.)(?.-30.))(?.+8.))(2.$9.(10.(?.+?5>50.)(2.$<.(=.&8.(?.+1099?8.))(7.$<.)))(2.$9.(10.(?.+1099?8.)(2.$<.(=.&8.(;.^9.))(7.$<.)))(7.$9.)))))))(2.$11.(12.(;.^5.)(;.^4.))(2.$11.(12.(;.^4.)(;.^2.))(2.$11.(12.(;.^2.)(13.(;.^5.)(;.^6.)))(2.$11.(14.(13.(;.^5.)(;.^6.))(?.(15.+2.+3?.)))(2.$11.(16.(;.^1.)(?.+8.)(;.^3.)(?.+4.))(2.$11.(17.(;.^6.)(;.^1.)(?.+8.)(;.^5.)(;.^6.))(2.$11.(17.(;.^6.)(;.^3.)(?.+4.)(;.^5.)(;.^6.))(2.$11.(18.(19.^1.)&3.)(2.$11.(18.(19.^3.)&2.)(2.$11.(14.(?.=)(;.^1.))(2.$11.(14.(?.=)(;.^3.))(2.$11.(14.(?.=)(;.^5.))(2.$11.(12.(;.^8.)(13.(;.^7.)(?.-40.)))(2.$11.(12.(;.^;.)(;.^8.))(2.$11.(18.(19.^7.)&4.)(2.$11.(16.(;.^1.)(?.+8.)(;.^8.)(13.(;.^7.)(1;.-1.(;.^8.))))(2.$11.(16.(;.^3.)(?.+4.)(;.^8.)(13.(;.^7.)(1;.-1.(;.^8.))))(2.$11.(17.(;.^6.)(;.^5.)(;.^6.)(;.^8.)(13.(;.^7.)(1;.-1.(;.^8.))))(2.$11.(1:.(;.^8.)(13.(;.^7.)(1;.-1.(;.^8.))))(2.$11.(12.(?.=)(;.^7.))(2.$11.(12.(;.^7.)(?.(1<.$1=.+1.)))(7.$11.))))))))))))))))))))))(2.(3.$1>.$1>.)(6.$1>.$1>.(;.^1.)(13.(;.^1.)(?.+8.)))(2.(3.$1>.$1>.)(6.$1>.$1>.(;.^3.)(13.(;.^3.)(?.+4.)))(2.(3.$1>.$1>.)(6.$1>.$1>.(13.(;.^7.)(?.-40.))(;.^7.))(7.(3.$1>.$1>.)))))(2.(3.$4.$5.)(6.$4.$5.+:.^<.)(2.(3.$4.$5.)(6.$4.$5.+5.^?.)(2.(3.$4.$5.)(6.$4.$5.+6.^10.)(2.(3.$4.$5.)(6.$4.$5.+7.^11.)(2.(3.$4.$5.)(6.$4.$5.+;.^12.)(2.(3.$4.$5.)(6.$4.$5.+<.^13.)(2.(3.$4.$5.)(6.$4.$5.+=.^14.)(2.(3.$4.$5.)(6.$4.$5.+>.^15.)(2.(3.$4.$5.)(6.$4.$5.+?.^16.)(2.(3.$4.$5.)(6.$4.$5.+10.^17.)(2.(3.$4.$5.)(6.$4.$5.+11.^18.)(2.(3.$4.$5.)(6.$4.$5.+1<.^19.)(2.(3.$4.$5.)(6.$4.$5.+1=.^1:.)(2.(3.$4.$5.)(6.$4.$5.+1>.^1;.)(2.(3.$4.$5.)(6.$4.$5.+1?.^1<.)(7.(3.$4.$5.)))))))))))))))))(2.$9.(:.(;.^1.)(2.$<.(=.&8.(;.^=.))(7.$<.)))(2.$9.(:.(;.^3.)(2.$<.(=.&4.(;.^>.))(7.$<.)))(2.$9.(1?.(;.^8.)(;.^7.))(7.$9.))))(2.$11.(14.(?.-7?.)(;.^<.))(2.$11.(12.(;.^<.)(?.=))(2.$11.(12.(;.^4.)(;.^=.))(2.$11.(12.(;.^=.)(;.^2.))(2.$11.(20.(13.(;.^<.)(?.+1.))(?.=)(13.(;.^4.)(?.+3.))(;.^=.))(2.$11.(12.(?.=)(;.^>.))(2.$11.(12.(;.^>.)(?.(1<.$1=.+1.)))(7.$11.)))))))))")
(* [comment removed for export] *).
Definition SUM_getboolA : summary := SUM_valp4A 0x999bc.
Definition SUM_getintA : summary := SUM_valp4A 0x99b4c.

(* [comment removed for export] *)
Definition SUM_bitstrnullA : summary := ltac2:(CDefT.buildp (gd_tbl_LxA_sums ()) "(21.+9:45<.$1.#;.#11.#1.(2.(3.$4.$5.)(6.$4.$5.+:.^1.)(2.(3.$4.$5.)(6.$4.$5.+;.^2.)(2.(3.$4.$5.)(6.$4.$5.+<.^3.)(2.(3.$4.$5.)(6.$4.$5.+2.^7.)(7.(3.$4.$5.))))))(2.(3.$5.$22.)(6.$5.$22.^;.#0.)(7.(3.$5.$22.)))(8.$5.^9.)(2.$9.(:.(;.^1.)(2.$<.(=.&8.(;.^4.))(7.$<.)))(2.$9.(:.(;.^3.)(2.$<.(=.&8.(;.^:.))(7.$<.)))(7.$9.)))(8.(3.$5.$5.)(6.$5.$5.^8.^7.))(2.(3.(3.$5.$5.)$5.)(6.(3.$5.$5.)$5.(6.$5.$5.^5.^6.)^1.)(7.(3.(3.$5.$5.)$5.)))(2.$9.(>.(;.^1.)(?.+8.))(2.$9.(>.(;.^3.)(?.+8.))(2.$9.(>.(;.^5.)(;.^6.))(2.$9.(10.(?.+?5>50.)(2.$<.(=.&8.(?.+1099?8.))(7.$<.)))(2.$9.(10.(?.+1099?8.)(2.$<.(=.&8.(;.^9.))(7.$<.)))(7.$9.))))))(2.$11.(12.(;.^5.)(;.^4.))(2.$11.(12.(;.^4.)(;.^2.))(2.$11.(12.(;.^2.)(13.(;.^5.)(;.^6.)))(2.$11.(14.(13.(;.^5.)(;.^6.))(?.(15.+2.+3?.)))(2.$11.(16.(;.^1.)(?.+8.)(;.^3.)(?.+8.))(2.$11.(17.(;.^6.)(;.^1.)(?.+8.)(;.^5.)(;.^6.))(2.$11.(17.(;.^6.)(;.^3.)(?.+8.)(;.^5.)(;.^6.))(2.$11.(18.(19.^1.)&3.)(2.$11.(18.(19.^3.)&3.)(2.$11.(14.(?.=)(;.^1.))(2.$11.(14.(?.=)(;.^3.))(2.$11.(14.(?.=)(;.^5.))(2.$11.(12.(;.^8.)(13.(;.^7.)(?.-40.)))(2.$11.(12.(;.^;.)(;.^8.))(2.$11.(18.(19.^7.)&4.)(2.$11.(16.(;.^1.)(?.+8.)(;.^8.)(13.(;.^7.)(1;.-1.(;.^8.))))(2.$11.(16.(;.^3.)(?.+8.)(;.^8.)(13.(;.^7.)(1;.-1.(;.^8.))))(2.$11.(17.(;.^6.)(;.^5.)(;.^6.)(;.^8.)(13.(;.^7.)(1;.-1.(;.^8.))))(2.$11.(1:.(;.^8.)(13.(;.^7.)(1;.-1.(;.^8.))))(2.$11.(12.(?.=)(;.^7.))(2.$11.(12.(;.^7.)(?.(1<.$1=.+1.)))(7.$11.))))))))))))))))))))))(2.(3.$1>.$1>.)(6.$1>.$1>.(;.^1.)(13.(;.^1.)(?.+8.)))(2.(3.$1>.$1>.)(6.$1>.$1>.(;.^3.)(13.(;.^3.)(?.+8.)))(2.(3.$1>.$1>.)(6.$1>.$1>.(13.(;.^7.)(?.-40.))(;.^7.))(7.(3.$1>.$1>.)))))(2.(3.$4.$5.)(6.$4.$5.+:.^<.)(2.(3.$4.$5.)(6.$4.$5.+5.^?.)(2.(3.$4.$5.)(6.$4.$5.+6.^10.)(2.(3.$4.$5.)(6.$4.$5.+7.^11.)(2.(3.$4.$5.)(6.$4.$5.+;.^12.)(2.(3.$4.$5.)(6.$4.$5.+<.^13.)(2.(3.$4.$5.)(6.$4.$5.+=.^14.)(2.(3.$4.$5.)(6.$4.$5.+>.^15.)(2.(3.$4.$5.)(6.$4.$5.+?.^16.)(2.(3.$4.$5.)(6.$4.$5.+10.^17.)(2.(3.$4.$5.)(6.$4.$5.+11.^18.)(2.(3.$4.$5.)(6.$4.$5.+1<.^19.)(2.(3.$4.$5.)(6.$4.$5.+1=.^1:.)(2.(3.$4.$5.)(6.$4.$5.+1>.^1;.)(2.(3.$4.$5.)(6.$4.$5.+1?.^1<.)(7.(3.$4.$5.)))))))))))))))))(2.$9.(:.(;.^1.)(2.$<.(=.&8.(;.^=.))(7.$<.)))(2.$9.(:.(;.^3.)(2.$<.(=.&8.(;.^>.))(7.$<.)))(2.$9.(1?.(;.^8.)(;.^7.))(7.$9.))))(2.$11.(14.(?.-7?.)(;.^<.))(2.$11.(12.(;.^<.)(?.=))(2.$11.(12.(;.^4.)(;.^=.))(2.$11.(12.(;.^=.)(;.^2.))(2.$11.(20.(13.(;.^<.)(?.+1.))(?.=)(13.(;.^4.)(?.+3.))(;.^=.))(2.$11.(20.(13.(;.^<.)(?.+1.))(?.=)(;.^>.)(13.(;.^2.)(1;.-1.(;.^=.))))(2.$11.(12.(?.=)(;.^>.))(2.$11.(12.(;.^>.)(?.(1<.$1=.+1.)))(7.$11.))))))))))")
(* [comment removed for export] *).

Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L38557627424.3000009S1z2H12H2". (* [comment removed for export] *)
Lemma uw64 : forall z, 0 <= z -> z <= two64 - 1 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z H1 H2. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus, two64 in *. cbn in *. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section S.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00<0@L12066857909.95 L13952666928.122L20572041089.122L20628170175.122L22369800293.122L23290313653.95 L2951488621.122 L43033456413.95 L43494931656.95 L4890678494.122 L57362612114.122L61492213990.12200000J01101g02V03E03_04F04d04e05L06B06iS2PP4LENP3SPu2bs4PR174PR19S2PP4LENP3SPu2bs3PR83PR94PR144PR191r2HrS2PP3END4LENP1P3SPu2bs3PR83PR94PR144PR191r2p'1L2Hr3HL0S2PP3END4LENP1P3SPu2bs3PR83PR94PR144PR192p'3Hp'S2PP3END4LENP1P3SPu2bs3PR83PR94PR144PR192p'3Hp'S2PP4LENP3SPu2bs4PR164PR19S2PP4LENP3SPu2bs3PR83PR94PR144PR191L2LRS2PP4LENP3BUF3SPu2bs4PR184PR19FS2PP4LENP3SPu2bs3PR83PR94PR144PR191L2LRS2PP3END4LENP1P3SPu2bs3PR83PR94PR144PR191r2p'1L2Hr3HL0S2PP4LENP3SPu2bs3PR83PR94PR144PR191r2Hr". (* [comment removed for export] *)
  Lemma sum_gettagA_valid : summary_valid asegs AL SUM_gettagA.
  Proof.
    unfold SUM_gettagA, q. lx_sum_unfold.
    intros PP END LENP P BUF LEN SPu lo sb LV TAG bs CS F fc m.
    intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
    intros [CSOK ALWF] SB MI R10 R11 R12 R13 R2 ST HPP HLENP [HBUF HLEN] OPP OLEN OBUF G1 G2.
    intros PR1 PR2 PR3 PR4 PR5 PR6 PR7 PR8 PR9 PR10 PR11 PR12 PR13 PR14 PR15 PR16 PR17 PR18 PR19 PR20.
    pose proof IMG as IMG'. unfold asan_img_ok in IMG'. destruct IMG' as (IG & ILO & IHI & IGSB). subst LEN.
    assert (U2 : bv_unsigned x2 = SPu) by (rewrite R2; apply uw64; assumption).
    pose proof (A_asn1_get_tag_spec AL IMG) as SP. unfold asn1_get_tag_stmtA, A_ASN1_GET_TAG in SP.
    eapply evtA_cut.
    { eapply (SP CS x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m PP LENP P END BUF lo bs (Z_to_bv 64 LV) TAG);
        rewrite ?U2; first [eassumption | cbn in *; lia | split; [rewrite IG, IGSB; exact G1 | rewrite IGSB, <- SB; exact G2] ]. }
    clear SP. cbv beta. intros ms' POST. unfold asn1_get_tag_postA in POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & r & p' & L & -> & MU & WM & MI' & -> & Hr & HPP' & HLENP' & Hp' & HL0 & ST').
    apply evtA_done. pose proof (lx_urange L) as LR. rewrite U2 in MU, ST'.
    lx_sum_post.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Lemma sums_asn1_ok : Forall (summary_ok asegs AL) [SUM_getlenA; SUM_gettagA].
  Proof. repeat constructor; apply apply_summary_sound; [exact (sum_getlenA_valid AL IMG) | apply sum_gettagA_valid]. Qed.
End S.

(* [comment removed for export] *)
Section SG.
  Context {HL : heap_layout}.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Let GS : list Z := [alloc_ceiling].

  Local Ltac2 Set LiaOrc.tbl := fun () => "00<0@L12066857909.95 L13952666928.122L20572041089.122L20628170175.122L22369800293.122L23290313653.95 L25516740322.122L2951488621.122 L43033456413.95 L43494931656.95 L4890678494.122 L61492213990.12200000J01101g02V03E03_04U05<05Z05[06B06iS2PP4LENP3SPu2bs4PR174PR19S2PP4LENP3SPu2bs3PR83PR94PR144PR191r2HrS2PP3END4LENP1P3SPu2bs3PR83PR94PR144PR191r2p'1L2Hr3HL0S2PP3END4LENP1P3SPu2bs3PR83PR94PR144PR192p'3Hp'S2PP3END4LENP1P3SPu2bs3PR83PR94PR144PR192p'3Hp'S2PP4LENP3SPu2bs4PR164PR19S2PP3END4LENP1P3SPu2bs3PR83PR94PR144PR191r2p'1L2Hr3HL0S2PP4LENP3SPu2bs3PR83PR94PR144PR191L2LRS2PP4LENP3BUF3SPu2bs4PR184PR19FS2PP4LENP3SPu2bs3PR83PR94PR144PR191L2LRS2PP4LENP3SPu2bs3PR83PR94PR144PR191r2Hr". (* [comment removed for export] *)
  Lemma sum_getlenA_validG : summary_validG asegs AL GS SUM_getlenA.
  Proof.
    unfold SUM_getlenA, LxConv_getlen.q, q. lx_sum_unfold.
    intros PP END LENP P BUF LEN SPu lo sb LV bs CS F fc m.
    intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
    intros [CSOK ALWF] SB MI R10 R11 R12 R2 ST HPP HLENP [HBUF HLEN] OPP OLEN OBUF G1 G2.
    intros PR1 PR2 PR3 PR4 PR5 PR6 PR7 PR8 PR9 PR10 PR11 PR12 PR13 PR14 PR15 PR16 PR17 PR18 PR19 PR20.
    pose proof IMG as IMG'. unfold asan_img_ok in IMG'. destruct IMG' as (IG & ILO & IHI & IGSB). subst LEN.
    assert (U2 : bv_unsigned x2 = SPu) by (rewrite R2; apply uw64; assumption).
    pose proof (A_asn1_get_len_spec AL IMG) as SP. unfold asn1_get_len_stmtA, A_ASN1_GET_LEN in SP.
    eapply evtA_cut.
    { eapply (SP CS x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m PP LENP P END BUF lo bs (Z_to_bv 64 LV));
        rewrite ?U2; first [eassumption | cbn in *; lia | split; [rewrite IG, IGSB; exact G1 | rewrite IGSB, <- SB; exact G2] ]. }
    clear SP. cbv beta. intros ms' POST. unfold asn1_get_len_postA in POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & r & p' & L & -> & MU & WM & MI' & -> & Hr & HPP' & HLENP' & Hp' & HL0 & ST').
    apply evtA_done. pose proof (lx_urange L) as LR. rewrite U2 in MU, ST'.
    lx_sum_post.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00<0@L12066857909.97 L13952666928.124L20572041089.124L20628170175.124L22369800293.124L23290313653.97 L2951488621.124 L43033456413.97 L43494931656.97 L4890678494.124 L57362612114.124L61492213990.12400000J01101g02V03E03_04F04d04e05L06B06iS2PP4LENP3SPu2bs4PR174PR19S2PP4LENP3SPu2bs3PR83PR94PR144PR191r2HrS2PP3END4LENP1P3SPu2bs3PR83PR94PR144PR191r2p'1L2Hr3HL0S2PP3END4LENP1P3SPu2bs3PR83PR94PR144PR192p'3Hp'S2PP3END4LENP1P3SPu2bs3PR83PR94PR144PR192p'3Hp'S2PP4LENP3SPu2bs4PR164PR19S2PP4LENP3SPu2bs3PR83PR94PR144PR191L2LRS2PP4LENP3BUF3SPu2bs4PR184PR19FS2PP4LENP3SPu2bs3PR83PR94PR144PR191L2LRS2PP3END4LENP1P3SPu2bs3PR83PR94PR144PR191r2p'1L2Hr3HL0S2PP4LENP3SPu2bs3PR83PR94PR144PR191r2Hr". (* [comment removed for export] *)
  Lemma sum_gettagA_validG : summary_validG asegs AL GS SUM_gettagA.
  Proof.
    unfold SUM_gettagA, q. lx_sum_unfold.
    intros PP END LENP P BUF LEN SPu lo sb LV TAG bs CS F fc m.
    intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
    intros [CSOK ALWF] SB MI R10 R11 R12 R13 R2 ST HPP HLENP [HBUF HLEN] OPP OLEN OBUF G1 G2.
    intros PR1 PR2 PR3 PR4 PR5 PR6 PR7 PR8 PR9 PR10 PR11 PR12 PR13 PR14 PR15 PR16 PR17 PR18 PR19 PR20.
    pose proof IMG as IMG'. unfold asan_img_ok in IMG'. destruct IMG' as (IG & ILO & IHI & IGSB). subst LEN.
    assert (U2 : bv_unsigned x2 = SPu) by (rewrite R2; apply uw64; assumption).
    pose proof (A_asn1_get_tag_spec AL IMG) as SP. unfold asn1_get_tag_stmtA, A_ASN1_GET_TAG in SP.
    eapply evtA_cut.
    { eapply (SP CS x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m PP LENP P END BUF lo bs (Z_to_bv 64 LV) TAG);
        rewrite ?U2; first [eassumption | cbn in *; lia | split; [rewrite IG, IGSB; exact G1 | rewrite IGSB, <- SB; exact G2] ]. }
    clear SP. cbv beta. intros ms' POST. unfold asn1_get_tag_postA in POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & r & p' & L & -> & MU & WM & MI' & -> & Hr & HPP' & HLENP' & Hp' & HL0 & ST').
    apply evtA_done. pose proof (lx_urange L) as LR. rewrite U2 in MU, ST'.
    lx_sum_post.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac valp4_valid SPEC :=
    unfold SUM_getboolA, SUM_getintA, SUM_valp4A, q; lx_sum_unfold;
    intros PP END VALP P BUF LEN SPu lo sb VV ACL bs CS F fc m;
    intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31;
    intros [CSOK ALWF] SB MI GB R10 R11 R12 R2 ST HPP HVALP [HBUF HLEN] OPP OVALP OBUF OLEN G1 G2;
    intros PR1 PR2 PR3 PR4 PR5 PR6 PR7 PR8 PR9 PR10 PR11 PR12 PR13 PR14 PR15 PR16 PR17 PR18 PR19 PR20 PR21;
    let IMG' := fresh "IMG'" in
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    let IG := fresh "IG" in let ILO := fresh "ILO" in let IHI := fresh "IHI" in let IGSB := fresh "IGSB" in
    destruct IMG' as (IG & ILO & IHI & IGSB); subst LEN;
    cbn [nth] in GB; subst ACL;
    let U2 := fresh "U2" in
    assert (U2 : bv_unsigned x2 = SPu) by (rewrite R2; apply uw64; assumption);
    let SP := fresh "SP" in
    pose proof (SPEC AL IMG) as SP; unfold asn1_get_bool_stmtA, asn1_get_int_stmtA, A_ASN1_GET_BOOL, A_ASN1_GET_INT in SP;
    eapply evtA_cut;
    [ eapply (SP CS x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m PP VALP P END BUF lo bs (Z_to_bv 64 VV));
      rewrite ?U2; first [eassumption | cbn in *; lia | split; [rewrite IG, IGSB; exact G1 | rewrite IGSB, <- SB; exact G2] ]
    | clear SP; cbv beta;
      let ms' := fresh "ms'" in let POST := fresh "POST" in
      intros ms' POST; unfold asn1_get_bool_postA, asn1_get_int_postA in POST;
      let MU := fresh "MU" in let ST' := fresh "ST'" in let v := fresh "v" in
      destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & r & p' & v & -> & MU & WM & MI' & -> & Hr & HPP' & HVALP' & ST' & Hp' & HL0);
      apply evtA_done; pose proof (lx_urange v) as LR; rewrite U2 in MU, ST';
      lx_sum_post ].

  Local Ltac2 Set LiaOrc.tbl := fun () => "00;0@L13952666928.123L20628170175.123L22369800293.123L43494931656.96 L44164795464.123L44870228291.123L47443572146.96 L51799707724.96 L57922663490.123L61492213990.123L67527703564.96 00000W01F02502602]03D03e04B05205Y066S2PP4VALP3SPu2bs3PR83PR94PR154PR201r2HrS2PP3END4VALP1P3SPu2bs3PR83PR94PR154PR202p'3Hp'S2PP3END4VALP1P3SPu2bs3PR83PR94PR154PR202p'3Hp'FS2PP4VALP3SPu2bs3PR83PR94PR154PR201v2LRS2PP4VALP3SPu2bs3PR83PR94PR154PR201v2LRS2PP4VALP3BUF3SPu2lo2bs4PR184PR20S2PP4VALP3SPu2lo2bs4PR164PR20S2PP4VALP1P3SPu2bs3PR83PR94PR154PR201r2p'2Hr3HL0S2PP4VALP3SPu2bs3PR83PR94PR154PR201r2HrS2PP4VALP3SPu2lo2bs4PR174PR20". (* [comment removed for export] *)
  Lemma sum_getboolA_validG : summary_validG asegs AL GS SUM_getboolA.
  Proof. valp4_valid (@A_asn1_get_bool_spec HL). Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00;0@L13952666928.123L20628170175.123L22369800293.123L43494931656.96 L44164795464.123L44870228291.123L47443572146.96 L51799707724.96 L57922663490.123L61492213990.123L67527703564.96 00000W01F02502602]03D03e04B05205Y066S2PP4VALP3SPu2bs3PR83PR94PR154PR201r2HrS2PP3END4VALP1P3SPu2bs3PR83PR94PR154PR202p'3Hp'S2PP3END4VALP1P3SPu2bs3PR83PR94PR154PR202p'3Hp'FS2PP4VALP3SPu2bs3PR83PR94PR154PR201v2LRS2PP4VALP3SPu2bs3PR83PR94PR154PR201v2LRS2PP4VALP3BUF3SPu2lo2bs4PR184PR20S2PP4VALP3SPu2lo2bs4PR164PR20S2PP4VALP1P3SPu2bs3PR83PR94PR154PR201r2p'2Hr3HL0S2PP4VALP3SPu2bs3PR83PR94PR154PR201r2HrS2PP4VALP3SPu2lo2bs4PR174PR20". (* [comment removed for export] *)
  Lemma sum_getintA_validG : summary_validG asegs AL GS SUM_getintA.
  Proof. valp4_valid (@A_asn1_get_int_spec HL). Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00<0@L13952666928.123L20572041089.123L20628170175.123L22369800293.123L2951488621.123 L43494931656.96 L47443572146.96 L4890678494.123 L51799707724.96 L57922663490.123L60906416716.96 L61492213990.12300000W01M02<02k03R03S04404[05805n06K072S2PP4LENP3SPu2bs3PR83PR94PR154PR201r2HrS2PP3END4LENP1P3SPu2bs3PR83PR94PR154PR201r2p'1L2Hr3HL0S2PP3END4LENP1P3SPu2bs3PR83PR94PR154PR202p'3Hp'S2PP3END4LENP1P3SPu2bs3PR83PR94PR154PR202p'3Hp'S2PP4LENP3SPu2bs3PR83PR94PR154PR201L2LRFS2PP4LENP3BUF3SPu2lo2bs4PR184PR20S2PP4LENP3SPu2bs3PR83PR94PR154PR201L2LRS2PP4LENP3SPu2lo2bs4PR164PR20S2PP3END4LENP1P3SPu2bs3PR83PR94PR154PR201r2p'1L2Hr3HL0S2PP4LENP3SPu2lo2bs4PR174PR20S2PP4LENP3SPu2bs3PR83PR94PR154PR201r2Hr". (* [comment removed for export] *)
  Lemma sum_bitstrnullA_validG : summary_validG asegs AL GS SUM_bitstrnullA.
  Proof.
    unfold SUM_bitstrnullA, q. lx_sum_unfold.
    intros PP END LENP P BUF LEN SPu lo sb LV ACL bs CS F fc m.
    intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
    intros [CSOK ALWF] SB MI GB R10 R11 R12 R2 ST HPP HLENP [HBUF HLEN] OPP OLEN OBUF G1 G2.
    intros PR1 PR2 PR3 PR4 PR5 PR6 PR7 PR8 PR9 PR10 PR11 PR12 PR13 PR14 PR15 PR16 PR17 PR18 PR19 PR20 PR21.
    pose proof IMG as IMG'. unfold asan_img_ok in IMG'. destruct IMG' as (IG & ILO & IHI & IGSB). subst LEN.
    cbn [nth] in GB. subst ACL.
    assert (U2 : bv_unsigned x2 = SPu) by (rewrite R2; apply uw64; assumption).
    pose proof (@A_asn1_get_bitstring_null_spec HL AL IMG) as SP. unfold asn1_get_bitstring_null_stmtA, A_ASN1_GET_BITSTRING_NULL in SP.
    eapply evtA_cut.
    { eapply (SP CS x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m PP LENP P END BUF lo bs (Z_to_bv 64 LV));
        rewrite ?U2; first [eassumption | cbn in *; lia | split; [rewrite IG, IGSB; exact G1 | rewrite IGSB, <- SB; exact G2] ]. }
    clear SP. cbv beta. intros ms' POST. unfold asn1_get_bitstring_null_postA in POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & r & p' & L & -> & MU & WM & MI' & -> & Hr & HPP' & HLENP' & ST' & Hp' & HL0).
    apply evtA_done. pose proof (lx_urange L) as LR. rewrite U2 in MU, ST'.
    lx_sum_post.
    all: intros R0; destruct (HL0 R0); first [assumption | lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Lemma sums_asn1G_ok : ltac2:(CDefT.buildp (gd_tbl_LxA_sums ()) "(23.$24.(25.$26.VAL,VGS,)(2.$24.$27.(2.$24.$28.(2.$24.$29.(2.$24.$2:.(2.$24.$2;.(7.$24.)))))))")
(* [comment removed for export] *).
  Proof.
    repeat constructor; apply apply_summary_soundG;
      [apply sum_getlenA_validG | apply sum_gettagA_validG | apply sum_getboolA_validG | apply sum_getintA_validG | apply sum_bitstrnullA_validG].
  Qed.
End SG.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition SUM_bitstringA : summary := ltac2:(CDefT.buildp (gd_tbl_LxA_sums ()) "(21.+99?;4.$1.#=.#13.#2.(2.(3.$4.$5.)(6.$4.$5.+:.^1.)(2.(3.$4.$5.)(6.$4.$5.+;.^2.)(2.(3.$4.$5.)(6.$4.$5.+<.^3.)(2.(3.$4.$5.)(6.$4.$5.+2.^7.)(7.(3.$4.$5.))))))(2.(3.$5.$22.)(6.$5.$22.^=.#0.)(7.(3.$5.$22.)))(8.$5.^9.)(2.$9.(:.(;.^1.)(2.$<.(=.&8.(;.^4.))(7.$<.)))(2.$9.(:.(;.^3.)(2.$<.(=.&8.(;.^:.))(2.$<.(=.&1.(;.^;.))(2.$<.(2<.&7.^2.)(2.$<.(=.&8.(;.^<.))(7.$<.))))))(7.$9.)))(8.(3.$5.$5.)(6.$5.$5.^8.^7.))(2.(3.(3.$5.$5.)$5.)(6.(3.$5.$5.)$5.(6.$5.$5.^5.^6.)^1.)(7.(3.(3.$5.$5.)$5.)))(2.$9.(>.(;.^1.)(?.+8.))(2.$9.(>.(;.^3.)(?.+18.))(2.$9.(>.(;.^5.)(;.^6.))(2.$9.(10.(?.+?5>50.)(2.$<.(=.&8.(?.+1099?8.))(7.$<.)))(2.$9.(10.(?.+1099?8.)(2.$<.(=.&8.(;.^9.))(7.$<.)))(7.$9.))))))(2.$11.(12.(;.^5.)(;.^4.))(2.$11.(12.(;.^4.)(;.^2.))(2.$11.(12.(;.^2.)(13.(;.^5.)(;.^6.)))(2.$11.(14.(13.(;.^5.)(;.^6.))(?.(15.+2.+3?.)))(2.$11.(16.(;.^1.)(?.+8.)(;.^3.)(?.+18.))(2.$11.(17.(;.^6.)(;.^1.)(?.+8.)(;.^5.)(;.^6.))(2.$11.(17.(;.^6.)(;.^3.)(?.+18.)(;.^5.)(;.^6.))(2.$11.(18.(19.^1.)&3.)(2.$11.(18.(19.^3.)&3.)(2.$11.(14.(?.=)(;.^1.))(2.$11.(14.(?.=)(;.^3.))(2.$11.(14.(?.=)(;.^5.))(2.$11.(12.(;.^8.)(13.(;.^7.)(?.-40.)))(2.$11.(12.(;.^=.)(;.^8.))(2.$11.(18.(19.^7.)&4.)(2.$11.(16.(;.^1.)(?.+8.)(;.^8.)(13.(;.^7.)(1;.-1.(;.^8.))))(2.$11.(16.(;.^3.)(?.+18.)(;.^8.)(13.(;.^7.)(1;.-1.(;.^8.))))(2.$11.(17.(;.^6.)(;.^5.)(;.^6.)(;.^8.)(13.(;.^7.)(1;.-1.(;.^8.))))(2.$11.(1:.(;.^8.)(13.(;.^7.)(1;.-1.(;.^8.))))(2.$11.(12.(?.=)(;.^7.))(2.$11.(12.(;.^7.)(?.(1<.$1=.+1.)))(7.$11.))))))))))))))))))))))(2.(3.$1>.$1>.)(6.$1>.$1>.(;.^1.)(13.(;.^1.)(?.+8.)))(2.(3.$1>.$1>.)(6.$1>.$1>.(;.^3.)(13.(;.^3.)(?.+18.)))(2.(3.$1>.$1>.)(6.$1>.$1>.(13.(;.^7.)(?.-40.))(;.^7.))(7.(3.$1>.$1>.)))))(2.(3.$4.$5.)(6.$4.$5.+:.^>.)(2.(3.$4.$5.)(6.$4.$5.+5.^13.)(2.(3.$4.$5.)(6.$4.$5.+6.^14.)(2.(3.$4.$5.)(6.$4.$5.+7.^15.)(2.(3.$4.$5.)(6.$4.$5.+;.^16.)(2.(3.$4.$5.)(6.$4.$5.+<.^17.)(2.(3.$4.$5.)(6.$4.$5.+=.^18.)(2.(3.$4.$5.)(6.$4.$5.+>.^19.)(2.(3.$4.$5.)(6.$4.$5.+?.^1:.)(2.(3.$4.$5.)(6.$4.$5.+10.^1;.)(2.(3.$4.$5.)(6.$4.$5.+11.^1<.)(2.(3.$4.$5.)(6.$4.$5.+1<.^1=.)(2.(3.$4.$5.)(6.$4.$5.+1=.^1>.)(2.(3.$4.$5.)(6.$4.$5.+1>.^1?.)(2.(3.$4.$5.)(6.$4.$5.+1?.^20.)(7.(3.$4.$5.)))))))))))))))))(2.$9.(:.(;.^1.)(2.$<.(=.&8.(;.^?.))(7.$<.)))(2.$9.(:.(;.^3.)(2.$<.(=.&8.(;.^10.))(2.$<.(=.&1.(;.^11.))(2.$<.(2<.&7.^2.)(2.$<.(=.&8.(;.^12.))(7.$<.))))))(2.$9.(1?.(;.^8.)(;.^7.))(7.$9.))))(2.$11.(14.(?.-7?.)(;.^>.))(2.$11.(12.(;.^>.)(?.=))(2.$11.(12.(;.^4.)(;.^?.))(2.$11.(12.(;.^?.)(;.^2.))(2.$11.(12.(?.=)(;.^10.))(2.$11.(12.(;.^10.)(?.(1<.$1=.+1.)))(2.$11.(12.(?.=)(;.^11.))(2.$11.(12.(;.^11.)(?.+??.))(2.$11.(12.(?.=)(;.^12.))(2.$11.(12.(;.^12.)(?.(1<.$1=.+1.)))(2.$11.(20.(13.(;.^>.)(?.+1.))(?.=)(13.(;.^4.)(?.+3.))(;.^12.))(2.$11.(20.(13.(;.^>.)(?.+1.))(?.=)(13.(;.^12.)(;.^10.))(;.^?.))(2.$11.(20.(13.(;.^>.)(?.+1.))(?.=)(;.^?.)(13.(;.^12.)(;.^10.)))(2.$11.(20.(13.(;.^>.)(?.+1.))(?.=)(;.^2.)(;.^?.))(7.$11.))))))))))))))))")
(* [comment removed for export] *).
Definition lxz1 : cellx := XZ 1 (ELit 0).
Definition lxz7 : cellx := XRep 7 (ELit 0).   (* [comment removed for export] *)
Definition lxz4 : cellx := XZ 4 (ELit 0).
Definition lxz8 : cellx := XZ 8 (ELit 0).
(* [comment removed for export] *)
Definition lxbs0 : list cellx := [lxz8; lxz1; lxz1; lxz1; lxz1; lxz1; lxz1; lxz1; lxz1; lxz8].
(* [comment removed for export] *)
Definition SUM_bitstring0A : summary := ltac2:(CDefT.buildp (gd_tbl_LxA_sums ()) "(21.+99?;4.$1.#=.#13.#1.(2.(3.$4.$5.)(6.$4.$5.+:.^1.)(2.(3.$4.$5.)(6.$4.$5.+;.^2.)(2.(3.$4.$5.)(6.$4.$5.+<.^3.)(2.(3.$4.$5.)(6.$4.$5.+2.^7.)(7.(3.$4.$5.))))))(2.(3.$5.$22.)(6.$5.$22.^=.#0.)(7.(3.$5.$22.)))(8.$5.^9.)(2.$9.(:.(;.^1.)(2.$<.(=.&8.(;.^4.))(7.$<.)))(2.$9.(:.(;.^3.)(2.$<.(=.&8.(;.^:.))(2.$<.(=.&1.(;.^;.))(2.$<.$2=.(2.$<.$2=.(2.$<.$2=.(2.$<.$2=.(2.$<.$2=.(2.$<.$2=.(2.$<.$2=.(2.$<.(=.&8.(;.^<.))(7.$<.))))))))))))(7.$9.)))(8.(3.$5.$5.)(6.$5.$5.^8.^7.))(2.(3.(3.$5.$5.)$5.)(6.(3.$5.$5.)$5.(6.$5.$5.^5.^6.)^1.)(7.(3.(3.$5.$5.)$5.)))(2.$9.(>.(;.^1.)(?.+8.))(2.$9.(>.(;.^3.)(?.+18.))(2.$9.(>.(;.^5.)(;.^6.))(2.$9.(10.(?.+?5>50.)(2.$<.(=.&8.(?.+1099?8.))(7.$<.)))(2.$9.(10.(?.+1099?8.)(2.$<.(=.&8.(;.^9.))(7.$<.)))(7.$9.))))))(2.$11.(12.(;.^5.)(;.^4.))(2.$11.(12.(;.^4.)(;.^2.))(2.$11.(12.(;.^2.)(13.(;.^5.)(;.^6.)))(2.$11.(14.(13.(;.^5.)(;.^6.))(?.(15.+2.+3?.)))(2.$11.(16.(;.^1.)(?.+8.)(;.^3.)(?.+18.))(2.$11.(17.(;.^6.)(;.^1.)(?.+8.)(;.^5.)(;.^6.))(2.$11.(17.(;.^6.)(;.^3.)(?.+18.)(;.^5.)(;.^6.))(2.$11.(18.(19.^1.)&3.)(2.$11.(18.(19.^3.)&3.)(2.$11.(14.(?.=)(;.^1.))(2.$11.(14.(?.=)(;.^3.))(2.$11.(14.(?.=)(;.^5.))(2.$11.(12.(;.^8.)(13.(;.^7.)(?.-40.)))(2.$11.(12.(;.^=.)(;.^8.))(2.$11.(18.(19.^7.)&4.)(2.$11.(16.(;.^1.)(?.+8.)(;.^8.)(13.(;.^7.)(1;.-1.(;.^8.))))(2.$11.(16.(;.^3.)(?.+18.)(;.^8.)(13.(;.^7.)(1;.-1.(;.^8.))))(2.$11.(17.(;.^6.)(;.^5.)(;.^6.)(;.^8.)(13.(;.^7.)(1;.-1.(;.^8.))))(2.$11.(1:.(;.^8.)(13.(;.^7.)(1;.-1.(;.^8.))))(2.$11.(12.(?.=)(;.^7.))(2.$11.(12.(;.^7.)(?.(1<.$1=.+1.)))(7.$11.))))))))))))))))))))))(2.(3.$1>.$1>.)(6.$1>.$1>.(;.^1.)(13.(;.^1.)(?.+8.)))(2.(3.$1>.$1>.)(6.$1>.$1>.(;.^3.)(13.(;.^3.)(?.+18.)))(2.(3.$1>.$1>.)(6.$1>.$1>.(13.(;.^7.)(?.-40.))(;.^7.))(7.(3.$1>.$1>.)))))(2.(3.$4.$5.)(6.$4.$5.+:.^>.)(2.(3.$4.$5.)(6.$4.$5.+5.^13.)(2.(3.$4.$5.)(6.$4.$5.+6.^14.)(2.(3.$4.$5.)(6.$4.$5.+7.^15.)(2.(3.$4.$5.)(6.$4.$5.+;.^16.)(2.(3.$4.$5.)(6.$4.$5.+<.^17.)(2.(3.$4.$5.)(6.$4.$5.+=.^18.)(2.(3.$4.$5.)(6.$4.$5.+>.^19.)(2.(3.$4.$5.)(6.$4.$5.+?.^1:.)(2.(3.$4.$5.)(6.$4.$5.+10.^1;.)(2.(3.$4.$5.)(6.$4.$5.+11.^1<.)(2.(3.$4.$5.)(6.$4.$5.+1<.^1=.)(2.(3.$4.$5.)(6.$4.$5.+1=.^1>.)(2.(3.$4.$5.)(6.$4.$5.+1>.^1?.)(2.(3.$4.$5.)(6.$4.$5.+1?.^20.)(7.(3.$4.$5.)))))))))))))))))(2.$9.(:.(;.^1.)(2.$<.(=.&8.(;.^?.))(7.$<.)))(2.$9.(:.(;.^3.)(2.$<.(=.&8.(;.^10.))(2.$<.(=.&1.(;.^11.))(2.$<.$2=.(2.$<.$2=.(2.$<.$2=.(2.$<.$2=.(2.$<.$2=.(2.$<.$2=.(2.$<.$2=.(2.$<.(=.&8.(;.^12.))(7.$<.))))))))))))(2.$9.(1?.(;.^8.)(;.^7.))(7.$9.))))(2.$11.(14.(?.-7?.)(;.^>.))(2.$11.(12.(;.^>.)(?.=))(2.$11.(12.(;.^4.)(;.^?.))(2.$11.(12.(;.^?.)(;.^2.))(2.$11.(12.(?.=)(;.^10.))(2.$11.(12.(;.^10.)(?.(1<.$1=.+1.)))(2.$11.(12.(?.=)(;.^11.))(2.$11.(12.(;.^11.)(?.+??.))(2.$11.(12.(?.=)(;.^12.))(2.$11.(12.(;.^12.)(?.(1<.$1=.+1.)))(2.$11.(20.(13.(;.^>.)(?.+1.))(?.=)(13.(;.^4.)(?.+3.))(;.^12.))(2.$11.(20.(13.(;.^>.)(?.+1.))(?.=)(13.(;.^12.)(;.^10.))(;.^?.))(2.$11.(20.(13.(;.^>.)(?.+1.))(?.=)(;.^?.)(13.(;.^12.)(;.^10.)))(2.$11.(20.(13.(;.^>.)(?.+1.))(?.=)(;.^2.)(;.^?.))(7.$11.))))))))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition SUM_amemsetA (n : N) (kd : nat) : summary := ltac2:(CDefT.buildp (gd_tbl_LxA_sums ()) "(2>.+68258.$1.#9.#?.#1.(2.(3.$4.$5.)(6.$4.$5.+:.^9.)(2.(3.$4.$5.)(6.$4.$5.+;.^2.)(2.(3.$4.$5.)(6.$4.$5.+<.^3.)(2.(3.$4.$5.)(6.$4.$5.+2.^4.)(7.(3.$4.$5.))))))(2.(3.$5.$22.)(6.$5.$22.^1.O1.)(2.(3.$5.$22.)(6.$5.$22.^6.#1.)(2.(3.$5.$22.)(6.$5.$22.^7.#2.)(2.(3.$5.$22.)(6.$5.$22.^8.#3.)(7.(3.$5.$22.))))))(2?.$5.)(2.$9.(:.(;.^1.)(2.$<.(2<.O2.^1.)(7.$<.)))(7.$9.))(8.(3.$5.$5.)(6.$5.$5.^5.^4.))(7.(3.(3.$5.$5.)$5.))(2.$9.(>.(;.^1.)(?.(30.O2.)))(7.$9.))(2.$11.(31.(;.^9.)(;.^1.))(2.$11.(31.(;.^3.)(?.(30.O2.)))(2.$11.(12.(?.=)(;.^2.))(2.$11.(14.(;.^2.)(?.+100.))(2.$11.(12.(;.^8.)(;.^5.))(2.$11.(12.(;.^5.)(13.(;.^4.)(1;.-1.(;.^7.))))(2.$11.(1:.(;.^5.)(13.(;.^4.)(1;.-1.(;.^5.))))(2.$11.(20.(13.(;.^1.)(?.(30.O2.)))(;.^5.)(;.^4.)(;.^1.))(2.$11.(12.(;.^4.)(;.^6.))(2.$11.(12.(?.=)(;.^4.))(2.$11.(12.(;.^4.)(?.(1<.$1=.+1.)))(7.$11.))))))))))))(2.(3.$1>.$1>.)(6.$1>.$1>.(;.^1.)(13.(;.^1.)(?.(30.O2.))))(2.(3.$1>.$1>.)(6.$1>.$1>.(;.^5.)(;.^4.))(7.(3.$1>.$1>.))))(2.(3.$4.$5.)(6.$4.$5.+:.^:.)(2.(3.$4.$5.)(6.$4.$5.+5.^;.)(2.(3.$4.$5.)(6.$4.$5.+6.^<.)(2.(3.$4.$5.)(6.$4.$5.+7.^=.)(2.(3.$4.$5.)(6.$4.$5.+;.^>.)(2.(3.$4.$5.)(6.$4.$5.+<.^?.)(2.(3.$4.$5.)(6.$4.$5.+=.^10.)(2.(3.$4.$5.)(6.$4.$5.+>.^11.)(2.(3.$4.$5.)(6.$4.$5.+?.^12.)(2.(3.$4.$5.)(6.$4.$5.+10.^13.)(2.(3.$4.$5.)(6.$4.$5.+11.^14.)(2.(3.$4.$5.)(6.$4.$5.+1<.^15.)(2.(3.$4.$5.)(6.$4.$5.+1=.^16.)(2.(3.$4.$5.)(6.$4.$5.+1>.^17.)(2.(3.$4.$5.)(6.$4.$5.+1?.^18.)(7.(3.$4.$5.)))))))))))))))))(2.$9.(:.(;.^1.)(2.$<.(32.O2.(;.^2.))(7.$<.)))(2.$9.(1?.(;.^5.)(;.^4.))(7.$9.)))(2.$11.(31.(;.^:.)(;.^1.))(7.$11.))(2.$22.#0.(7.$22.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition SUM_amemset0A (n : N) (cells : list cellx) (kd : nat) : summary := ltac2:(CDefT.buildp (gd_tbl_LxA_sums ()) "(2>.+68258.$1.#9.#?.#1.(2.(3.$4.$5.)(6.$4.$5.+:.^9.)(2.(3.$4.$5.)(6.$4.$5.+;.^2.)(2.(3.$4.$5.)(6.$4.$5.+<.^3.)(2.(3.$4.$5.)(6.$4.$5.+2.^4.)(7.(3.$4.$5.))))))(2.(3.$5.$22.)(6.$5.$22.^1.O1.)(2.(3.$5.$22.)(6.$5.$22.^6.#1.)(2.(3.$5.$22.)(6.$5.$22.^7.#2.)(2.(3.$5.$22.)(6.$5.$22.^8.#3.)(7.(3.$5.$22.))))))(2?.$5.)(2.$9.(:.(;.^1.)(2.$<.(2<.O3.^1.)(7.$<.)))(7.$9.))(8.(3.$5.$5.)(6.$5.$5.^5.^4.))(7.(3.(3.$5.$5.)$5.))(2.$9.(>.(;.^1.)(?.(30.O3.)))(7.$9.))(2.$11.(31.(;.^9.)(;.^1.))(2.$11.(31.(;.^2.)(?.=))(2.$11.(31.(;.^3.)(?.(30.O3.)))(2.$11.(12.(?.=)(;.^2.))(2.$11.(14.(;.^2.)(?.+100.))(2.$11.(12.(;.^8.)(;.^5.))(2.$11.(12.(;.^5.)(13.(;.^4.)(1;.-1.(;.^7.))))(2.$11.(1:.(;.^5.)(13.(;.^4.)(1;.-1.(;.^5.))))(2.$11.(20.(13.(;.^1.)(?.(30.O3.)))(;.^5.)(;.^4.)(;.^1.))(2.$11.(12.(;.^4.)(;.^6.))(2.$11.(12.(?.=)(;.^4.))(2.$11.(12.(;.^4.)(?.(1<.$1=.+1.)))(7.$11.)))))))))))))(2.(3.$1>.$1>.)(6.$1>.$1>.(;.^1.)(13.(;.^1.)(?.(30.O3.))))(2.(3.$1>.$1>.)(6.$1>.$1>.(;.^5.)(;.^4.))(7.(3.$1>.$1>.))))(2.(3.$4.$5.)(6.$4.$5.+:.^:.)(2.(3.$4.$5.)(6.$4.$5.+5.^;.)(2.(3.$4.$5.)(6.$4.$5.+6.^<.)(2.(3.$4.$5.)(6.$4.$5.+7.^=.)(2.(3.$4.$5.)(6.$4.$5.+;.^>.)(2.(3.$4.$5.)(6.$4.$5.+<.^?.)(2.(3.$4.$5.)(6.$4.$5.+=.^10.)(2.(3.$4.$5.)(6.$4.$5.+>.^11.)(2.(3.$4.$5.)(6.$4.$5.+?.^12.)(2.(3.$4.$5.)(6.$4.$5.+10.^13.)(2.(3.$4.$5.)(6.$4.$5.+11.^14.)(2.(3.$4.$5.)(6.$4.$5.+1<.^15.)(2.(3.$4.$5.)(6.$4.$5.+1=.^16.)(2.(3.$4.$5.)(6.$4.$5.+1>.^17.)(2.(3.$4.$5.)(6.$4.$5.+1?.^18.)(7.(3.$4.$5.)))))))))))))))))(2.$9.(:.(;.^1.)O2.)(2.$9.(1?.(;.^5.)(;.^4.))(7.$9.)))(2.$11.(31.(;.^:.)(;.^1.))(7.$11.))(2.$22.#0.(7.$22.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition SUM_getalgA (kp ka kr : nat) : summary := ltac2:(CDefT.buildp (gd_tbl_LxA_sums ()) "(2>.+9:9<0.$1.#17.#18.#1.(2.(3.$4.$5.)(6.$4.$5.+:.^15.)(2.(3.$4.$5.)(6.$4.$5.+;.^2.)(2.(3.$4.$5.)(6.$4.$5.+<.^16.)(2.(3.$4.$5.)(6.$4.$5.+=.^17.)(2.(3.$4.$5.)(6.$4.$5.+2.^8.)(7.(3.$4.$5.)))))))(2.(3.$5.$22.)(6.$5.$22.^1.O3.)(2.(3.$5.$22.)(6.$5.$22.^3.O2.)(2.(3.$5.$22.)(6.$5.$22.^4.O1.)(2.(3.$5.$22.)(6.$5.$22.^12.#1.)(2.(3.$5.$22.)(6.$5.$22.^13.#2.)(2.(3.$5.$22.)(6.$5.$22.^14.#3.)(7.(3.$5.$22.))))))))(2?.$5.)(2.$9.(:.(;.^1.)(2.$<.(=.&8.(;.^5.))(7.$<.)))(2.$9.(:.(;.^3.)(2.$<.(=.&4.(;.^:.))(2.$<.(=.&4.(;.^;.))(2.$<.(=.&8.(;.^<.))(2.$<.(=.&8.(;.^=.))(7.$<.))))))(2.$9.(:.(;.^4.)(2.$<.(=.&4.(;.^>.))(2.$<.(=.&4.(;.^?.))(2.$<.(=.&8.(;.^10.))(2.$<.(=.&8.(;.^11.))(7.$<.))))))(7.$9.))))(8.(3.$5.$5.)(6.$5.$5.^9.^8.))(2.(3.(3.$5.$5.)$5.)(6.(3.$5.$5.)$5.(6.$5.$5.^6.^7.)^1.)(7.(3.(3.$5.$5.)$5.)))(2.$9.(>.(;.^1.)(?.+8.))(2.$9.(>.(;.^3.)(?.+18.))(2.$9.(>.(;.^4.)(?.+18.))(2.$9.(>.(;.^6.)(;.^7.))(2.$9.(>.(13.(;.^8.)(?.-48.))(?.+8.))(7.$9.))))))(2.$11.(31.(;.^15.)(;.^1.))(2.$11.(31.(;.^16.)(;.^3.))(2.$11.(31.(;.^17.)(;.^4.))(2.$11.(12.(;.^6.)(;.^5.))(2.$11.(12.(;.^5.)(;.^2.))(2.$11.(12.(;.^2.)(13.(;.^6.)(;.^7.)))(2.$11.(14.(13.(;.^6.)(;.^7.))(?.(15.+2.+3?.)))(2.$11.(16.(;.^1.)(?.+8.)(;.^3.)(?.+18.))(2.$11.(16.(;.^1.)(?.+8.)(;.^4.)(?.+18.))(2.$11.(16.(;.^3.)(?.+18.)(;.^4.)(?.+18.))(2.$11.(17.(;.^7.)(;.^1.)(?.+8.)(;.^6.)(;.^7.))(2.$11.(17.(;.^7.)(;.^3.)(?.+18.)(;.^6.)(;.^7.))(2.$11.(17.(;.^7.)(;.^4.)(?.+18.)(;.^6.)(;.^7.))(2.$11.(18.(19.^1.)&3.)(2.$11.(18.(19.^3.)&3.)(2.$11.(18.(19.^4.)&3.)(2.$11.(14.(?.=)(;.^1.))(2.$11.(14.(?.=)(;.^3.))(2.$11.(14.(?.=)(;.^4.))(2.$11.(14.(?.=)(;.^6.))(2.$11.(12.(;.^14.)(;.^9.))(2.$11.(12.(;.^9.)(13.(13.(;.^8.)(1;.-1.(;.^13.)))(?.-60.)))(2.$11.(12.(;.^8.)(;.^12.))(2.$11.(18.(19.^8.)&4.)(2.$11.(16.(;.^1.)(?.+8.)(;.^9.)(13.(;.^8.)(1;.-1.(;.^9.))))(2.$11.(16.(;.^3.)(?.+18.)(;.^9.)(13.(;.^8.)(1;.-1.(;.^9.))))(2.$11.(16.(;.^4.)(?.+18.)(;.^9.)(13.(;.^8.)(1;.-1.(;.^9.))))(2.$11.(17.(;.^7.)(;.^6.)(;.^7.)(;.^9.)(13.(;.^8.)(1;.-1.(;.^9.))))(2.$11.(12.(?.=)(;.^8.))(2.$11.(12.(;.^8.)(?.(1<.$1=.+1.)))(7.$11.)))))))))))))))))))))))))))))))(2.(3.$1>.$1>.)(6.$1>.$1>.(;.^1.)(13.(;.^1.)(?.+8.)))(2.(3.$1>.$1>.)(6.$1>.$1>.(;.^3.)(13.(;.^3.)(?.+18.)))(2.(3.$1>.$1>.)(6.$1>.$1>.(;.^4.)(13.(;.^4.)(?.+18.)))(2.(3.$1>.$1>.)(6.$1>.$1>.(;.^9.)(;.^8.))(7.(3.$1>.$1>.))))))(2.(3.$4.$5.)(6.$4.$5.+:.^18.)(2.(3.$4.$5.)(6.$4.$5.+5.^22.)(2.(3.$4.$5.)(6.$4.$5.+6.^23.)(2.(3.$4.$5.)(6.$4.$5.+7.^24.)(2.(3.$4.$5.)(6.$4.$5.+;.^25.)(2.(3.$4.$5.)(6.$4.$5.+<.^26.)(2.(3.$4.$5.)(6.$4.$5.+=.^27.)(2.(3.$4.$5.)(6.$4.$5.+>.^28.)(2.(3.$4.$5.)(6.$4.$5.+?.^29.)(2.(3.$4.$5.)(6.$4.$5.+10.^2:.)(2.(3.$4.$5.)(6.$4.$5.+11.^2;.)(2.(3.$4.$5.)(6.$4.$5.+1<.^2<.)(2.(3.$4.$5.)(6.$4.$5.+1=.^2=.)(2.(3.$4.$5.)(6.$4.$5.+1>.^2>.)(2.(3.$4.$5.)(6.$4.$5.+1?.^2?.)(7.(3.$4.$5.)))))))))))))))))(2.$9.(:.(;.^1.)(2.$<.(=.&8.(;.^19.))(7.$<.)))(2.$9.(:.(;.^3.)(2.$<.(=.&4.(;.^1:.))(2.$<.(=.&4.(;.^1;.))(2.$<.(=.&8.(;.^1<.))(2.$<.(=.&8.(;.^1=.))(7.$<.))))))(2.$9.(:.(;.^4.)(2.$<.(=.&4.(;.^1>.))(2.$<.(=.&4.(;.^1?.))(2.$<.(=.&8.(;.^20.))(2.$<.(=.&8.(;.^21.))(7.$<.))))))(2.$9.(1?.(;.^9.)(;.^8.))(7.$9.)))))(2.$11.(14.(?.-7?.)(;.^18.))(2.$11.(12.(;.^18.)(?.=))(2.$11.(12.(;.^5.)(;.^19.))(2.$11.(12.(;.^19.)(;.^2.))(2.$11.(12.(?.=)(;.^1:.))(2.$11.(12.(;.^1:.)(?.(1<.$1=.+1.)))(2.$11.(12.(?.=)(;.^1;.))(2.$11.(12.(;.^1;.)(?.(1<.$1=.+1.)))(2.$11.(12.(?.=)(;.^1<.))(2.$11.(12.(;.^1<.)(?.(1<.$1=.+1.)))(2.$11.(12.(?.=)(;.^1=.))(2.$11.(12.(;.^1=.)(?.(1<.$1=.+1.)))(2.$11.(12.(?.=)(;.^1>.))(2.$11.(12.(;.^1>.)(?.(1<.$1=.+1.)))(2.$11.(12.(?.=)(;.^1?.))(2.$11.(12.(;.^1?.)(?.(1<.$1=.+1.)))(2.$11.(12.(?.=)(;.^20.))(2.$11.(12.(;.^20.)(?.(1<.$1=.+1.)))(2.$11.(12.(?.=)(;.^21.))(2.$11.(12.(;.^21.)(?.(1<.$1=.+1.)))(2.$11.(20.(13.(;.^18.)(?.+1.))(?.=)(;.^6.)(;.^1=.))(2.$11.(20.(13.(;.^18.)(?.+1.))(?.=)(13.(;.^1=.)(;.^1<.))(;.^19.))(2.$11.(33.(;.^21.)(13.(;.^18.)(?.+1.))(?.=)(;.^6.)(;.^21.))(2.$11.(33.(;.^21.)(13.(;.^18.)(?.+1.))(?.=)(13.(;.^21.)(;.^20.))(;.^19.))(2.$11.(33.(;.^21.)(13.(;.^18.)(?.+1.))(?.=)(;.^19.)(13.(;.^21.)(;.^20.)))(2.$11.(33.(;.^20.)(13.(;.^18.)(?.+1.))(?.=)(?.+1.)(;.^21.))(2.$11.(33.(;.^1>.)(13.(;.^18.)(?.+1.))(?.=)(?.+1.)(;.^21.))(7.$11.))))))))))))))))))))))))))))(2.$22.#0.(7.$22.)))")
(* [comment removed for export] *).


(* [comment removed for export] *)
Definition SUM_oidlook1A (pc stack : Z) (ko ke kb : nat) : summary := ltac2:(CDefT.buildp (gd_tbl_LxA_sums ()) "(2>.O5.$1.#10.#10.#1.(2.(3.$4.$5.)(6.$4.$5.+:.^?.)(2.(3.$4.$5.)(6.$4.$5.+;.^10.)(2.(3.$4.$5.)(6.$4.$5.+2.^9.)(7.(3.$4.$5.)))))(2.(3.$5.$22.)(6.$5.$22.^1.O3.)(2.(3.$5.$22.)(6.$5.$22.^2.O2.)(2.(3.$5.$22.)(6.$5.$22.^;.#1.)(2.(3.$5.$22.)(6.$5.$22.^<.O1.)(2.(3.$5.$22.)(6.$5.$22.^=.#3.)(7.(3.$5.$22.)))))))(2?.$5.)(2.$9.(:.(;.^1.)(2.$<.(=.&4.(;.^3.))(7.$<.)))(2.$9.(:.(13.(;.^1.)(?.+4.))(2.$<.(=.&4.(;.^4.))(7.$<.)))(2.$9.(:.(13.(;.^1.)(?.+8.))(2.$<.(=.&8.(;.^5.))(7.$<.)))(2.$9.(:.(13.(;.^1.)(?.+10.))(2.$<.(=.&8.(;.^6.))(7.$<.)))(2.$9.(:.(;.^2.)(2.$<.(=.&4.(;.^>.))(7.$<.)))(7.$9.))))))(8.(3.$5.$5.)(6.$5.$5.^:.^9.))(2.(3.(3.$5.$5.)$5.)(6.(3.$5.$5.)$5.(6.$5.$5.^7.^8.)^1.)(7.(3.(3.$5.$5.)$5.)))(2.$9.(>.(;.^1.)(?.+18.))(2.$9.(>.(;.^6.)(;.^5.))(2.$9.(>.(;.^2.)(?.+4.))(7.$9.))))(2.$11.(31.(;.^?.)(;.^1.))(2.$11.(31.(;.^10.)(;.^2.))(2.$11.(14.(;.^7.)(;.^6.))(2.$11.(12.(?.=)(;.^5.))(2.$11.(12.(13.(;.^6.)(;.^5.))(13.(;.^7.)(;.^8.)))(2.$11.(16.(;.^2.)(?.+4.)(;.^1.)(?.+18.))(2.$11.(17.(;.^8.)(;.^2.)(?.+4.)(;.^7.)(;.^8.))(2.$11.(18.(19.^1.)&3.)(2.$11.(18.(19.^2.)&2.)(2.$11.(14.(?.=)(;.^1.))(2.$11.(14.(?.=)(;.^2.))(2.$11.(14.(?.=)(;.^7.))(2.$11.(12.(;.^=.)(;.^:.))(2.$11.(12.(;.^:.)(13.(13.(;.^9.)(1;.-1.(?.O4.)))(1;.-1.(;.^<.))))(2.$11.(12.(;.^9.)(;.^;.))(2.$11.(18.(19.^9.)&4.)(2.$11.(16.(;.^1.)(?.+18.)(;.^:.)(13.(;.^9.)(1;.-1.(;.^:.))))(2.$11.(16.(;.^2.)(?.+4.)(;.^:.)(13.(;.^9.)(1;.-1.(;.^:.))))(2.$11.(17.(;.^8.)(;.^7.)(;.^8.)(;.^:.)(13.(;.^9.)(1;.-1.(;.^:.))))(2.$11.(12.(13.(13.(;.^7.)(;.^8.))(?.+8.))(?.(15.+2.+2?.)))(2.$11.(12.(?.=)(;.^9.))(2.$11.(12.(;.^9.)(?.(1<.$1=.+1.)))(7.$11.)))))))))))))))))))))))(2.(3.$1>.$1>.)(6.$1>.$1>.(;.^2.)(13.(;.^2.)(?.+4.)))(2.(3.$1>.$1>.)(6.$1>.$1>.(;.^:.)(;.^9.))(7.(3.$1>.$1>.))))(2.(3.$4.$5.)(6.$4.$5.+:.^11.)(2.(3.$4.$5.)(6.$4.$5.+5.^13.)(2.(3.$4.$5.)(6.$4.$5.+6.^14.)(2.(3.$4.$5.)(6.$4.$5.+7.^15.)(2.(3.$4.$5.)(6.$4.$5.+;.^16.)(2.(3.$4.$5.)(6.$4.$5.+<.^17.)(2.(3.$4.$5.)(6.$4.$5.+=.^18.)(2.(3.$4.$5.)(6.$4.$5.+>.^19.)(2.(3.$4.$5.)(6.$4.$5.+?.^1:.)(2.(3.$4.$5.)(6.$4.$5.+10.^1;.)(2.(3.$4.$5.)(6.$4.$5.+11.^1<.)(2.(3.$4.$5.)(6.$4.$5.+1<.^1=.)(2.(3.$4.$5.)(6.$4.$5.+1=.^1>.)(2.(3.$4.$5.)(6.$4.$5.+1>.^1?.)(2.(3.$4.$5.)(6.$4.$5.+1?.^20.)(7.(3.$4.$5.)))))))))))))))))(2.$9.(:.(;.^2.)(2.$<.(=.&4.(;.^12.))(7.$<.)))(2.$9.(1?.(;.^:.)(;.^9.))(7.$9.)))(2.$11.(12.(?.-2>.)(;.^11.))(2.$11.(12.(;.^11.)(?.=))(2.$11.(20.(;.^11.)(?.-2>.)(?.=)(;.^11.))(2.$11.(12.(?.=)(;.^12.))(2.$11.(12.(;.^12.)(?.(1<.$1=.+1.)))(7.$11.))))))(2.$22.#0.(7.$22.)))")
(* [comment removed for export] *).


Section SGX.
  Context {HL : heap_layout}.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Variable GSX : list Z.
  Let GS : list Z := alloc_ceiling :: GSX.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00<0@L12066857909.96 L13952666928.123L20572041089.123L20628170175.123L22369800293.123L23290313653.96 L25516740322.123L2951488621.123 L43033456413.96 L43494931656.96 L4890678494.123 L61492213990.12300000J01101g02V03E03_04U05<05Z05[06B06iS2PP4LENP3SPu2bs4PR174PR19S2PP4LENP3SPu2bs3PR83PR94PR144PR191r2HrS2PP3END4LENP1P3SPu2bs3PR83PR94PR144PR191r2p'1L2Hr3HL0S2PP3END4LENP1P3SPu2bs3PR83PR94PR144PR192p'3Hp'S2PP3END4LENP1P3SPu2bs3PR83PR94PR144PR192p'3Hp'S2PP4LENP3SPu2bs4PR164PR19S2PP3END4LENP1P3SPu2bs3PR83PR94PR144PR191r2p'1L2Hr3HL0S2PP4LENP3SPu2bs3PR83PR94PR144PR191L2LRS2PP4LENP3BUF3SPu2bs4PR184PR19FS2PP4LENP3SPu2bs3PR83PR94PR144PR191L2LRS2PP4LENP3SPu2bs3PR83PR94PR144PR191r2Hr". (* [comment removed for export] *)
  Lemma sum_getlenA_validGX : summary_validG asegs AL GS SUM_getlenA.
  Proof.
    unfold SUM_getlenA, LxConv_getlen.q, q. lx_sum_unfold.
    intros PP END LENP P BUF LEN SPu lo sb LV bs CS F fc m.
    intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
    intros [CSOK ALWF] SB MI R10 R11 R12 R2 ST HPP HLENP [HBUF HLEN] OPP OLEN OBUF G1 G2.
    intros PR1 PR2 PR3 PR4 PR5 PR6 PR7 PR8 PR9 PR10 PR11 PR12 PR13 PR14 PR15 PR16 PR17 PR18 PR19 PR20.
    pose proof IMG as IMG'. unfold asan_img_ok in IMG'. destruct IMG' as (IG & ILO & IHI & IGSB). subst LEN.
    assert (U2 : bv_unsigned x2 = SPu) by (rewrite R2; apply uw64; assumption).
    pose proof (A_asn1_get_len_spec AL IMG) as SP. unfold asn1_get_len_stmtA, A_ASN1_GET_LEN in SP.
    eapply evtA_cut.
    { eapply (SP CS x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m PP LENP P END BUF lo bs (Z_to_bv 64 LV));
        rewrite ?U2; first [eassumption | cbn in *; lia | split; [rewrite IG, IGSB; exact G1 | rewrite IGSB, <- SB; exact G2] ]. }
    clear SP. cbv beta. intros ms' POST. unfold asn1_get_len_postA in POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & r & p' & L & -> & MU & WM & MI' & -> & Hr & HPP' & HLENP' & Hp' & HL0 & ST').
    apply evtA_done. pose proof (lx_urange L) as LR. rewrite U2 in MU, ST'.
    lx_sum_post.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00<0@L12066857909.98 L13952666928.125L20572041089.125L20628170175.125L22369800293.125L23290313653.98 L2951488621.125 L43033456413.98 L43494931656.98 L4890678494.125 L57362612114.125L61492213990.12500000J01101g02V03E03_04F04d04e05L06B06iS2PP4LENP3SPu2bs4PR174PR19S2PP4LENP3SPu2bs3PR83PR94PR144PR191r2HrS2PP3END4LENP1P3SPu2bs3PR83PR94PR144PR191r2p'1L2Hr3HL0S2PP3END4LENP1P3SPu2bs3PR83PR94PR144PR192p'3Hp'S2PP3END4LENP1P3SPu2bs3PR83PR94PR144PR192p'3Hp'S2PP4LENP3SPu2bs4PR164PR19S2PP4LENP3SPu2bs3PR83PR94PR144PR191L2LRS2PP4LENP3BUF3SPu2bs4PR184PR19FS2PP4LENP3SPu2bs3PR83PR94PR144PR191L2LRS2PP3END4LENP1P3SPu2bs3PR83PR94PR144PR191r2p'1L2Hr3HL0S2PP4LENP3SPu2bs3PR83PR94PR144PR191r2Hr". (* [comment removed for export] *)
  Lemma sum_gettagA_validGX : summary_validG asegs AL GS SUM_gettagA.
  Proof.
    unfold SUM_gettagA, q. lx_sum_unfold.
    intros PP END LENP P BUF LEN SPu lo sb LV TAG bs CS F fc m.
    intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
    intros [CSOK ALWF] SB MI R10 R11 R12 R13 R2 ST HPP HLENP [HBUF HLEN] OPP OLEN OBUF G1 G2.
    intros PR1 PR2 PR3 PR4 PR5 PR6 PR7 PR8 PR9 PR10 PR11 PR12 PR13 PR14 PR15 PR16 PR17 PR18 PR19 PR20.
    pose proof IMG as IMG'. unfold asan_img_ok in IMG'. destruct IMG' as (IG & ILO & IHI & IGSB). subst LEN.
    assert (U2 : bv_unsigned x2 = SPu) by (rewrite R2; apply uw64; assumption).
    pose proof (A_asn1_get_tag_spec AL IMG) as SP. unfold asn1_get_tag_stmtA, A_ASN1_GET_TAG in SP.
    eapply evtA_cut.
    { eapply (SP CS x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m PP LENP P END BUF lo bs (Z_to_bv 64 LV) TAG);
        rewrite ?U2; first [eassumption | cbn in *; lia | split; [rewrite IG, IGSB; exact G1 | rewrite IGSB, <- SB; exact G2] ]. }
    clear SP. cbv beta. intros ms' POST. unfold asn1_get_tag_postA in POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & r & p' & L & -> & MU & WM & MI' & -> & Hr & HPP' & HLENP' & Hp' & HL0 & ST').
    apply evtA_done. pose proof (lx_urange L) as LR. rewrite U2 in MU, ST'.
    lx_sum_post.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Ltac valp4_validX SPEC :=
    unfold SUM_getboolA, SUM_getintA, SUM_valp4A, q; lx_sum_unfold;
    intros PP END VALP P BUF LEN SPu lo sb VV ACL bs CS F fc m;
    intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31;
    intros [CSOK ALWF] SB MI GB R10 R11 R12 R2 ST HPP HVALP [HBUF HLEN] OPP OVALP OBUF OLEN G1 G2;
    intros PR1 PR2 PR3 PR4 PR5 PR6 PR7 PR8 PR9 PR10 PR11 PR12 PR13 PR14 PR15 PR16 PR17 PR18 PR19 PR20 PR21;
    let IMG' := fresh "IMG'" in
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    let IG := fresh "IG" in let ILO := fresh "ILO" in let IHI := fresh "IHI" in let IGSB := fresh "IGSB" in
    destruct IMG' as (IG & ILO & IHI & IGSB); subst LEN;
    cbn [nth] in GB; subst ACL;
    let U2 := fresh "U2" in
    assert (U2 : bv_unsigned x2 = SPu) by (rewrite R2; apply uw64; assumption);
    let SP := fresh "SP" in
    pose proof (SPEC AL IMG) as SP; unfold asn1_get_bool_stmtA, asn1_get_int_stmtA, A_ASN1_GET_BOOL, A_ASN1_GET_INT in SP;
    eapply evtA_cut;
    [ eapply (SP CS x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m PP VALP P END BUF lo bs (Z_to_bv 64 VV));
      rewrite ?U2; first [eassumption | cbn in *; lia | split; [rewrite IG, IGSB; exact G1 | rewrite IGSB, <- SB; exact G2] ]
    | clear SP; cbv beta;
      let ms' := fresh "ms'" in let POST := fresh "POST" in
      intros ms' POST; unfold asn1_get_bool_postA, asn1_get_int_postA in POST;
      let MU := fresh "MU" in let ST' := fresh "ST'" in let v := fresh "v" in
      destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & r & p' & v & -> & MU & WM & MI' & -> & Hr & HPP' & HVALP' & ST' & Hp' & HL0);
      apply evtA_done; pose proof (lx_urange v) as LR; rewrite U2 in MU, ST';
      lx_sum_post ].

  Local Ltac2 Set LiaOrc.tbl := fun () => "00;0@L13952666928.124L20628170175.124L22369800293.124L43494931656.97 L44164795464.124L44870228291.124L47443572146.97 L51799707724.97 L57922663490.124L61492213990.124L67527703564.97 00000W01F02502602]03D03e04B05205Y066S2PP4VALP3SPu2bs3PR83PR94PR154PR201r2HrS2PP3END4VALP1P3SPu2bs3PR83PR94PR154PR202p'3Hp'S2PP3END4VALP1P3SPu2bs3PR83PR94PR154PR202p'3Hp'FS2PP4VALP3SPu2bs3PR83PR94PR154PR201v2LRS2PP4VALP3SPu2bs3PR83PR94PR154PR201v2LRS2PP4VALP3BUF3SPu2lo2bs4PR184PR20S2PP4VALP3SPu2lo2bs4PR164PR20S2PP4VALP1P3SPu2bs3PR83PR94PR154PR201r2p'2Hr3HL0S2PP4VALP3SPu2bs3PR83PR94PR154PR201r2HrS2PP4VALP3SPu2lo2bs4PR174PR20". (* [comment removed for export] *)
  Lemma sum_getboolA_validGX : summary_validG asegs AL GS SUM_getboolA.
  Proof. valp4_validX (@A_asn1_get_bool_spec HL). Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00;0@L13952666928.124L20628170175.124L22369800293.124L43494931656.97 L44164795464.124L44870228291.124L47443572146.97 L51799707724.97 L57922663490.124L61492213990.124L67527703564.97 00000W01F02502602]03D03e04B05205Y066S2PP4VALP3SPu2bs3PR83PR94PR154PR201r2HrS2PP3END4VALP1P3SPu2bs3PR83PR94PR154PR202p'3Hp'S2PP3END4VALP1P3SPu2bs3PR83PR94PR154PR202p'3Hp'FS2PP4VALP3SPu2bs3PR83PR94PR154PR201v2LRS2PP4VALP3SPu2bs3PR83PR94PR154PR201v2LRS2PP4VALP3BUF3SPu2lo2bs4PR184PR20S2PP4VALP3SPu2lo2bs4PR164PR20S2PP4VALP1P3SPu2bs3PR83PR94PR154PR201r2p'2Hr3HL0S2PP4VALP3SPu2bs3PR83PR94PR154PR201r2HrS2PP4VALP3SPu2lo2bs4PR174PR20". (* [comment removed for export] *)
  Lemma sum_getintA_validGX : summary_validG asegs AL GS SUM_getintA.
  Proof. valp4_validX (@A_asn1_get_int_spec HL). Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00<0@L13952666928.124L20572041089.124L20628170175.124L22369800293.124L2951488621.124 L43494931656.97 L47443572146.97 L4890678494.124 L51799707724.97 L57922663490.124L60906416716.97 L61492213990.12400000W01M02<02k03R03S04404[05805n06K072S2PP4LENP3SPu2bs3PR83PR94PR154PR201r2HrS2PP3END4LENP1P3SPu2bs3PR83PR94PR154PR201r2p'1L2Hr3HL0S2PP3END4LENP1P3SPu2bs3PR83PR94PR154PR202p'3Hp'S2PP3END4LENP1P3SPu2bs3PR83PR94PR154PR202p'3Hp'S2PP4LENP3SPu2bs3PR83PR94PR154PR201L2LRFS2PP4LENP3BUF3SPu2lo2bs4PR184PR20S2PP4LENP3SPu2bs3PR83PR94PR154PR201L2LRS2PP4LENP3SPu2lo2bs4PR164PR20S2PP3END4LENP1P3SPu2bs3PR83PR94PR154PR201r2p'1L2Hr3HL0S2PP4LENP3SPu2lo2bs4PR174PR20S2PP4LENP3SPu2bs3PR83PR94PR154PR201r2Hr". (* [comment removed for export] *)
  Lemma sum_bitstrnullA_validGX : summary_validG asegs AL GS SUM_bitstrnullA.
  Proof.
    unfold SUM_bitstrnullA, q. lx_sum_unfold.
    intros PP END LENP P BUF LEN SPu lo sb LV ACL bs CS F fc m.
    intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
    intros [CSOK ALWF] SB MI GB R10 R11 R12 R2 ST HPP HLENP [HBUF HLEN] OPP OLEN OBUF G1 G2.
    intros PR1 PR2 PR3 PR4 PR5 PR6 PR7 PR8 PR9 PR10 PR11 PR12 PR13 PR14 PR15 PR16 PR17 PR18 PR19 PR20 PR21.
    pose proof IMG as IMG'. unfold asan_img_ok in IMG'. destruct IMG' as (IG & ILO & IHI & IGSB). subst LEN.
    cbn [nth] in GB. subst ACL.
    assert (U2 : bv_unsigned x2 = SPu) by (rewrite R2; apply uw64; assumption).
    pose proof (@A_asn1_get_bitstring_null_spec HL AL IMG) as SP. unfold asn1_get_bitstring_null_stmtA, A_ASN1_GET_BITSTRING_NULL in SP.
    eapply evtA_cut.
    { eapply (SP CS x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m PP LENP P END BUF lo bs (Z_to_bv 64 LV));
        rewrite ?U2; first [eassumption | cbn in *; lia | split; [rewrite IG, IGSB; exact G1 | rewrite IGSB, <- SB; exact G2] ]. }
    clear SP. cbv beta. intros ms' POST. unfold asn1_get_bitstring_null_postA in POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & r & p' & L & -> & MU & WM & MI' & -> & Hr & HPP' & HLENP' & ST' & Hp' & HL0).
    apply evtA_done. pose proof (lx_urange L) as LR. rewrite U2 in MU, ST'.
    lx_sum_post.
    all: intros R0; destruct (HL0 R0); first [assumption | lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00I0@L13950420272.131L18151966734.135L20630646207.131L21473122132.131L22372309093.131L23666182881.132L2459357707.131 L26212100466.131L27358792120.131L2949278829.131 L32432601718.135L36654050060.135L37722658859.135L38711614776.131L43494931656.100L43710749615.131L47443572146.100L4893154526.131 L51799707724.100L56348811285.131L61490524390.131L62594125787.135L65482468237.131L7331612829.135 L9499998796.100 00000]01\02Q02R03G04704f05U05V06C06k07G08008108208Z09:09g0:C0:k0;X0<70<80<k0=GS2PP3BSP3SPu2bs3PR83PR94PR154PR201r2ub2Hr3UBRS2PP3END3BSP3BUF3SPu2bs3PR43PR34PR104PR114PR202p'1L2qv2LR2Q22Q3S2PP3END3BSP1P3SPu2bs3PR83PR94PR154PR202p'2ub3Hp'3UBRFS2PP3END3BSP1P3SPu2bs3PR83PR94PR154PR202p'2ub3Hp'3UBRS2PP3BSP3SPu2bs3PR83PR94PR154PR201r2ub2Hr3UBR2R0S2PP3BSP3SPu2bs3PR83PR94PR154PR202ub2pw3PWR3UBRS2PP3BSP3SPu2bs3PR83PR94PR154PR202ub2pw3PWR3UBRFS2PP3BSP3SPu2bs3PR83PR94PR154PR201L2ub2LR3UBRS2PP3END3BSP3SPu2bs4PR104PR114PR202p'2Q3S2PP3BSP1P3SPu2bs4PR202qv2Q1S2PP3BSP3SPu2bs4PR104PR114PR202p'1L2qv2Q2FFS2PP3BSP3SPu2bs3PR83PR94PR154PR202ub3UBRS2PP3BSP3BUF3SPu2lo2bs4PR184PR20S2PP3BSP3SPu2bs3PR83PR94PR154PR201L2ub2LR3UBRS2PP3BSP3SPu2lo2bs4PR164PR20S2PP3BSP3SPu2bs3PR83PR94PR154PR202ub3UBRS2PP3BSP3SPu2bs3PR83PR94PR154PR201r2ub2Hr3UBRS2PP3BSP3SPu2bs4PR202p'1L2qv2Q2FS2PP3BSP1P3BUF3SPu2bs3PR14PR104PR114PR124PR202qv2Q1S2PP3BSP3SPu2lo2bs4PR174PR20". (* [comment removed for export] *)
  Lemma sum_bitstringA_validGX : summary_validG asegs AL GS SUM_bitstringA.
  Proof.
    unfold SUM_bitstringA, q. lx_sum_unfold.
    intros PP END BSP P BUF LEN SPu lo sb LV UB PV ACL bs pad CS F fc m.
    intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
    intros [CSOK ALWF] SB MI GB R10 R11 R12 R2 ST HPP HBSP [HBUF HLEN] OPP OBSP OBUF G1 G2.
    intros PR1 PR2 PR3 PR4 PR5 PR6 PR7 PR8 PR9 PR10 PR11 PR12 PR13 PR14 PR15 PR16 PR17 PR18 PR19 PR20 PR21.
    pose proof IMG as IMG'. unfold asan_img_ok in IMG'. destruct IMG' as (IG & ILO & IHI & IGSB). subst LEN.
    cbn [nth] in GB. subst ACL.
    assert (U2 : bv_unsigned x2 = SPu) by (rewrite R2; apply uw64; assumption).
    pose proof (@A_asn1_get_bitstring_spec HL AL IMG) as SP. unfold asn1_get_bitstring_stmtA, A_ASN1_GET_BITSTRING in SP.
    eapply evtA_cut.
    { eapply (SP CS x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m PP BSP P END BUF lo bs (Z_to_bv 64 LV) (Z_to_bv 8 UB) pad (Z_to_bv 64 PV));
        rewrite ?U2; first [eassumption | cbn in *; lia | split; [rewrite IG, IGSB; exact G1 | rewrite IGSB, <- SB; exact G2] ]. }
    clear SP. cbv beta. intros ms' POST. unfold asn1_get_bitstring_postA in POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & r & p' & L & ub & pw & -> & MU & WM & MI' & -> & Hr & HPP' & HBSP' & ST' & Hp' & HL0).
    apply evtA_done. pose proof (lx_urange L) as LR. pose proof (lx_urange pw) as PWR.
    pose proof (bv_unsigned_in_range 8 ub) as UBR. unfold bv_modulus in UBR. cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul] in UBR.
    rewrite U2 in MU, ST'. unfold bitstring_cells in HBSP'.
    lx_sum_post.
    all: destruct (Z.eq_dec r 0) as [R0|R0]; [ right | left; lia ];
         destruct (HL0 R0) as (qv & -> & Q1 & Q2 & Q3); rewrite ?(uw64 qv) in * by (unfold two64; cbn in *; lia); cbn in *; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00I0@L13950420272.130L18151966734.134L20630646207.130L21473122132.130L22372309093.130L23666182881.131L2459357707.130 L26212100466.130L27358792120.130L2949278829.130 L32432601718.134L36654050060.134L37722658859.134L38711614776.130L43494931656.99 L43710749615.130L47443572146.99 L4893154526.130 L51799707724.99 L56348811285.130L61490524390.130L62594125787.134L65482468237.130L7331612829.134 L9499998796.99  00000]01\02Q02R03G04704f05U05V06C06k07G08008108208Z09:09g0:C0:k0;X0<70<80<k0=GS2PP3BSP3SPu2bs3PR83PR94PR154PR201r2ub2Hr3UBRS2PP3END3BSP3BUF3SPu2bs3PR43PR34PR104PR114PR202p'1L2qv2LR2Q22Q3S2PP3END3BSP1P3SPu2bs3PR83PR94PR154PR202p'2ub3Hp'3UBRFS2PP3END3BSP1P3SPu2bs3PR83PR94PR154PR202p'2ub3Hp'3UBRS2PP3BSP3SPu2bs3PR83PR94PR154PR201r2ub2Hr3UBR2R0S2PP3BSP3SPu2bs3PR83PR94PR154PR202ub2pw3PWR3UBRS2PP3BSP3SPu2bs3PR83PR94PR154PR202ub2pw3PWR3UBRFS2PP3BSP3SPu2bs3PR83PR94PR154PR201L2ub2LR3UBRS2PP3END3BSP3SPu2bs4PR104PR114PR202p'2Q3S2PP3BSP1P3SPu2bs4PR202qv2Q1S2PP3BSP3SPu2bs4PR104PR114PR202p'1L2qv2Q2FFS2PP3BSP3SPu2bs3PR83PR94PR154PR202ub3UBRS2PP3BSP3BUF3SPu2lo2bs4PR184PR20S2PP3BSP3SPu2bs3PR83PR94PR154PR201L2ub2LR3UBRS2PP3BSP3SPu2lo2bs4PR164PR20S2PP3BSP3SPu2bs3PR83PR94PR154PR202ub3UBRS2PP3BSP3SPu2bs3PR83PR94PR154PR201r2ub2Hr3UBRS2PP3BSP3SPu2bs4PR202p'1L2qv2Q2FS2PP3BSP1P3BUF3SPu2bs3PR14PR104PR114PR124PR202qv2Q1S2PP3BSP3SPu2lo2bs4PR174PR20". (* [comment removed for export] *)
  Lemma sum_bitstring0A_validGX : summary_validG asegs AL GS SUM_bitstring0A.
  Proof.
    unfold SUM_bitstring0A, lxz1, q. lx_sum_unfold.
    intros PP END BSP P BUF LEN SPu lo sb LV UB PV ACL bs CS F fc m.
    intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
    intros [CSOK ALWF] SB MI GB R10 R11 R12 R2 ST HPP HBSP [HBUF HLEN] OPP OBSP OBUF G1 G2.
    intros PR1 PR2 PR3 PR4 PR5 PR6 PR7 PR8 PR9 PR10 PR11 PR12 PR13 PR14 PR15 PR16 PR17 PR18 PR19 PR20 PR21.
    pose proof IMG as IMG'. unfold asan_img_ok in IMG'. destruct IMG' as (IG & ILO & IHI & IGSB). subst LEN.
    cbn [nth] in GB. subst ACL.
    assert (U2 : bv_unsigned x2 = SPu) by (rewrite R2; apply uw64; assumption).
    (* [comment removed for export] *)
    apply (rw_cells_reshape asegs m BSP _ (bitstring_cells (Z_to_bv 64 LV) (Z_to_bv 8 UB) (repeat (Z_to_bv 8 0) 7) (Z_to_bv 64 PV))) in HBSP;
      [ | cbn; repeat split; reflexivity | cbn [bitstring_cells cells_bytes cbytes repeat List.app]; reflexivity ].
    pose proof (@A_asn1_get_bitstring_spec HL AL IMG) as SP. unfold asn1_get_bitstring_stmtA, A_ASN1_GET_BITSTRING in SP.
    eapply evtA_cut.
    { eapply (SP CS x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m PP BSP P END BUF lo bs (Z_to_bv 64 LV) (Z_to_bv 8 UB) (repeat (Z_to_bv 8 0) 7) (Z_to_bv 64 PV));
        rewrite ?U2; first [eassumption | cbn in *; lia | split; [rewrite IG, IGSB; exact G1 | rewrite IGSB, <- SB; exact G2] ]. }
    clear SP. cbv beta. intros ms' POST. unfold asn1_get_bitstring_postA in POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & r & p' & L & ub & pw & -> & MU & WM & MI' & -> & Hr & HPP' & HBSP' & ST' & Hp' & HL0).
    apply evtA_done. pose proof (lx_urange L) as LR. pose proof (lx_urange pw) as PWR.
    pose proof (bv_unsigned_in_range 8 ub) as UBR. unfold bv_modulus in UBR. cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul] in UBR.
    rewrite U2 in MU, ST'. unfold bitstring_cells in HBSP'.
    apply (rw_cells_reshape asegs m' BSP _ [C8 L; C1 ub; C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C8 pw]) in HBSP';
      [ | cbn; repeat split; reflexivity | cbn [cells_bytes cbytes repeat List.app]; reflexivity ].
    lx_sum_post.
    all: destruct (Z.eq_dec r 0) as [R0|R0]; [ right | left; lia ];
         destruct (HL0 R0) as (qv & -> & Q1 & Q2 & Q3); rewrite ?(uw64 qv) in * by (unfold two64; cbn in *; lia); cbn in *; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma sum_getlenA_okOX : forall OPS CS, summary_okO asegs AL GS OPS CS SUM_getlenA.
  Proof. intros; apply apply_summary_soundO, summary_validG_O, sum_getlenA_validGX. Qed.
  Lemma sum_gettagA_okOX : forall OPS CS, summary_okO asegs AL GS OPS CS SUM_gettagA.
  Proof. intros; apply apply_summary_soundO, summary_validG_O, sum_gettagA_validGX. Qed.
  Lemma sum_getboolA_okOX : forall OPS CS, summary_okO asegs AL GS OPS CS SUM_getboolA.
  Proof. intros; apply apply_summary_soundO, summary_validG_O, sum_getboolA_validGX. Qed.
  Lemma sum_getintA_okOX : forall OPS CS, summary_okO asegs AL GS OPS CS SUM_getintA.
  Proof. intros; apply apply_summary_soundO, summary_validG_O, sum_getintA_validGX. Qed.
  Lemma sum_bitstrnullA_okOX : forall OPS CS, summary_okO asegs AL GS OPS CS SUM_bitstrnullA.
  Proof. intros; apply apply_summary_soundO, summary_validG_O, sum_bitstrnullA_validGX. Qed.
  Lemma sum_bitstringA_okOX : forall OPS CS, summary_okO asegs AL GS OPS CS SUM_bitstringA.
  Proof. intros; apply apply_summary_soundO, summary_validG_O, sum_bitstringA_validGX. Qed.
  Lemma sum_bitstring0A_okOX : forall OPS CS, summary_okO asegs AL GS OPS CS SUM_bitstring0A.
  Proof. intros; apply apply_summary_soundO, summary_validG_O, sum_bitstring0A_validGX. Qed.
End SGX.

Section SOX.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Variables (GSX : list Z) (OPS : list (mem -> Prop)).
  Let GS : list Z := alloc_ceiling :: GSX.
  Hypothesis G1 : nth 1 GS 0 = htop asegs R HIA h.
  Hypothesis G2 : nth 2 GS 0 = arl_need_amem R.
  Hypothesis G3 : nth 3 GS 0 = arl_stklo R.
  Hypothesis O0 : nth 0 OPS (fun _ => True) = (fun m => HM asegs R HIA h LB LF m).
  Hypothesis AMS : arl_amemset R = 0x68258 \/ arl_memset_i R = 0x68258.

  (* [comment removed for export] *)
  Ltac amemset_valid n kd DST GD CW :=
    unfold SUM_amemsetA, q; lx_sum_unfold;
    repeat match goal with |- context [Z.of_N ?w] => let k := eval cbv in (Z.of_N w) in change (Z.of_N w) with k end;
    let DSTp := fresh "DSTp" in let V := fresh "V" in let NN := fresh "NN" in let SPu := fresh "SPu" in let LO := fresh "LO" in
    let HT := fresh "HT" in let NA := fresh "NA" in let SL := fresh "SL" in let bs1 := fresh "bs1" in
    let F := fresh "F" in let fc := fresh "fc" in let m := fresh "m" in
    intros DSTp V NN SPu LO HT NA SL A0 bs1 F fc m;
    intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31;
    let GD' := fresh "GD'" in let GHT := fresh "GHT" in let GNA := fresh "GNA" in let GSL := fresh "GSL" in
    intros [CSOK ALWF] _ MI GD' GHT GNA GSL R10 R11 R12 R2 ST HDST OD EA0 ENN V0 V1 SLLO LOSP SCR SEP SPTOP SP0 SP1 OQ0;
    change (DSTp = nth kd GS 0) in GD'; change (HT = nth 1 GS 0) in GHT; change (NA = nth 2 GS 0) in GNA; change (SL = nth 3 GS 0) in GSL;
    change (nth 0 OPS (fun _ => True) m) in OQ0;
    rewrite GD in GD'; rewrite G1 in GHT; rewrite G2 in GNA; rewrite G3 in GSL; rewrite O0 in OQ0; cbv beta in OQ0;
    subst DSTp HT NA SL NN; subst A0;
    let U2 := fresh "U2" in
    assert (U2 : bv_unsigned x2 = SPu) by (rewrite R2; apply uw64; assumption);
    let HU := fresh "HU" in pose proof (u8arr_of_rw_cells asegs m DST _ bs1 HDST) as HU;
    let LEN := fresh "LEN" in
    assert (LEN : Z.of_nat (length bs1) = n) by (let WF := fresh in destruct HDST as [[WF _] _]; cbn in WF; lia);
    let HI := fresh "HI" in
    pose proof (cw_top47_or asegs R HIA h LB LF m (arl_stklo R) DST n OQ0 CW ltac:(clear; lia)) as HI;
    eapply evtA_cut;
    [ destruct AMS as [AE|AE];
      [ eapply (artA_amemset asegs R HIA 0x68258 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m h LB LF DST V n LO bs1); rewrite ?U2;
        first [ left; symmetry; exact AE | eassumption | cbn in *; lia ]
      | eapply (artA_amemset asegs R HIA 0x68258 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m h LB LF DST V n LO bs1); rewrite ?U2;
        first [ right; symmetry; exact AE | eassumption | cbn in *; lia ] ]
    | cbv beta;
      let ms' := fresh "ms'" in let POST := fresh "POST" in
      intros ms' POST; unfold call_postA in POST;
      let MU := fresh "MU" in let WM := fresh "WM" in let HU' := fresh "HU'" in let ST' := fresh "ST'" in let HH' := fresh "HH'" in
      let MI' := fresh "MI'" in let m' := fresh "m'" in
      destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & -> & HU' & ST' & HH');
      apply evtA_done; rewrite U2 in MU, ST';
      apply (rw_cells_of_u8arr asegs) in HU'; rewrite repeat_length in HU';
      let k := eval cbv in (Z.to_nat n) in change (Z.to_nat n) with k in HU';
      lx_sum_post;
      (* [comment removed for export] *)
      try (lazymatch goal with |- ?f 0%nat OPS ?d ?mm => change (nth 0%nat OPS d mm); rewrite O0; cbv beta; exact HH' end) ].

  Local Ltac2 Set LiaOrc.tbl := fun () => "0060@L1632069692.82  L35497379938.82 L39076636629.0  L56089036902.79 L64076393781.102L67529247213.10200000=00B00C00J00S00TS1V3bs12V02V1S3bs1SS3bs11HS3DST3bs1F". (* [comment removed for export] *)
  Lemma sum_amemsetA24_okO (kd : nat) (DST : Z) (CS : Z -> Prop) : ltac2:(CDefT.buildp (gd_tbl_LxA_sums ()) "P,(34.P,$4.Sp(35.$26.VR,VHIA,Vh,)O1.)P,(34.$4.(36.$4.O3.VGS,=)O2.)P,(37.(38.VR,)(39.$3:.VLB,(3;.VLF,))(3<.VR,)(3=.$26.VR,VHIA,Vh,)O2.+18.)(3>.$26.(3?.VR,)VGS,VOPS,O1.(40.&18.O3.))")
(* [comment removed for export] *).
  Proof. intros ECS GD CW. subst CS. apply apply_summary_soundO. amemset_valid 24 kd DST GD CW. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060@L1632069692.82  L23044565922.82 L39012636437.0  L57165256614.79 L64076393781.102L67529247213.10200000=00B00C00J00S00TS1V3bs12V02V1S3bs1SS3bs11HS3DST3bs1F". (* [comment removed for export] *)
  Lemma sum_amemsetA20_okO (kd : nat) (DST : Z) (CS : Z -> Prop) : ltac2:(CDefT.buildp (gd_tbl_LxA_sums ()) "P,(34.P,$4.Sp(35.$26.VR,VHIA,Vh,)O1.)P,(34.$4.(36.$4.O3.VGS,=)O2.)P,(37.(38.VR,)(39.$3:.VLB,(3;.VLF,))(3<.VR,)(3=.$26.VR,VHIA,Vh,)O2.+14.)(3>.$26.(3?.VR,)VGS,VOPS,O1.(40.&14.O3.))")
(* [comment removed for export] *).
  Proof. intros ECS GD CW. subst CS. apply apply_summary_soundO. amemset_valid 20 kd DST GD CW. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060@L1632069692.82  L33537894950.79 L35363462434.82 L39140636821.0  L64076393781.102L67529247213.10200000=00D00I00J00S00TS1V3bs12V02V1S3bs11HS3bs1SS3DST3bs1F". (* [comment removed for export] *)
  Lemma sum_amemsetA28_okO (kd : nat) (DST : Z) (CS : Z -> Prop) : ltac2:(CDefT.buildp (gd_tbl_LxA_sums ()) "P,(34.P,$4.Sp(35.$26.VR,VHIA,Vh,)O1.)P,(34.$4.(36.$4.O3.VGS,=)O2.)P,(37.(38.VR,)(39.$3:.VLB,(3;.VLF,))(3<.VR,)(3=.$26.VR,VHIA,Vh,)O2.+1<.)(3>.$26.(3?.VR,)VGS,VOPS,O1.(40.&1<.O3.))")
(* [comment removed for export] *).
  Proof. intros ECS GD CW. subst CS. apply apply_summary_soundO. amemset_valid 28 kd DST GD CW. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060@L1632069692.82  L22636553186.82 L38692635477.0  L64076393781.102L6732944102.79  L67529247213.10200000=00B00C00L00S00TS1V3bs12V02V1S3bs1SS3DST3bs1S3bs11HF". (* [comment removed for export] *)
  Lemma sum_amemsetA32_okO (kd : nat) (DST : Z) (CS : Z -> Prop) : ltac2:(CDefT.buildp (gd_tbl_LxA_sums ()) "P,(34.P,$4.Sp(35.$26.VR,VHIA,Vh,)O1.)P,(34.$4.(36.$4.O3.VGS,=)O2.)P,(37.(38.VR,)(39.$3:.VLB,(3;.VLF,))(3<.VR,)(3=.$26.VR,VHIA,Vh,)O2.+20.)(3>.$26.(3?.VR,)VGS,VOPS,O1.(40.&20.O3.))")
(* [comment removed for export] *).
  Proof. intros ECS GD CW. subst CS. apply apply_summary_soundO. amemset_valid 32 kd DST GD CW. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060@L1632069692.82  L34953352546.82 L38820635861.0  L51825038694.79 L64076393781.102L67529247213.10200000=00B00C00J00S00TS1V3bs12V02V1S3bs1SS3bs11HS3DST3bs1F". (* [comment removed for export] *)
  Lemma sum_amemsetA40_okO (kd : nat) (DST : Z) (CS : Z -> Prop) : ltac2:(CDefT.buildp (gd_tbl_LxA_sums ()) "P,(34.P,$4.Sp(35.$26.VR,VHIA,Vh,)O1.)P,(34.$4.(36.$4.O3.VGS,=)O2.)P,(37.(38.VR,)(39.$3:.VLB,(3;.VLF,))(3<.VR,)(3=.$26.VR,VHIA,Vh,)O2.+28.)(3>.$26.(3?.VR,)VGS,VOPS,O1.(40.&28.O3.))")
(* [comment removed for export] *).
  Proof. intros ECS GD CW. subst CS. apply apply_summary_soundO. amemset_valid 40 kd DST GD CW. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060@L1533269218.82  L1632069692.82  L38436634709.0  L53959138278.79 L64076393781.102L67529247213.10200000500B00C00J00S00TS3bs1S1V3bs12V02V1SS3bs11HS3DST3bs1F". (* [comment removed for export] *)
  Lemma sum_amemsetA48_okO (kd : nat) (DST : Z) (CS : Z -> Prop) : ltac2:(CDefT.buildp (gd_tbl_LxA_sums ()) "P,(34.P,$4.Sp(35.$26.VR,VHIA,Vh,)O1.)P,(34.$4.(36.$4.O3.VGS,=)O2.)P,(37.(38.VR,)(39.$3:.VLB,(3;.VLF,))(3<.VR,)(3=.$26.VR,VHIA,Vh,)O2.+30.)(3>.$26.(3?.VR,)VGS,VOPS,O1.(40.&30.O3.))")
(* [comment removed for export] *).
  Proof. intros ECS GD CW. subst CS. apply apply_summary_soundO. amemset_valid 48 kd DST GD CW. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060@L15250729190.79 L1632069692.82  L40228640085.0  L64076393781.102L67529247213.102L982933986.82   00000700D00E00N00O00TS3bs11HS1V3bs12V02V1SS3DST3bs1FS3bs1". (* [comment removed for export] *)
  Lemma sum_amemsetA64_okO (kd : nat) (DST : Z) (CS : Z -> Prop) : ltac2:(CDefT.buildp (gd_tbl_LxA_sums ()) "P,(34.P,$4.Sp(35.$26.VR,VHIA,Vh,)O1.)P,(34.$4.(36.$4.O3.VGS,=)O2.)P,(37.(38.VR,)(39.$3:.VLB,(3;.VLF,))(3<.VR,)(3=.$26.VR,VHIA,Vh,)O2.+40.)(3>.$26.(3?.VR,)VGS,VOPS,O1.(40.&40.O3.))")
(* [comment removed for export] *).
  Proof. intros ECS GD CW. subst CS. apply apply_summary_soundO. amemset_valid 64 kd DST GD CW. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060@L1632069692.82  L21012710114.82 L39972639317.0  L62493151718.79 L64076393781.102L67529247213.10200000=00B00C00J00S00TS1V3bs12V02V1S3bs1SS3bs11HS3DST3bs1F". (* [comment removed for export] *)
  Lemma sum_amemsetA80_okO (kd : nat) (DST : Z) (CS : Z -> Prop) : ltac2:(CDefT.buildp (gd_tbl_LxA_sums ()) "P,(34.P,$4.Sp(35.$26.VR,VHIA,Vh,)O1.)P,(34.$4.(36.$4.O3.VGS,=)O2.)P,(37.(38.VR,)(39.$3:.VLB,(3;.VLF,))(3<.VR,)(3=.$26.VR,VHIA,Vh,)O2.+50.)(3>.$26.(3?.VR,)VGS,VOPS,O1.(40.&50.O3.))")
(* [comment removed for export] *).
  Proof. intros ECS GD CW. subst CS. apply apply_summary_soundO. amemset_valid 80 kd DST GD CW. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060@L1632069692.82  L328567142.79   L37123320162.82 L37796632789.0  L64076393781.102L67529247213.10200000=00D00I00J00S00TS1V3bs12V02V1S3bs11HS3bs1SS3DST3bs1F". (* [comment removed for export] *)
  Lemma sum_amemsetA232_okO (kd : nat) (DST : Z) (CS : Z -> Prop) : ltac2:(CDefT.buildp (gd_tbl_LxA_sums ()) "P,(34.P,$4.Sp(35.$26.VR,VHIA,Vh,)O1.)P,(34.$4.(36.$4.O3.VGS,=)O2.)P,(37.(38.VR,)(39.$3:.VLB,(3;.VLF,))(3<.VR,)(3=.$26.VR,VHIA,Vh,)O2.+>8.)(3>.$26.(3?.VR,)VGS,VOPS,O1.(40.&>8.O3.))")
(* [comment removed for export] *).
  Proof. intros ECS GD CW. subst CS. apply apply_summary_soundO. amemset_valid 232 kd DST GD CW. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060@L1632069692.82  L29604608213.0  L54539536738.82 L64076393781.102L657123686.79   L67529247213.10200000=00>00C00L00S00TS1V3bs12V02V1SS3bs1S3DST3bs1S3bs11HF". (* [comment removed for export] *)
  Lemma sum_amemsetA744_okO (kd : nat) (DST : Z) (CS : Z -> Prop) : ltac2:(CDefT.buildp (gd_tbl_LxA_sums ()) "P,(34.P,$4.Sp(35.$26.VR,VHIA,Vh,)O1.)P,(34.$4.(36.$4.O3.VGS,=)O2.)P,(37.(38.VR,)(39.$3:.VLB,(3;.VLF,))(3<.VR,)(3=.$26.VR,VHIA,Vh,)O2.+2>8.)(3>.$26.(3?.VR,)VGS,VOPS,O1.(40.&2>8.O3.))")
(* [comment removed for export] *).
  Proof. intros ECS GD CW. subst CS. apply apply_summary_soundO. amemset_valid 744 kd DST GD CW. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060@L1632069692.82  L39019453158.79 L53103950818.82 L57124690773.0  L64076393781.102L67529247213.10200000=00D00I00J00S00TS1V3bs12V02V1S3bs11HS3bs1SS3DST3bs1F". (* [comment removed for export] *)
  Lemma sum_amemsetA1440_okO (kd : nat) (DST : Z) (CS : Z -> Prop) : ltac2:(CDefT.buildp (gd_tbl_LxA_sums ()) "P,(34.P,$4.Sp(35.$26.VR,VHIA,Vh,)O1.)P,(34.$4.(36.$4.O3.VGS,=)O2.)P,(37.(38.VR,)(39.$3:.VLB,(3;.VLF,))(3<.VR,)(3=.$26.VR,VHIA,Vh,)O2.+5:0.)(3>.$26.(3?.VR,)VGS,VOPS,O1.(40.&5:0.O3.))")
(* [comment removed for export] *).
  Proof. intros ECS GD CW. subst CS. apply apply_summary_soundO. amemset_valid 1440 kd DST GD CW. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac amemset0_valid n kd DST GD CW CELLS :=
    unfold SUM_amemset0A, lxbs0, lxz1, lxz4, lxz7, lxz8, q; lx_sum_unfold;
    repeat match goal with |- context [Z.of_N ?w] => let k := eval cbv in (Z.of_N w) in change (Z.of_N w) with k end;
    let DSTp := fresh "DSTp" in let V := fresh "V" in let NN := fresh "NN" in let SPu := fresh "SPu" in let LO := fresh "LO" in
    let HT := fresh "HT" in let NA := fresh "NA" in let SL := fresh "SL" in let A0 := fresh "A0" in let bs1 := fresh "bs1" in
    let F := fresh "F" in let fc := fresh "fc" in let m := fresh "m" in
    intros DSTp V NN SPu LO HT NA SL A0 bs1 F fc m;
    intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31;
    let GD' := fresh "GD'" in let GHT := fresh "GHT" in let GNA := fresh "GNA" in let GSL := fresh "GSL" in
    intros [CSOK ALWF] _ MI GD' GHT GNA GSL R10 R11 R12 R2 ST HDST OD EA0 EV0 ENN V0 V1 SLLO LOSP SCR SEP SPTOP SP0 SP1 OQ0;
    change (DSTp = nth kd GS 0) in GD'; change (HT = nth 1 GS 0) in GHT; change (NA = nth 2 GS 0) in GNA; change (SL = nth 3 GS 0) in GSL;
    change (nth 0 OPS (fun _ => True) m) in OQ0;
    rewrite GD in GD'; rewrite G1 in GHT; rewrite G2 in GNA; rewrite G3 in GSL; rewrite O0 in OQ0; cbv beta in OQ0;
    subst DSTp HT NA SL NN; subst A0; subst V;
    let U2 := fresh "U2" in
    assert (U2 : bv_unsigned x2 = SPu) by (rewrite R2; apply uw64; assumption);
    let HU := fresh "HU" in pose proof (u8arr_of_rw_cells asegs m DST _ bs1 HDST) as HU;
    let LEN := fresh "LEN" in
    assert (LEN : Z.of_nat (length bs1) = n) by (let WF := fresh in destruct HDST as [[WF _] _]; cbn in WF; lia);
    let HI := fresh "HI" in
    pose proof (cw_top47_or asegs R HIA h LB LF m (arl_stklo R) DST n OQ0 CW ltac:(clear; lia)) as HI;
    eapply evtA_cut;
    [ destruct AMS as [AE|AE];
      [ eapply (artA_amemset asegs R HIA 0x68258 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m h LB LF DST 0 n LO bs1); rewrite ?U2;
        first [ left; symmetry; exact AE | eassumption | cbn in *; lia ]
      | eapply (artA_amemset asegs R HIA 0x68258 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m h LB LF DST 0 n LO bs1); rewrite ?U2;
        first [ right; symmetry; exact AE | eassumption | cbn in *; lia ] ]
    | cbv beta;
      let ms' := fresh "ms'" in let POST := fresh "POST" in
      intros ms' POST; unfold call_postA in POST;
      let MU := fresh "MU" in let WM := fresh "WM" in let HU' := fresh "HU'" in let ST' := fresh "ST'" in let HH' := fresh "HH'" in
      let MI' := fresh "MI'" in let m' := fresh "m'" in
      destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & -> & HU' & ST' & HH');
      apply evtA_done; rewrite U2 in MU, ST';
      apply (rw_cells_of_u8arr asegs) in HU'; rewrite repeat_length in HU';
      let k := eval cbv in (Z.to_nat n) in change (Z.to_nat n) with k in HU';
      apply (rw_cells_zeros asegs m' DST k CELLS) in HU'; [ | cbn; repeat split; reflexivity | reflexivity ];
      lx_sum_post;
      try (lazymatch goal with |- ?f 0%nat OPS ?d ?mm => change (nth 0%nat OPS d mm); rewrite O0; cbv beta; exact HH' end) ].

  Local Ltac2 Set LiaOrc.tbl := fun () => "0050@L39076636629.0  L56089036902.78 L57020145596.81 L64076393781.101L67529247213.10100000100800=00F00GSS3bs11HS3bs1S3DST3bs1F". (* [comment removed for export] *)
  Lemma sum_amemset0A24s_okO (kd : nat) (DST : Z) (CS : Z -> Prop) : ltac2:(CDefT.buildp (gd_tbl_LxA_sums ()) "P,(34.P,$4.Sp(35.$26.VR,VHIA,Vh,)O1.)P,(34.$4.(36.$4.O3.VGS,=)O2.)P,(37.(38.VR,)(39.$3:.VLB,(3;.VLF,))(3<.VR,)(3=.$26.VR,VHIA,Vh,)O2.+18.)(3>.$26.(3?.VR,)VGS,VOPS,O1.(41.&18.(2.$<.$42.(2.$<.$42.(2.$<.$43.(2.$<.$43.(7.$<.)))))O3.))")
(* [comment removed for export] *).
  Proof. intros ECS GD CW. subst CS. apply apply_summary_soundO.
         amemset0_valid 24 kd DST GD CW constr:([C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]). Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050@L39076636629.0  L56089036902.78 L57020145596.81 L64076393781.101L67529247213.10100000100800=00F00GSS3bs11HS3bs1S3DST3bs1F". (* [comment removed for export] *)
  Lemma sum_amemset0A24b_okO (kd : nat) (DST : Z) (CS : Z -> Prop) : ltac2:(CDefT.buildp (gd_tbl_LxA_sums ()) "P,(34.P,$4.Sp(35.$26.VR,VHIA,Vh,)O1.)P,(34.$4.(36.$4.O3.VGS,=)O2.)P,(37.(38.VR,)(39.$3:.VLB,(3;.VLF,))(3<.VR,)(3=.$26.VR,VHIA,Vh,)O2.+18.)(3>.$26.(3?.VR,)VGS,VOPS,O1.(41.&18.$44.O3.))")
(* [comment removed for export] *).
  Proof. intros ECS GD CW. subst CS. apply apply_summary_soundO.
         amemset0_valid 24 kd DST GD CW constr:([C8 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
                                                C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C8 (Z_to_bv 64 0)]). Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050@L39012636437.0  L57020145596.81 L57165256614.78 L64076393781.101L67529247213.10100000100600=00F00GSS3bs1S3bs11HS3DST3bs1F". (* [comment removed for export] *)
  Lemma sum_amemset0A20p_okO (kd : nat) (DST : Z) (CS : Z -> Prop) : ltac2:(CDefT.buildp (gd_tbl_LxA_sums ()) "P,(34.P,$4.Sp(35.$26.VR,VHIA,Vh,)O1.)P,(34.$4.(36.$4.O3.VGS,=)O2.)P,(37.(38.VR,)(39.$3:.VLB,(3;.VLF,))(3<.VR,)(3=.$26.VR,VHIA,Vh,)O2.+14.)(3>.$26.(3?.VR,)VGS,VOPS,O1.(41.&14.(2.$<.$43.(2.$<.$43.(2.$<.$42.(7.$<.))))O3.))")
(* [comment removed for export] *).
  Proof. intros ECS GD CW. subst CS. apply apply_summary_soundO.
         amemset0_valid 20 kd DST GD CW constr:([C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]). Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End SOX.

Section SOG.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Variables (GSX : list Z) (OPS : list (mem -> Prop)).
  Let GS : list Z := alloc_ceiling :: GSX.
  Hypothesis G1 : nth 1 GS 0 = htop asegs R HIA h.
  Hypothesis G2 : nth 2 GS 0 = arl_need_amem R.
  Hypothesis G3 : nth 3 GS 0 = arl_stklo R.
  Hypothesis O0 : nth 0 OPS (fun _ => True) = (fun m => HM asegs R HIA h LB LF m).
  Hypothesis GA : asn1_get_alg_stmtA asegs R HIA 0x9a9c0.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0120@L10080462640.162L10080462640.168L10730259282.122L12161533383.22 L13071194087.10 L13950453531.162L13950453531.168L14281088506.10 L15260915864.0  L15824345493.25 L15824346142.22 L20243917769.162L20243917769.168L20630679444.162L20630679444.168L21462821282.25 L21910927408.162L22372407886.162L22372407886.168L22804866563.10 L25271522275.16 L25273412207.168L26887523608.22 L28203547420.22 L28203548311.25 L28285773730.25 L30084834608.162L30084834608.168L35174387812.16 L35176311407.168L35980939678.25 L36088593770.168L37782002751.16 L38709599012.10 L39107896096.25 L39280637297.0  L42749616056.16 L43192147922.22 L45169315804.122L46362028405.22 L47846551420.10 L4819348681.162 L49755000201.10 L50202834992.162L50243717505.25 L50506983216.162L50506983216.168L5068751233.22  L52813803977.162L52813803977.168L55555154242.122L58377790768.162L58377790768.168L58754702168.122L60142021513.10 L61462588617.162L61490557645.162L61490557645.168L62633770346.168L62768330284.122L64891089353.162L64891089353.168L67528838909.162L67528838909.168L8167680969.162 L8167680969.168 00000`01P02202A02S03?03k04B04C04S04c05\06U07I08=08[09J0:>0;20;D0;f0<S0<Y0<n0=C0=a0>Z0?S0?f0@S0@h0AU0B?0BV0Bk0Bl0C\0Cf0DD0DV0Dm0E\0F00F_0Fo0G_0HO0H^0IN0J>0J_0KX0LQ0Lo0MC0N20N^0OJ0P70PU0QE0R50R60R70S00SiS2PP3ALG3PAR3SPu2bs3AL13AL23AL33SPA3SP05alen'2RcS2PP3ALG3PAR3SPu2bs3AL13AL23AL33SPA3SP05alen'2RcS2PP3ALG3PAR3BUF3SPu2LO2bs3DS43SP0S2bs1r2p'5plen'S3BUF1r4apw'2Hr2RNS2PP3ALG3PAR3SPu2bs3AL13AL23AL33SPA3SP01r2HrS2PP3ALG3PAR3SPu2bs3AL13AL23AL33SPA3SP01r2HrS1r2p'5plen'4ppw'2Hr2RNSS3BUF2bs1r2ap2F1S3BUF2bs1r2ap2F1S2PP3ALG3PAR3SPu2bs3AL13AL23AL33SPA3SP05atag'2Ra5apad'2RbS2PP3ALG3PAR3SPu2bs3AL13AL23AL33SPA3SP05atag'2Ra5apad'2RbS2PP3ALG3PAR3END1P3SPu2bs3AL13AL23AL33SPA3SP02p'3Hp'S2PP3ALG3PAR3END1P3SPu2bs3AL13AL23AL33SPA3SP02p'3Hp'S3BUF2bs4BUF01r5ptag'2pp2Re2FbS2PP3ALG3PAR3SPu2bs3AL13AL23AL33SPA3SP04ppw'2RhS2PP3ALG3PAR3END1P3SPu2bs3AL13AL23AL33SPA3SP02p'3Hp'S2PP3ALG3PAR3END1P3SPu2bs3AL13AL23AL33SPA3SP02p'3Hp'S3BUF1r4ppw'2Hr2RNS3BUF2bs4BUF02p'5ptag'5plen'2pp2F3S2PP3ALG3PAR3SPu2bs3AL13AL23AL33SPA3SP02pp2RhS2bs1rS2bs1r2p'5alen'2ap2F2S2bs1r2p'5alen'2ap2F2S3BUF2bs4BUF01r5plen'2pp2Rg2FbS2PP3ALG3PAR3SPu2bs3AL13AL23AL33SPA3SP05ptag'2Re5ppad'2RfS2PP3ALG3PAR3SPu2bs3AL13AL23AL33SPA3SP05ptag'2Re5ppad'2RfS3BUF2bs4BUF02ap2F1S2PP3ALG3PAR3SPu2bs3AL13AL23AL33SPA3SP02ap2RdS2bs1r2p'5plen'2pp2FeS2PP3ALG3PAR3SPu2bs3AL13AL23AL33SPA3SP02pp2RhS3END1P3BUF2bs2B42B32p'5alen'2ap3Hp'2Rc2F2S1r2p'5alen'4apw'2Hr2RNS2bs1r2p'5plen'2pp2FeSS3END1P3BUF2bs2B42B32p'5ptag'5plen'2pp3Hp'2Rg2F3S3BUF2bs1rS2PP3ALG3PAR3SPu2LO2bs3DS23SP0S2bs1r5plen'2Rg2FlS1r2p'5plen'4ppw'2Hr2RNS2PP3ALG3PAR3SPu2bs3AL13AL23AL33SPA3SP04apw'2RdS1r5plen'4ppw'2Hr2RNS2PP3ALG3PAR3SPu2bs3AL13AL23AL33SPA3SP04apw'2RdS3BUF2bs1r2pp2FbS2PP3ALG3PAR3SPu2bs3AL13AL23AL33SPA3SP05plen'2RgS2PP3ALG3PAR3SPu2bs3AL13AL23AL33SPA3SP05plen'2RgS2bs1r2p'5plen'S2PP3ALG3PAR3SPu2bs3AL13AL23AL33SPA3SP05plen'2RgS2PP3ALG3PAR3SPu2bs3AL13AL23AL33SPA3SP05plen'2RgS1R2PP3ALG3PAR3SPu2LO2bs4LOSP3SP0S2PP3ALG3PAR3SPu2bs3AL13AL23AL33SPA3SP05atag'2Ra5apad'2RbS2PP3ALG3PAR3SPu2bs3AL13AL23AL33SPA3SP05atag'2Ra5apad'2RbS2PP3ALG3PAR3SPu2LO2bs3DS33SP0S1r5ptag'4ppw'2Hr2RNS2PP3ALG3PAR3SPu2bs3AL13AL23AL33SPA3SP04ppw'2RhS2PP3ALG3PAR3SPu2bs3AL13AL23AL33SPA3SP01r2HrS2PP3ALG3PAR3SPu2bs3AL13AL23AL33SPA3SP01r2HrS2PP3ALG3PAR3SPu2bs3AL13AL23AL33SPA3SP02ap2RdS2PP3ALG3PAR3SPu2LO2bs3DS13SP0S2PP3ALG3PAR3SPu2bs3AL13AL23AL33SPA3SP05alen'2RcS2PP3ALG3PAR3SPu2bs3AL13AL23AL33SPA3SP05alen'2RcFFS2PP3ALG3PAR3SPu2bs3AL13AL23AL33SPA3SP05ptag'2Re5ppad'2RfS2PP3ALG3PAR3SPu2bs3AL13AL23AL33SPA3SP05ptag'2Re5ppad'2Rf". (* [comment removed for export] *)
  Lemma sum_getalgA_okO (kp ka kr : nat) (PP ALG PAR : Z) (CS : Z -> Prop) : ltac2:(CDefT.buildp (gd_tbl_LxA_sums ()) "P,(34.P,$4.Sp(35.$26.VR,VHIA,Vh,)O1.)P,(34.$4.(36.$4.O7.VGS,=)O4.)P,(34.$4.(36.$4.O6.VGS,=)O3.)P,(34.$4.(36.$4.O5.VGS,=)O2.)P,(37.(38.VR,)(39.$3:.VLB,(3;.VLF,))(3<.VR,)(3=.$26.VR,VHIA,Vh,)O4.+8.)P,(37.(38.VR,)(39.$3:.VLB,(3;.VLF,))(3<.VR,)(3=.$26.VR,VHIA,Vh,)O3.+18.)P,(37.(38.VR,)(39.$3:.VLB,(3;.VLF,))(3<.VR,)(3=.$26.VR,VHIA,Vh,)O2.+18.)(3>.$26.(3?.VR,)VGS,VOPS,O1.(45.O7.O6.O5.))")
(* [comment removed for export] *).
  Proof.
    intros ECS GP GAl GR CW1 CW2 CW3. subst CS. apply apply_summary_soundO. unfold SUM_getalgA, q. lx_sum_unfold.
    intros PPp END ALGp PARp P BUF LEN SPu LO ATAG APAD ALEN APW PTAG PPAD PLEN PPW HT NA SL A0 A2 A3 bs F fc m.
    intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
    intros [CSOK ALWF] _ MI GDp GDa GDr GHT GNA GSL R10 R11 R12 R13 R2 ST HPP HALG HPAR [HBUF HLEN] OPP OALG OPAR OBUF OLEN.
    intros EA0 EA2 EA3 B1 B2 B3 B4 D1 D2 D3 D4 D5 D6 AL1 AL2 AL3 PP0 ALG0 PAR0 BUF0 SLLO LOSP SPTOP SPA DS1 DS2 DS3 DS4 SP0 SP1 OQ0.
    change (PPp = nth kp GS 0) in GDp; change (ALGp = nth ka GS 0) in GDa; change (PARp = nth kr GS 0) in GDr;
    change (HT = nth 1 GS 0) in GHT; change (NA = nth 2 GS 0) in GNA; change (SL = nth 3 GS 0) in GSL;
    change (nth 0 OPS (fun _ => True) m) in OQ0.
    rewrite GP in GDp; rewrite GAl in GDa; rewrite GR in GDr; rewrite G1 in GHT; rewrite G2 in GNA; rewrite G3 in GSL; rewrite O0 in OQ0; cbv beta in OQ0.
    subst PPp ALGp PARp HT NA SL LEN. subst A0 A2 A3.
    assert (U2 : bv_unsigned x2 = SPu) by (rewrite R2; apply uw64; assumption).
    pose proof GA as SP. unfold asn1_get_alg_stmtA in SP.
    eapply evtA_cut.
    { eapply (SP h LB LF x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m PP ALG PAR P END BUF LO bs
                (Z_to_bv 64 ATAG) (Z_to_bv 64 APAD) (Z_to_bv 64 ALEN) (Z_to_bv 64 APW) (Z_to_bv 64 PTAG) (Z_to_bv 64 PPAD) (Z_to_bv 64 PLEN) (Z_to_bv 64 PPW));
        rewrite ?U2; first [ eassumption | cbn in *; lia ]. }
    clear SP. cbv beta. intros ms' POST. unfold asn1_get_alg_postA in POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & r & p' &
                      atag' & apad' & alen' & apw' & ptag' & ppad' & plen' & ppw' & -> & MU & WM & MI' & -> & Hr & HPP' & HALG' & HPAR' & ST' & HH' & Hp' & HL0).
    apply evtA_done. rewrite U2 in MU, ST'.
    pose proof (lx_urange atag') as Ra. pose proof (lx_urange apad') as Rb. pose proof (lx_urange alen') as Rc. pose proof (lx_urange apw') as Rd.
    pose proof (lx_urange ptag') as Re. pose proof (lx_urange ppad') as Rf. pose proof (lx_urange plen') as Rg. pose proof (lx_urange ppw') as Rh.
    (* [comment removed for export] *)
    destruct (Z.eq_dec r 0) as [R0|RN].
    - destruct (HL0 R0) as (ap & pp & Eap & Epp & F1 & F2 & F3).
      rewrite Eap, Epp in *. rewrite (uw64 ap) in * by (clear - F1 F2 Hp' B1 B2 B3 B4 BUF0 Rc; unfold two64; lia).
      rewrite (uw64 pp) in * by (clear - F3 Hp' B1 B2 B3 B4 BUF0 Rg; unfold two64; lia).
      assert (SF : (r + 1 <= 0 \/ BUF <= ap) /\ (r + 1 <= 0 \/ ap + bv_unsigned alen' <= p')
                   /\ (pp = 0 \/ r + 1 <= 0 \/ BUF <= pp)
                   /\ (pp = 0 \/ r + 1 <= 0 \/ pp + bv_unsigned plen' <= p')
                   /\ (pp = 0 \/ r + 1 <= 0 \/ p' <= pp + bv_unsigned plen')
                   /\ (bv_unsigned plen' = 0 \/ r + 1 <= 0 \/ 1 <= pp)
                   /\ (bv_unsigned ptag' = 0 \/ r + 1 <= 0 \/ 1 <= pp)).
      { clear - R0 F1 F2 F3 Hp' B1 B2 B3 B4 BUF0 Rc Rg Re.
        destruct F3 as [(-> & Fl & ->)|(Fb & Fe)]; [ rewrite (uw64 0) in * by (unfold two64; clear; lia) | ]; repeat split; lia. }
      destruct SF as (SF1 & SF2 & SF3 & SF4 & SF5 & SF6 & SF7).
      clear D1 D2 D3 D4 D5 D6 DS1 DS2 DS3 DS4 HL0 F3.
      lx_sum_post.
      all: try (lazymatch goal with |- ?f 0%nat OPS ?d ?mm => change (nth 0%nat OPS d mm); rewrite O0; cbv beta; exact HH' end).
    - assert (SF : (r + 1 <= 0 \/ BUF <= bv_unsigned apw') /\ (r + 1 <= 0 \/ bv_unsigned apw' + bv_unsigned alen' <= p')
                 /\ (bv_unsigned ppw' = 0 \/ r + 1 <= 0 \/ BUF <= bv_unsigned ppw')
                 /\ (bv_unsigned ppw' = 0 \/ r + 1 <= 0 \/ bv_unsigned ppw' + bv_unsigned plen' <= p')
                 /\ (bv_unsigned ppw' = 0 \/ r + 1 <= 0 \/ p' <= bv_unsigned ppw' + bv_unsigned plen')
                 /\ (bv_unsigned plen' = 0 \/ r + 1 <= 0 \/ 1 <= bv_unsigned ppw')
                 /\ (bv_unsigned ptag' = 0 \/ r + 1 <= 0 \/ 1 <= bv_unsigned ppw')) by (clear - RN Hr; repeat split; lia).
      destruct SF as (SF1 & SF2 & SF3 & SF4 & SF5 & SF6 & SF7).
      clear D1 D2 D3 D4 D5 D6 DS1 DS2 DS3 DS4 HL0.
      lx_sum_post.
      all: try (lazymatch goal with |- ?f 0%nat OPS ?d ?mm => change (nth 0%nat OPS d mm); rewrite O0; cbv beta; exact HH' end).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End SOG.

Section SOL.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Variables (GSX : list Z) (OPS : list (mem -> Prop)).
  Let GS : list Z := alloc_ceiling :: GSX.
  Hypothesis G1 : nth 1 GS 0 = htop asegs R HIA h.
  Hypothesis G3 : nth 3 GS 0 = arl_stklo R.
  Hypothesis O0 : nth 0 OPS (fun _ => True) = (fun m => HM asegs R HIA h LB LF m).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00F0@L10735319650.107L16582993888.110L16585183589.111L19221018620.106L1958463078.109 L22582847566.98 L23731244404.110L23733451761.111L23735094998.105L44164697160.138L44870654275.138L45261830903.108L47783816100.114L49724159872.138L52679951748.114L56484586670.99 L61492574438.138L63203728362.110L63214316911.111L65390931599.138L67530982614.138L8135324285.100 00001N02502\03_04T04]05F05o06X07@07h08f09D0:S0;10;:0;b0<a0=`0>o0?00?9S3OID3EXT3LEN1P3BUF4BLEN3SPu2LO2bs4HLEN2BP2L02B22D22D13AL13AL23NZ13NZ23SPA3DS13DS23DS33SP03D2PS3OID3EXT3LEN3SPu2bs2L03AL13AL23SPA3SP0S3OID3EXT3LEN3SPu2bs2L03AL13AL23SPA3SP0S3OID3EXT3LEN1P3BUF4BLEN3SPu2bs2BP2L02B22D23AL13AL23NZ13NZ23SPA3SP0S3OID3EXT1P3BUF3SPu2bs2BP3AL13AL23NZ13NZ23NZ33SPA3SP0S4OIDp2bsS3OID3EXT1P3BUF3SPu2bs2BP3AL13AL23SPA3SP0S3OID3EXT1P3BUF3SPu2bs2BP3AL13AL23SPA3SP0S3OID3EXT1P3BUF3SPu2bs2BP3AL13AL23SPA3SP0S3OID3EXT3SPu2bs3AL13AL23SPA3SP02xs1v2VRS3OID3EXT3SPu2bs3AL13AL23SPA3SP02xs1v2VRS3OID3EXT3LEN1P3BUF4BLEN3SPu2bs2B23AL13AL23NZ13NZ23SPA3P473SP0S3OID3EXT3SPu2LO2bs3DS23SP02xsS3OID3EXT3LEN1P3BUF4BLEN3SPu2bs2BP2B22D23AL13AL23NZ13NZ23SPA3SP03D2P2xs2XL1r2HrS3OID3EXT3SPu2LO2bs3DS13SP02xsS4OIDp2bsS3OID3EXT3SPu2bs3AL13AL23SPA3SP02xs1r2HrS3OID3EXT3LEN1P3BUF4BLEN3SPu2bs4HLEN2B23AL13AL23NZ13NZ23SPA3SP0S3OID3EXT3LEN1P3BUF4BLEN3SPu2bs4HLEN2B23AL13AL23NZ13NZ23SPA3SP0S3OID3EXT3LEN1P3BUF4BLEN3SPu2bs2BP2B22D23AL13AL23NZ13NZ23SPA3SP03D2P2xs2XL1r2HrFS4OIDp2bs". (* [comment removed for export] *)
  Lemma sum_oidlook1A_okO (pc stack : Z) (ko ke kb : nat) (OID EXT : Z) (CS : Z -> Prop) : ltac2:(CDefT.buildp (gd_tbl_LxA_sums ()) "P,(46.$26.VR,VHIA,O8.O7.)P,(34.P,$4.Sp(35.$26.VR,VHIA,Vh,)O1.)P,(34.$4.(36.$4.O6.VGS,=)O3.)P,(34.$4.(36.$4.O5.VGS,=)O2.)P,(34.$4.(36.$4.O4.VGS,=)(47.VR,))P,(37.(38.VR,)(39.$3:.VLB,(3;.VLF,))(3<.VR,)(3=.$26.VR,VHIA,Vh,)O2.+4.)(3>.$26.(3?.VR,)VGS,VOPS,O1.(48.O8.O7.O6.O5.O4.))")
(* [comment removed for export] *).
  Proof.
    intros OL ECS GO GE GB CW. subst CS. apply apply_summary_soundO. unfold SUM_oidlook1A, q. lx_sum_unfold.
    intros OIDp EXTp TG PD LEN P BUF BLEN SPu LO HT NB SL V0 A0 A1 bs F fc m.
    intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
    intros [CSOK ALWF] _ MI GDo GDe GHT GNB GSL R10 R11 R2 ST HO1 HO2 HO3 HO4 HEXT [HBUF HLEN] OOID OP OEXT.
    assert (HO34 : rw_cells asegs m (OIDp + 8) [C8 (Z_to_bv 64 LEN); C8 (Z_to_bv 64 P)]).
    { apply (proj2 (rw_cells_app asegs m (OIDp + 8) [C8 (Z_to_bv 64 LEN)] [C8 (Z_to_bv 64 P)])). split; [exact HO3|].
      replace (OIDp + 8 + Z.of_nat (cells_size [C8 (Z_to_bv 64 LEN)])) with (OIDp + 16)
        by (cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; lia). exact HO4. }
    assert (HO234 : rw_cells asegs m (OIDp + 4) [C4 (Z_to_bv 64 PD); C8 (Z_to_bv 64 LEN); C8 (Z_to_bv 64 P)]).
    { apply (proj2 (rw_cells_app asegs m (OIDp + 4) [C4 (Z_to_bv 64 PD)] [C8 (Z_to_bv 64 LEN); C8 (Z_to_bv 64 P)])). split; [exact HO2|].
      replace (OIDp + 4 + Z.of_nat (cells_size [C4 (Z_to_bv 64 PD)])) with (OIDp + 8)
        by (cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; lia). exact HO34. }
    assert (HOID : rw_cells asegs m OIDp [C4 (Z_to_bv 64 TG); C4 (Z_to_bv 64 PD); C8 (Z_to_bv 64 LEN); C8 (Z_to_bv 64 P)]).
    { apply (proj2 (rw_cells_app asegs m OIDp [C4 (Z_to_bv 64 TG)] [C4 (Z_to_bv 64 PD); C8 (Z_to_bv 64 LEN); C8 (Z_to_bv 64 P)])). split; [exact HO1|].
      replace (OIDp + Z.of_nat (cells_size [C4 (Z_to_bv 64 TG)])) with (OIDp + 4)
        by (cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; lia). exact HO234. }
    clear HO1 HO2 HO3 HO4 HO34 HO234.
    intros EA0 EA1 BP L0 B2 D1 D2 AL1 AL2 NZ1 NZ2 NZ3 SLLO LOSP SPTOP SPA DS1 DS2 DS3 P47 SP0 SP1 OQ0.
    change (OIDp = nth ko GS 0) in GDo; change (EXTp = nth ke GS 0) in GDe; change (HT = nth 1 GS 0) in GHT;
    change (NB = nth kb GS 0) in GNB; change (SL = nth 3 GS 0) in GSL; change (nth 0 OPS (fun _ => True) m) in OQ0.
    rewrite GO in GDo; rewrite GE in GDe; rewrite G1 in GHT; rewrite GB in GNB; rewrite G3 in GSL; rewrite O0 in OQ0; cbv beta in OQ0.
    subst OIDp EXTp HT NB SL. subst A0 A1.
    assert (U2 : bv_unsigned x2 = SPu) by (rewrite R2; apply uw64; assumption).
    assert (B1 : BUF <= P) by lia.
    assert (D2P : EXT + 4 <= P \/ P + LEN <= EXT) by lia.
    assert (DS3P : P + LEN <= LO \/ SPu <= P) by lia.
    assert (P47P : P + LEN + 8 <= 2^47) by lia.
    assert (NZ3P : 0 < P) by lia.
    set (xs := firstn (Z.to_nat LEN) (skipn (Z.to_nat (P - BUF)) bs)).
    assert (HXS : bytes_at asegs m P xs) by (subst xs; eapply bytes_at_sub; [exact HBUF | lia | lia | lia]).
    assert (XL : Z.of_nat (length xs) = LEN) by (subst xs; apply bytes_at_sub_length; lia).
    clearbody xs.
    pose proof OL as SP. unfold oid_lookup1_stmtA in SP.
    eapply evtA_cut.
    { eapply (SP h LB LF x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m OID EXT P LEN LO
                (Z_to_bv 64 TG) (Z_to_bv 64 PD) (Z_to_bv 64 V0) xs);
        unfold buf_cells; rewrite ?U2; first [ eassumption | cbn in *; lia ]. }
    clear SP. cbv beta. intros ms' POST. unfold oid_lookup1_postA in POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & r & v & -> & MU & WM & MI' & -> & Hr & HEXT' & ST' & HH').
    apply evtA_done. pose proof (lx_urange v) as VR. rewrite U2 in MU, ST'.
    unfold MBEDTLS_ERR_OID_NOT_FOUND in Hr.
    lx_sum_post.
    all: try (lazymatch goal with |- ?f 0%nat OPS ?d ?mm => change (nth 0%nat OPS d mm); rewrite O0; cbv beta; exact HH' end).
    all: try lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End SOL.


(* [comment removed for export] *)
Definition SUM_bcmpA (pat : Z) (n : Z) (j : nat) (kq kb kbl knb : nat) : summary := ltac2:(CDefT.buildp (gd_tbl_LxA_sums ()) "(2>.+58704.$1.#:.#?.#0.(2.(3.$4.$5.)(6.$4.$5.+;.^1.)(2.(3.$4.$5.)(6.$4.$5.+<.^2.)(2.(3.$4.$5.)(6.$4.$5.+2.^5.)(2.(3.$4.$5.)(6.$4.$5.+:.^:.)(7.(3.$4.$5.))))))(2.(3.$5.$22.)(6.$5.$22.^3.O3.)(2.(3.$5.$22.)(6.$5.$22.^4.O2.)(2.(3.$5.$22.)(6.$5.$22.^7.#1.)(2.(3.$5.$22.)(6.$5.$22.^8.O1.)(2.(3.$5.$22.)(6.$5.$22.^9.#3.)(7.(3.$5.$22.)))))))(2?.$5.)(7.$9.)(8.(3.$5.$5.)(6.$5.$5.^6.^5.))(7.(3.(3.$5.$5.)$5.))(2.$9.(>.(;.^3.)(;.^4.))(7.$9.))(2.$11.(31.(;.^:.)(?.O7.))(2.$11.(31.(;.^2.)(?.O6.))(2.$11.(12.(;.^3.)(;.^1.))(2.$11.(12.(13.(;.^1.)(;.^2.))(13.(;.^3.)(;.^4.)))(2.$11.(12.(;.^9.)(;.^6.))(2.$11.(12.(;.^6.)(13.(;.^5.)(1;.-1.(;.^8.))))(2.$11.(1:.(;.^6.)(13.(;.^5.)(1;.-1.(;.^6.))))(2.$11.(16.(;.^1.)(;.^2.)(;.^6.)(13.(;.^5.)(1;.-1.(;.^6.))))(2.$11.(17.(;.^4.)(;.^3.)(;.^4.)(;.^6.)(13.(;.^5.)(1;.-1.(;.^6.))))(2.$11.(33.(;.^2.)(13.(13.(;.^1.)(;.^2.))(?.+8.))(?.(15.+2.+2?.))(?.+1.)(?.=))(2.$11.(12.(;.^5.)(;.^7.))(2.$11.(12.(?.=)(;.^5.))(2.$11.(12.(;.^5.)(?.(1<.$1=.+1.)))(7.$11.))))))))))))))(2.(3.$1>.$1>.)(6.$1>.$1>.(;.^6.)(;.^5.))(7.(3.$1>.$1>.)))(2.(3.$4.$5.)(6.$4.$5.+:.^;.)(2.(3.$4.$5.)(6.$4.$5.+5.^<.)(2.(3.$4.$5.)(6.$4.$5.+6.^=.)(2.(3.$4.$5.)(6.$4.$5.+7.^>.)(2.(3.$4.$5.)(6.$4.$5.+;.^?.)(2.(3.$4.$5.)(6.$4.$5.+<.^10.)(2.(3.$4.$5.)(6.$4.$5.+=.^11.)(2.(3.$4.$5.)(6.$4.$5.+>.^12.)(2.(3.$4.$5.)(6.$4.$5.+?.^13.)(2.(3.$4.$5.)(6.$4.$5.+10.^14.)(2.(3.$4.$5.)(6.$4.$5.+11.^15.)(2.(3.$4.$5.)(6.$4.$5.+1<.^16.)(2.(3.$4.$5.)(6.$4.$5.+1=.^17.)(2.(3.$4.$5.)(6.$4.$5.+1>.^18.)(2.(3.$4.$5.)(6.$4.$5.+1?.^19.)(7.(3.$4.$5.)))))))))))))))))(2.$9.(1?.(;.^6.)(;.^5.))(7.$9.))(2.$11.(12.(?.=)(;.^;.))(2.$11.(12.(;.^;.)(?.(1<.$1=.+1.)))(2.$11.(49.O5.(2.$1>.(;.^;.)(2.$1>.(;.^1.)(7.$1>.))))(7.$11.))))(2.$22.#0.(2.$22.O4.(7.$22.))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition bcmp_prop (BUF : Z) (bs : list byte) (n : Z) (ps : list byte) : list Z -> Prop :=
  fun l => match l with r :: qv :: _ => (r = 0 <-> ps = firstn (Z.to_nat n) (skipn (Z.to_nat (qv - BUF)) bs)) | _ => True end.

Section SBCMP.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Variables (GSX : list Z) (OPSX : list (mem -> Prop)) (LAWS : list (list (Z * Z) -> mem -> mem -> Prop)) (PROPS : list (list Z -> Prop)).
  Let GS : list Z := alloc_ceiling :: GSX.
  Let OPS : list (mem -> Prop) := (fun m => HM asegs R HIA h LB LF m) :: OPSX.
  Hypothesis G1 : nth 1 GS 0 = htop asegs R HIA h.
  Hypothesis G3 : nth 3 GS 0 = arl_stklo R.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00A0@L12963415410.133L14721197074.109L2424813989.105 L2427054789.105 L26917761098.107L28960822020.12 L28962926396.12 L35341488937.105L35343958089.105L47756206852.102L49279934426.109L5379818758.12  L55809163969.109L58243311243.133L7320571669.107 L7324848883.105 L7326794131.105 00000A00Z00h01601R02502602T03203C03i04<04[04l05@05Q05bS2bs2ps2qs3a0'2RaS1n2bs2ps1Q3SPu2LO3DS12qsS1n2bs2ps4NPOSS1n2bs2ps4NPOSS1n4BUFg5BLENg2bs2ps1Q2B22qsS1n4BUFg5BLENg2bs4NPOS1Q2LO2B22B11HFS1n4BUFg5BLENg2bs2ps4HLEN1Q2B2S1n4BUFg5BLENg2bs2ps4HLEN1Q2B2S3pat1n2bs2ps3P47S1R3pat1n2bs2ps3PLO3ALO3SPu2LO4SLLO2qsS4BUFg2bs3SPu2LO2H0S3pat1n2bs2ps4NPOS3P472qs1Q3Q47S2bs2ps2qs3a0'2RaS4BUFg2bs2ps1Q2B12qsS4BUFg2bs2ps1Q2B1S4BUFg2bs2ps1Q2B1". (* [comment removed for export] *)
  Lemma sum_bcmpA_okP (pat n : Z) (j : nat) (kq kb kbl knb : nat) (BUFg BLENg : Z) (bs : list byte) (ps : list byte) (CS : Z -> Prop) : ltac2:(CDefT.buildp (gd_tbl_LxA_sums ()) "P,(34.P,$4.Sp(35.$26.VR,VHIA,Vh,)O1.)P,(34.$4.(4:.VR,)+58704.)P,(34.$4.(36.$4.O8.VGS,=)O5.)P,(34.$4.(36.$4.O7.VGS,=)O4.)P,(34.$4.(36.$4.O6.VGS,=)(47.VR,))P,(34.$4.O4.(4;.(4<.(4=.&8.)O3.)))P,(34.P,P,(4=.&40.)(4>.(4=.&8.))Sp(36.P,P,(4=.&40.)(4>.(4=.&8.))SpO9.VOPS,L,P,(4=.&40.)(4>.(4=.&8.))$4?.)Lm,P,(4=.&40.)(4>.(4=.&8.))(50.$26.R1.O5.O3.))P,(34.P,(51.$4.)Sp(36.P,(51.$4.)SpO:.VPROPS,L,(51.$4.)$4?.)(52.O5.O3.O;.O2.))P,(34.$53.(54.$26.O<.O2.)$1.)P,(34.$4.(4;.(4<.(4=.&8.)O2.))O;.)P,(55.=O;.)P,(55.O;.(15.+2.+28.))P,(56.=O<.)P,(56.(57.(57.O<.O;.)+8.)(15.+2.+2?.))P,(56.(57.O<.O;.)(58.(38.VR,)))P,(56.(58.(38.VR,))(3<.VR,))P,(59.O1.)P,Ph',(5:.$26.VR,VHIA,)PLB',(51.$3:.)PLF',(51.$3:.)Pm',P,(4=.&40.)(4>.(4=.&8.))P,(5;.$26.VR,VHIA,R4.R3.R2.R1.)(5<.$26.(3?.VR,)R2.)P,(34.$53.(5=.O<.O;.)$1.)(5>.$26.(3?.VR,)VGS,VOPS,VLAWS,VPROPS,O1.(5?.O<.O;.O:.O9.O8.O7.O6.))")
(* [comment removed for export] *).
  Proof.
    intros ECS MCI GB GBL GNB HLEN OQK PJ RB PL NPOS N40 P0 P47 PLO ALO ICS ISH INZ. subst CS. apply apply_summary_soundP.
    unfold SUM_bcmpA, q. lx_sum_unfold.
    intros Q N BUF BLEN SPu LO HT NB SL A0 F fc m.
    intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
    intros [CSOK ALWF] _ MI GDb GDbl GDht GDnb GDsl R11 R12 R2 R10 ST OBUF.
    intros EA0 EN B1 B2 SLLO LONB CRS DS1 DS4 Q47 SPTOP SP0 SP1 OQ0 OQ1.
    change (BUF = nth kb GS 0) in GDb; change (BLEN = nth kbl GS 0) in GDbl; change (HT = nth 1 GS 0) in GDht;
    change (NB = nth knb GS 0) in GDnb; change (SL = nth 3 GS 0) in GDsl; change (nth 0 OPS (fun _ => True) m) in OQ0;
    change (nth kq OPS (fun _ => True) m) in OQ1.
    rewrite GB in GDb; rewrite GBL in GDbl; rewrite G1 in GDht; rewrite GNB in GDnb; rewrite G3 in GDsl; rewrite OQK in OQ1.
    cbn [OPS nth] in OQ0. cbv beta in OQ1.
    subst BUF BLEN HT NB SL. subst A0 N.
    assert (U2 : bv_unsigned x2 = SPu) by (rewrite R2; apply uw64; assumption).
    (* [comment removed for export] *)
    pose proof (ro_image_bytes_at asegs m pat ps MI RB P0 ltac:(rewrite PL; lia)) as HPAT.
    pose proof (aobj_img asegs (arl_AL R) (hcs asegs R HIA h) m pat n ICS (ISH _ _ _ _ OQ0) INZ) as OPAT.
    (* [comment removed for export] *)
    set (qs := firstn (Z.to_nat n) (skipn (Z.to_nat (Q - BUFg)) bs)).
    assert (HQS : bytes_at asegs m Q qs) by (eapply (bytes_at_sub asegs m BUFg bs Q n OQ1); lia).
    assert (LENQ : Z.of_nat (length qs) = n) by (subst qs; apply bytes_at_sub_length; lia).
    assert (OQS : aobj asegs (arl_AL R) (hcs asegs R HIA h) m Q n) by (eapply aobj_sub; [ exact OBUF | lia | lia ]).
    pose proof (artA_bcmp asegs R HIA) as SP. rewrite MCI in SP.
    eapply evtA_cut.
    { eapply (SP x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m h LB LF pat Q n LO ps qs);
        rewrite ?U2; first [ eassumption | exact OQ0 | lia ]. }
    clear SP. cbv beta. intros ms' POST. unfold call_postA in POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & HRES & ST' & HH').
    apply evtA_done. rewrite U2 in MU, ST'.
    pose proof (lx_urange a0') as Ra.
    (* [comment removed for export] *)
    assert (OPQ : nth j PROPS (fun _ => True) [bv_unsigned a0'; Q]).
    { rewrite PJ. unfold bcmp_prop. subst qs. split.
      - intros E. apply (proj1 HRES). rewrite <- (lx_w64u a0'), E. reflexivity.
      - intros E. apply (proj2 HRES) in E. rewrite E. reflexivity. }
    (* [comment removed for export] *)
    assert (OPB : nth kq OPS (fun _ => True) m').
    { rewrite OQK. cbv beta. eapply (bytes_at_transport asegs [(LO, SPu)] m m' BUFg bs OQ1 MU).
      cbn [disjoint_from]. rewrite <- HLEN. clear - DS4 B1 B2 NPOS HLEN. intuition lia. }
    lx_sum_post.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End SBCMP.

(* [comment removed for export] *)
Section SBCMPQ.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Variables (GSX : list Z) (OPS : list (mem -> Prop)) (LAWS : list (list (Z * Z) -> mem -> mem -> Prop)) (PROPS : list (list Z -> Prop)).
  Let GS : list Z := alloc_ceiling :: GSX.
  Hypothesis G1 : nth 1 GS 0 = htop asegs R HIA h.
  Hypothesis G3 : nth 3 GS 0 = arl_stklo R.
  Hypothesis O0 : nth 0 OPS (fun _ => True) = (fun m => HMQ R HIA h LB LF m).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00A0@L12963415416.142L14721197074.117L2424813989.113 L2427054789.113 L26917761098.115L28960822020.12 L28962926396.12 L35341488937.113L35343958089.113L47756206852.110L49279934426.117L5379818758.12  L55809163969.117L58243311233.142L7320571669.115 L7324848883.113 L7326794131.113 00000A00Z00h01601R02502602T03203C03i04<04[04l05@05Q05bS2bs2ps2qs3a0'2RaS1n2bs2ps1Q3SPu2LO3DS12qsS1n2bs2ps4NPOSS1n2bs2ps4NPOSS1n4BUFg5BLENg2bs2ps1Q2B22qsS1n4BUFg5BLENg2bs4NPOS1Q2LO2B22B11HFS1n4BUFg5BLENg2bs2ps4HLEN1Q2B2S1n4BUFg5BLENg2bs2ps4HLEN1Q2B2S3pat1n2bs2ps3P47S1R3pat1n2bs2ps3PLO3ALO3SPu2LO4SLLO2qsS4BUFg2bs3SPu2LO2H0S3pat1n2bs2ps4NPOS3P472qs1Q3Q47S2bs2ps2qs3a0'2RaS4BUFg2bs2ps1Q2B12qsS4BUFg2bs2ps1Q2B1S4BUFg2bs2ps1Q2B1". (* [comment removed for export] *)
  Lemma sum_bcmpA_okQ (pat n : Z) (j : nat) (kq kb kbl knb : nat) (BUFg BLENg : Z) (bs : list byte) (ps : list byte) (CS : Z -> Prop) : ltac2:(CDefT.buildp (gd_tbl_LxA_sums ()) "P,(34.P,$4.Sp(35.$26.VR,VHIA,Vh,)O1.)P,(34.$4.(4:.VR,)+58704.)P,(34.$4.(36.$4.O8.VGS,=)O5.)P,(34.$4.(36.$4.O7.VGS,=)O4.)P,(34.$4.(36.$4.O6.VGS,=)(47.VR,))P,(34.$4.O4.(4;.(4<.(4=.&8.)O3.)))P,(34.P,P,(4=.&40.)(4>.(4=.&8.))Sp(36.P,P,(4=.&40.)(4>.(4=.&8.))SpO9.VOPS,L,P,(4=.&40.)(4>.(4=.&8.))$4?.)Lm,P,(4=.&40.)(4>.(4=.&8.))(50.$26.R1.O5.O3.))P,(34.P,(51.$4.)Sp(36.P,(51.$4.)SpO:.VPROPS,L,(51.$4.)$4?.)(52.O5.O3.O;.O2.))P,(34.$53.(54.$26.O<.O2.)$1.)P,(34.$4.(4;.(4<.(4=.&8.)O2.))O;.)P,(55.=O;.)P,(55.O;.(15.+2.+28.))P,(56.=O<.)P,(56.(57.(57.O<.O;.)+8.)(15.+2.+2?.))P,(56.(57.O<.O;.)(58.(38.VR,)))P,(56.(58.(38.VR,))(3<.VR,))P,(59.O1.)P,Ph',(5:.$26.VR,VHIA,)PLB',(51.$3:.)PLF',(51.$3:.)Pm',P,(4=.&40.)(4>.(4=.&8.))P,(5;.$26.VR,VHIA,R4.R3.R2.R1.)(5<.$26.(3?.VR,)R2.)P,(34.$53.(5=.O<.O;.)$1.)(5>.$26.(3?.VR,)VGS,VOPS,VLAWS,VPROPS,O1.(5?.O<.O;.O:.O9.O8.O7.O6.))")
(* [comment removed for export] *).
  Proof.
    intros ECS MCI GB GBL GNB HLEN OQK PJ RB PL NPOS N40 P0 P47 PLO ALO ICS ISH INZ. subst CS. apply apply_summary_soundP.
    unfold SUM_bcmpA, q. lx_sum_unfold.
    intros Q N BUF BLEN SPu LO HT NB SL A0 F fc m.
    intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
    intros [CSOK ALWF] _ MI GDb GDbl GDht GDnb GDsl R11 R12 R2 R10 ST OBUF.
    intros EA0 EN B1 B2 SLLO LONB CRS DS1 DS4 Q47 SPTOP SP0 SP1 OQ0 OQ1.
    change (BUF = nth kb GS 0) in GDb; change (BLEN = nth kbl GS 0) in GDbl; change (HT = nth 1 GS 0) in GDht;
    change (NB = nth knb GS 0) in GDnb; change (SL = nth 3 GS 0) in GDsl; change (nth 0 OPS (fun _ => True) m) in OQ0;
    change (nth kq OPS (fun _ => True) m) in OQ1.
    rewrite GB in GDb; rewrite GBL in GDbl; rewrite G1 in GDht; rewrite GNB in GDnb; rewrite G3 in GDsl; rewrite OQK in OQ1; rewrite O0 in OQ0.
    cbv beta in OQ0, OQ1.
    subst BUF BLEN HT NB SL. subst A0 N.
    destruct OQ0 as (hq & HHq & Ecs & Etop & Estk & Ehk & Efl & Evol & Efr).
    assert (U2 : bv_unsigned x2 = SPu) by (rewrite R2; apply uw64; assumption).
    pose proof (ro_image_bytes_at asegs m pat ps MI RB P0 ltac:(rewrite PL; lia)) as HPAT.
    pose proof (aobj_img asegs (arl_AL R) (hcs asegs R HIA h) m pat n ICS (ISH _ _ _ _ HHq) INZ) as OPAT.
    set (qs := firstn (Z.to_nat n) (skipn (Z.to_nat (Q - BUFg)) bs)).
    assert (HQS : bytes_at asegs m Q qs) by (eapply (bytes_at_sub asegs m BUFg bs Q n OQ1); lia).
    assert (LENQ : Z.of_nat (length qs) = n) by (subst qs; apply bytes_at_sub_length; lia).
    assert (OQS : aobj asegs (arl_AL R) (hcs asegs R HIA h) m Q n) by (eapply aobj_sub; [ exact OBUF | lia | lia ]).
    pose proof (artA_bcmp asegs R HIA) as SP. rewrite MCI in SP.
    rewrite <- Ecs in OPAT, OQS, CRS. rewrite <- Etop in SPTOP.
    eapply evtA_cut.
    { rewrite <- Ecs.
      eapply (SP x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m hq LB LF pat Q n LO ps qs);
        rewrite ?U2; first [ eassumption | exact HHq | lia ]. }
    clear SP. cbv beta. intros ms' POST. unfold call_postA in POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & HRES & ST' & HH').
    apply evtA_done. rewrite U2 in MU, ST'.
    pose proof (lx_urange a0') as Ra.
    assert (OPQ : nth j PROPS (fun _ => True) [bv_unsigned a0'; Q]).
    { rewrite PJ. unfold bcmp_prop. subst qs. split.
      - intros E. apply (proj1 HRES). rewrite <- (lx_w64u a0'), E. reflexivity.
      - intros E. apply (proj2 HRES) in E. rewrite E. reflexivity. }
    assert (OPB : nth kq OPS (fun _ => True) m').
    { rewrite OQK. cbv beta. eapply (bytes_at_transport asegs [(LO, SPu)] m m' BUFg bs OQ1 MU).
      cbn [disjoint_from]. rewrite <- HLEN. clear - DS4 B1 B2 NPOS HLEN. intuition lia. }
    assert (OPH : nth 0 OPS (fun _ => True) m').
    { rewrite O0. cbv beta. exists hq. split; [exact HH'|]. split; [exact Ecs|]. split; [exact Etop|]. split; [exact Estk|]. split; [exact Ehk|]. split; [exact Efl|]. split; [exact Evol|exact Efr]. }
    lx_sum_post.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End SBCMPQ.

(* [comment removed for export] *)
Definition SUM_bcmp0A (pat : Z) (n : Z) (kq kb kbl knb : nat) : summary := ltac2:(CDefT.buildp (gd_tbl_LxA_sums ()) "(2>.+58704.$1.#:.#?.#0.(2.(3.$4.$5.)(6.$4.$5.+;.^1.)(2.(3.$4.$5.)(6.$4.$5.+<.^2.)(2.(3.$4.$5.)(6.$4.$5.+2.^5.)(2.(3.$4.$5.)(6.$4.$5.+:.^:.)(7.(3.$4.$5.))))))(2.(3.$5.$22.)(6.$5.$22.^3.O3.)(2.(3.$5.$22.)(6.$5.$22.^4.O2.)(2.(3.$5.$22.)(6.$5.$22.^7.#1.)(2.(3.$5.$22.)(6.$5.$22.^8.O1.)(2.(3.$5.$22.)(6.$5.$22.^9.#3.)(7.(3.$5.$22.)))))))(2?.$5.)(7.$9.)(8.(3.$5.$5.)(6.$5.$5.^6.^5.))(7.(3.(3.$5.$5.)$5.))(2.$9.(>.(;.^3.)(;.^4.))(7.$9.))(2.$11.(31.(;.^:.)(?.O6.))(2.$11.(31.(;.^2.)(?.O5.))(2.$11.(12.(;.^3.)(;.^1.))(2.$11.(12.(13.(;.^1.)(;.^2.))(13.(;.^3.)(;.^4.)))(2.$11.(12.(;.^9.)(;.^6.))(2.$11.(12.(;.^6.)(13.(;.^5.)(1;.-1.(;.^8.))))(2.$11.(1:.(;.^6.)(13.(;.^5.)(1;.-1.(;.^6.))))(2.$11.(16.(;.^1.)(;.^2.)(;.^6.)(13.(;.^5.)(1;.-1.(;.^6.))))(2.$11.(17.(;.^4.)(;.^3.)(;.^4.)(;.^6.)(13.(;.^5.)(1;.-1.(;.^6.))))(2.$11.(33.(;.^2.)(13.(13.(;.^1.)(;.^2.))(?.+8.))(?.(15.+2.+2?.))(?.+1.)(?.=))(2.$11.(12.(;.^5.)(;.^7.))(2.$11.(12.(?.=)(;.^5.))(2.$11.(12.(;.^5.)(?.(1<.$1=.+1.)))(7.$11.))))))))))))))(2.(3.$1>.$1>.)(6.$1>.$1>.(;.^6.)(;.^5.))(7.(3.$1>.$1>.)))(2.(3.$4.$5.)(6.$4.$5.+:.^;.)(2.(3.$4.$5.)(6.$4.$5.+5.^<.)(2.(3.$4.$5.)(6.$4.$5.+6.^=.)(2.(3.$4.$5.)(6.$4.$5.+7.^>.)(2.(3.$4.$5.)(6.$4.$5.+;.^?.)(2.(3.$4.$5.)(6.$4.$5.+<.^10.)(2.(3.$4.$5.)(6.$4.$5.+=.^11.)(2.(3.$4.$5.)(6.$4.$5.+>.^12.)(2.(3.$4.$5.)(6.$4.$5.+?.^13.)(2.(3.$4.$5.)(6.$4.$5.+10.^14.)(2.(3.$4.$5.)(6.$4.$5.+11.^15.)(2.(3.$4.$5.)(6.$4.$5.+1<.^16.)(2.(3.$4.$5.)(6.$4.$5.+1=.^17.)(2.(3.$4.$5.)(6.$4.$5.+1>.^18.)(2.(3.$4.$5.)(6.$4.$5.+1?.^19.)(7.(3.$4.$5.)))))))))))))))))(2.$9.(1?.(;.^6.)(;.^5.))(7.$9.))(2.$11.(12.(?.=)(;.^;.))(2.$11.(12.(;.^;.)(?.(1<.$1=.+1.)))(7.$11.)))(2.$22.#0.(2.$22.O4.(7.$22.))))")
(* [comment removed for export] *).

Section SBCMP0.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Variables (GSX : list Z) (OPS : list (mem -> Prop)).
  Let GS : list Z := alloc_ceiling :: GSX.
  Hypothesis G1 : nth 1 GS 0 = htop asegs R HIA h.
  Hypothesis G3 : nth 3 GS 0 = arl_stklo R.
  Hypothesis O0 : nth 0 OPS (fun _ => True) = (fun m => HM asegs R HIA h LB LF m).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00A0@L12963415416.130L14721197074.106L2424813989.102 L2427054789.102 L26917761098.104L28960822020.12 L28962926396.12 L35341488937.102L35343958089.102L47756206852.99 L49279934426.106L5379818758.12  L55809163969.106L58243311233.130L7320571669.104 L7324848883.102 L7326794131.102 00000A00Z00h01601R02502602T03203C03i04<04[04l05@05Q05bS2bs2ps2qs3a0'2RaS1n2bs2ps1Q3SPu2LO3DS12qsS1n2bs2ps4NPOSS1n2bs2ps4NPOSS1n4BUFg5BLENg2bs2ps1Q2B22qsS1n4BUFg5BLENg2bs4NPOS1Q2LO2B22B11HFS1n4BUFg5BLENg2bs2ps4HLEN1Q2B2S1n4BUFg5BLENg2bs2ps4HLEN1Q2B2S3pat1n2bs2ps3P47S1R3pat1n2bs2ps3PLO3ALO3SPu2LO4SLLO2qsS4BUFg2bs3SPu2LO2H0S3pat1n2bs2ps4NPOS3P472qs1Q3Q47S2bs2ps2qs3a0'2RaS4BUFg2bs2ps1Q2B12qsS4BUFg2bs2ps1Q2B1S4BUFg2bs2ps1Q2B1". (* [comment removed for export] *)
  Lemma sum_bcmp0A_okO (pat n : Z) (kq kb kbl knb : nat) (BUFg BLENg : Z) (bs : list byte) (ps : list byte) (CS : Z -> Prop) : ltac2:(CDefT.buildp (gd_tbl_LxA_sums ()) "P,(34.P,$4.Sp(35.$26.VR,VHIA,Vh,)O1.)P,(34.$4.(4:.VR,)+58704.)P,(34.$4.(36.$4.O8.VGS,=)O5.)P,(34.$4.(36.$4.O7.VGS,=)O4.)P,(34.$4.(36.$4.O6.VGS,=)(47.VR,))P,(34.$4.O4.(4;.(4<.(4=.&8.)O3.)))P,(34.P,P,(4=.&40.)(4>.(4=.&8.))Sp(36.P,P,(4=.&40.)(4>.(4=.&8.))SpO9.VOPS,L,P,(4=.&40.)(4>.(4=.&8.))$4?.)Lm,P,(4=.&40.)(4>.(4=.&8.))(50.$26.R1.O5.O3.))P,(34.$53.(54.$26.O;.O2.)$1.)P,(34.$4.(4;.(4<.(4=.&8.)O2.))O:.)P,(55.=O:.)P,(55.O:.(15.+2.+28.))P,(56.=O;.)P,(56.(57.(57.O;.O:.)+8.)(15.+2.+2?.))P,(56.(57.O;.O:.)(58.(38.VR,)))P,(56.(58.(38.VR,))(3<.VR,))P,(59.O1.)P,(34.$53.(5=.O;.O:.)$1.)(3>.$26.(3?.VR,)VGS,VOPS,O1.(60.O;.O:.O9.O8.O7.O6.))")
(* [comment removed for export] *).
  Proof.
    intros ECS MCI GB GBL GNB HLEN OQK RB PL NPOS N40 P0 P47 PLO ALO ICS INZ. subst CS. apply apply_summary_soundO.
    unfold SUM_bcmp0A, q. lx_sum_unfold.
    intros Q N BUF BLEN SPu LO HT NB SL A0 F fc m.
    intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
    intros [CSOK ALWF] _ MI GDb GDbl GDht GDnb GDsl R11 R12 R2 R10 ST OBUF.
    intros EA0 EN B1 B2 SLLO LONB CRS DS1 DS4 Q47 SPTOP SP0 SP1 OQ0 OQ1.
    change (BUF = nth kb GS 0) in GDb; change (BLEN = nth kbl GS 0) in GDbl; change (HT = nth 1 GS 0) in GDht;
    change (NB = nth knb GS 0) in GDnb; change (SL = nth 3 GS 0) in GDsl; change (nth 0 OPS (fun _ => True) m) in OQ0;
    change (nth kq OPS (fun _ => True) m) in OQ1.
    rewrite GB in GDb; rewrite GBL in GDbl; rewrite G1 in GDht; rewrite GNB in GDnb; rewrite G3 in GDsl; rewrite OQK in OQ1; rewrite O0 in OQ0.
    cbv beta in OQ0, OQ1.
    subst BUF BLEN HT NB SL. subst A0 N.
    assert (U2 : bv_unsigned x2 = SPu) by (rewrite R2; apply uw64; assumption).
    pose proof (ro_image_bytes_at asegs m pat ps MI RB P0 ltac:(rewrite PL; lia)) as HPAT.
    pose proof (aobj_img asegs (arl_AL R) (hcs asegs R HIA h) m pat n ICS (hm_img_shadow _ _ _ _ _ _ _ OQ0) INZ) as OPAT.
    set (qs := firstn (Z.to_nat n) (skipn (Z.to_nat (Q - BUFg)) bs)).
    assert (HQS : bytes_at asegs m Q qs) by (eapply (bytes_at_sub asegs m BUFg bs Q n OQ1); lia).
    assert (LENQ : Z.of_nat (length qs) = n) by (subst qs; apply bytes_at_sub_length; lia).
    assert (OQS : aobj asegs (arl_AL R) (hcs asegs R HIA h) m Q n) by (eapply aobj_sub; [ exact OBUF | lia | lia ]).
    pose proof (artA_bcmp asegs R HIA) as SP. rewrite MCI in SP.
    eapply evtA_cut.
    { eapply (SP x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m h LB LF pat Q n LO ps qs);
        rewrite ?U2; first [ eassumption | exact OQ0 | lia ]. }
    clear SP. cbv beta. intros ms' POST. unfold call_postA in POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & HRES & ST' & HH').
    apply evtA_done. rewrite U2 in MU, ST'.
    pose proof (lx_urange a0') as Ra.
    assert (OPB : nth kq OPS (fun _ => True) m').
    { rewrite OQK. cbv beta. eapply (bytes_at_transport asegs [(LO, SPu)] m m' BUFg bs OQ1 MU).
      cbn [disjoint_from]. rewrite <- HLEN. clear - DS4 B1 B2 NPOS HLEN. intuition lia. }
    assert (OPH : nth 0 OPS (fun _ => True) m') by (rewrite O0; exact HH').
    lx_sum_post.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End SBCMP0.

(* [comment removed for export] *)
Ltac lxa_cw :=
  (* [comment removed for export] *)
  try (lazymatch goal with |- client_wrange ?L ?LBs ?lo ?top ?a ?n =>
         let a' := eval cbn [List.nth] in a in change (client_wrange L LBs lo top a' n) end);
  (* [comment removed for export] *)
  try match goal with E : htop _ _ _ _ = htop _ _ _ _ |- _ => rewrite E end;
  (* [comment removed for export] *)
  first [ assumption
        | solve_client_wrange
        | match goal with |- ?g => idtac "lxa_cw: cannot show" g; fail end ].
Ltac lxa_ecs := first [ reflexivity | assumption | symmetry; assumption ].
Ltac lxa_amemset_side := [> reflexivity | reflexivity | reflexivity | reflexivity | first [left; assumption | right; assumption] | lxa_ecs | reflexivity | lxa_cw ].
(* [comment removed for export] *)
Ltac lxa_sum1 :=
  lazymatch goal with
  | |- summary_okO _ _ _ _ _ SUM_getlenA => apply sum_getlenA_okOX; assumption
  | |- summary_okO _ _ _ _ _ SUM_gettagA => apply sum_gettagA_okOX; assumption
  | |- summary_okO _ _ _ _ _ SUM_getboolA => apply sum_getboolA_okOX; assumption
  | |- summary_okO _ _ _ _ _ SUM_getintA => apply sum_getintA_okOX; assumption
  | |- summary_okO _ _ _ _ _ SUM_bitstrnullA => apply sum_bitstrnullA_okOX; assumption
  | |- summary_okO _ _ _ _ _ SUM_bitstringA => apply sum_bitstringA_okOX; assumption
  | |- summary_okO _ _ _ _ _ SUM_bitstring0A => apply sum_bitstring0A_okOX; assumption
  | |- summary_okO _ _ _ _ _ (SUM_amemsetA 20 _) => eapply sum_amemsetA20_okO; lxa_amemset_side
  | |- summary_okO _ _ _ _ _ (SUM_amemsetA 24 _) => eapply sum_amemsetA24_okO; lxa_amemset_side
  | |- summary_okO _ _ _ _ _ (SUM_amemsetA 28 _) => eapply sum_amemsetA28_okO; lxa_amemset_side
  | |- summary_okO _ _ _ _ _ (SUM_amemsetA 32 _) => eapply sum_amemsetA32_okO; lxa_amemset_side
  | |- summary_okO _ _ _ _ _ (SUM_amemsetA 40 _) => eapply sum_amemsetA40_okO; lxa_amemset_side
  | |- summary_okO _ _ _ _ _ (SUM_amemsetA 48 _) => eapply sum_amemsetA48_okO; lxa_amemset_side
  | |- summary_okO _ _ _ _ _ (SUM_amemsetA 64 _) => eapply sum_amemsetA64_okO; lxa_amemset_side
  | |- summary_okO _ _ _ _ _ (SUM_amemsetA 80 _) => eapply sum_amemsetA80_okO; lxa_amemset_side
  | |- summary_okO _ _ _ _ _ (SUM_amemsetA 232 _) => eapply sum_amemsetA232_okO; lxa_amemset_side
  | |- summary_okO _ _ _ _ _ (SUM_amemsetA 744 _) => eapply sum_amemsetA744_okO; lxa_amemset_side
  | |- summary_okO _ _ _ _ _ (SUM_amemsetA 1440 _) => eapply sum_amemsetA1440_okO; lxa_amemset_side
  | |- summary_okO _ _ _ _ _ (SUM_amemset0A 24 [lxz4; lxz4; lxz8; lxz8] _) => eapply sum_amemset0A24s_okO; lxa_amemset_side
  | |- summary_okO _ _ _ _ _ (SUM_amemset0A 20 [lxz8; lxz8; lxz4] _) => eapply sum_amemset0A20p_okO; lxa_amemset_side
  | |- summary_okO _ _ _ _ _ (SUM_amemset0A 24 lxbs0 _) => eapply sum_amemset0A24b_okO; lxa_amemset_side
  | |- summary_okO _ _ _ _ _ (SUM_oidlook1A _ _ _ _ _) =>
      eapply sum_oidlook1A_okO; [> reflexivity | reflexivity | reflexivity | assumption | lxa_ecs | reflexivity | reflexivity | reflexivity | lxa_cw ]
  | |- summary_okO _ _ _ _ _ (SUM_getalgA _ _ _) =>
      eapply sum_getalgA_okO; [> reflexivity | reflexivity | reflexivity | reflexivity | assumption | lxa_ecs | reflexivity | reflexivity | reflexivity | lxa_cw | lxa_cw | lxa_cw ]
  | |- summary_okO ?sg _ _ _ _ (SUM_bcmp0A ?pat ?n _ _ _ _) =>
      (* [comment removed for export] *)
      let psl := eval vm_compute in (match image_bytes sg pat (Z.to_nat n) with Some b => b | None => @nil byte end) in
      eapply sum_bcmp0A_okO with (ps := psl);
      [> reflexivity | reflexivity | reflexivity                      (* [comment removed for export] *)
       | lxa_ecs
       | first [ assumption | match goal with M : arl_memcmp_i _ = ?v |- _ => rewrite M; reflexivity end ]   (* [comment removed for export] *)
       | reflexivity | reflexivity | reflexivity | reflexivity      (* [comment removed for export] *)
       | reflexivity                                                (* [comment removed for export] *)
       | vm_compute; reflexivity                                    (* [comment removed for export] *)
       | cbn; lia | lia | lia | lia | lia                           (* [comment removed for export] *)
       | pose proof (@alloc_ceiling_bounds _); lia                  (* [comment removed for export] *)
       | assumption                                                 (* [comment removed for export] *)
       | first [ assumption | eapply hcs_img_cs; [ assumption | assumption ] ]   (* [comment removed for export] *)
       | vm_compute; reflexivity ]                                  (* [comment removed for export] *)
  | |- ?g => idtac "lxa_sums: no ok-lemma for" g; fail
  end.
(* [comment removed for export] *)
Ltac lxa_sums L GS OPS :=
  lazymatch goal with |- evtA ?segs ?AL ?CS _ _ =>
    let H := fresh "LXSUMS" in
    assert (H : List.Forall (summary_okO segs AL GS OPS CS) L) by (repeat (apply List.Forall_cons; [ lxa_sum1 | ]); apply List.Forall_nil)
  end.

(* [comment removed for export] *)
Definition lxa_gmark (x : Z) : Prop := True.
Ltac lxa_atomize objs k :=
  lazymatch objs with
  | nil => k constr:(@nil Z)
  | cons ?o ?rest =>
      first [ is_var o; lxa_atomize rest ltac:(fun r => k constr:(@cons Z o r))
            | let g := fresh "lxg" in let E := fresh "LXG" in let M := fresh "LXGM" in
              remember o as g eqn:E in *;
              pose proof (I : lxa_gmark g) as M;
              lxa_atomize rest ltac:(fun r => k constr:(@cons Z g r)) ]
  end.
Ltac lxa_unglob :=
  repeat match goal with
  | M : lxa_gmark ?g, E : ?g' = _ |- _ => constr_eq g g'; clear M; subst g
  | M : lxa_gmark ?g |- _ => clear M
  end.
Ltac lxa_ops_rest mx hmP acc :=
  match goal with
  | H : lx_opq _ _ _ ?P _ _ mx |- _ =>
      lazymatch P with hmP => fail | _ => lazymatch acc with context [P] => fail | _ => lxa_ops_rest mx hmP constr:(@cons (mem -> Prop) P acc) end end
  | _ => acc
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lxa_stk_list mx acc :=
  match goal with
  | H : stk _ mx ?lo ?hi |- _ => lazymatch acc with context [(lo, hi)] => fail | _ => lxa_stk_list mx ((lo, hi) :: acc) end
  | _ => acc
  end.
Ltac lxa_rw_list mx acc :=
  match goal with
  | H : rw_cells _ mx ?a ?cs |- _ =>
      let n := eval cbv in (Z.of_nat (cells_size cs)) in
      lazymatch acc with context [(a, a + n)] => fail | _ => lxa_rw_list mx ((a, a + n) :: acc) end
  | _ => acc
  end.
Ltac lxa_has_bcmp SUMS := lazymatch SUMS with context [SUM_bcmp0A] => idtac | context [SUM_bcmpA] => idtac end.
Ltac lxa_pose_bytes mx :=
  lazymatch goal with
  | _ : lx_opq _ _ _ (fun m => bytes_at _ m _ _) _ _ mx |- _ => idtac
  | HB : bytes_at ?segs mx ?BUF ?bs |- evtA _ ?AL ?CS _ _ =>
      lazymatch goal with R : art_layout, HH : lx_opq _ _ _ (fun m => HM _ _ _ ?h _ _ m) _ _ mx |- _ =>
      let L := constr:(arl_L R) in
      let cands := lxr_cw_list L constr:([(arl_stklo R, htop segs R _ h)] : list ivl) in
      let cands := lxr_in_list cands in
      let cands := lxa_stk_list mx cands in
      let cands := lxa_rw_list mx cands in
      lxr_filter cands ltac:(fun lo hi => constr:(forall a, lo <= a < hi -> (a < BUF \/ BUF + Z.of_nat (length bs) <= a)))
        ltac:(let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; lxr_lia)
        ltac:(fun ok =>
          let H := fresh "OQB" in
          assert (H : lx_opq segs AL CS (fun m => bytes_at segs m BUF bs) ok [] mx)
            by (apply (lx_opq_bytes segs AL CS BUF bs ok mx HB); lxr_forall_okw));
      lxr_clear_okw
      end
  end.
Ltac lxa_ops_rest2 mx p1 p2 acc :=
  match goal with
  | H : lx_opq _ _ _ ?P _ _ mx |- _ =>
      lazymatch P with
      | p1 => fail | p2 => fail
      | _ => lazymatch acc with context [P] => fail | _ => lxa_ops_rest2 mx p1 p2 constr:(@cons (mem -> Prop) P acc) end end
  | _ => acc
  end.
Ltac lxa_auto SUMS OBJS :=
  lx_rw_merge;   (* [comment removed for export] *)
  let mx := lazymatch goal with |- context [MS _ _ _ _ _ ?mx (seg_rom _)] => mx end in
  try (lxa_has_bcmp SUMS; lxa_pose_bytes mx);
  lazymatch goal with
  | H : lx_opq _ _ _ (fun m => HM ?segs ?R ?HIA ?h ?LB ?LF m) _ _ mx |- _ =>
      let hmP := constr:(fun m => HM segs R HIA h LB LF m) in
      (* [comment removed for export] *)
      let rest := match goal with
                  | B : lx_opq _ _ _ (fun m => bytes_at ?sg m ?BUF ?bs) _ _ mx |- _ =>
                      let bP := constr:(fun m => bytes_at sg m BUF bs) in
                      let r2 := lxa_ops_rest2 mx hmP bP constr:(@nil (mem -> Prop)) in
                      constr:(@cons (mem -> Prop) bP r2)
                  | _ => lxa_ops_rest mx hmP constr:(@nil (mem -> Prop)) end in
      let OPS := constr:(@cons (mem -> Prop) hmP rest) in
      let GS := constr:(alloc_ceiling :: htop segs R HIA h :: arl_need_amem R :: arl_stklo R :: OBJS) in
      lxa_sums SUMS GS OPS
  | |- _ => fail "lxa_auto: no lx_opq HM fact at the goal memory (run lxr_pose first)"
  end.
