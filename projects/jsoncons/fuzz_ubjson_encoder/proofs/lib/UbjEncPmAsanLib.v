(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec StoreOk AsanAcct HeapIface HeapIfaceA HeapIfaceAEx HeapIfaceAEr IcptIfaceA LibIface LibIfaceAB LibIfaceAE
     L5Defs L5Core L5DefsA PmLayout PmLayoutA PeSpecsAa PeSpecsAmc PeCSinkA PeCSpecsA PeCSpecsAa PeCTopA PeCTopAsmA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_UbjEncPmAsanLib () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:PeCSpecsAa5PECSA6pay_inC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:PeCSpecsAa5PECSA7pay_outC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:PeCTopAsmA7PECASMA6fam_okC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:PeCTopAsmA7PECASMA4LayAC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:LibIfaceAB5lla_LC13~~~I47Corelib4Init5Logic2eq00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs4SCFGC13~~~K47Corelib4Init9Datatypes4list01C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<HeapIfaceAEx3HAJ9strict_ofC13~~~I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:LibIfaceAE?lib_iface_okA_x00C13~~~K47Corelib4Init5Logic2eq01C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:PeCTopAsmA7PECASMA=top_iface_asmC13~~~K47Corelib4Init5Logic3and01c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?UbjEncPmAsanLib=lib_ok_stmtFXC13~~~K47Corelib7Numbers7BinNums8positive03I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA8asan_run00C13~~~I47Corelib7Numbers7BinNums1Z00I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA:asan_iface00C13~~~I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA;asan_layout00C13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:PeCTopAsmA7PECASMA6TopLSAC13~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section SCFG_1.
Context {SCFG_P : ScfgP}.

(* [comment removed for export] *)
Definition lib_ok_stmtFX (FAMP : asan_run -> (list (list Z) -> asan_iface) -> Prop) (L : asan_layout) (Lay : lib_layoutA) (LSt : lib_statics)
           (PayOk PayExport : list byte -> Prop) : Prop :=
  forall (ar : asan_run) (HIk : list (list Z) -> asan_iface), FAMP ar HIk ->
    lla_L Lay = L /\ lib_iface_okA_x Lay ar SCFG (HAJ.strict_of (HIk [])) LSt PayOk PayExport.

Section A.
Variables (L : asan_layout) (C : asan_statics_cells) (IL : icpt_layout) (LR : HAR.layoutR) (P : PESKA.sink_policyA).
Hypothesis LY : PMA.layout L C.
Hypothesis ILY : as0_icpt_layout IL.
Hypothesis MCC : PMAMC.mcmp_cells C.
Hypothesis PO : PESKA.sink_policyA_ok L P.
Hypothesis PMODE : PESKA.spa_mode P.
Hypothesis NMAXOK : PESKA.spa_nmax P <= HAR.NREQ.
(* [comment removed for export] *)
Hypothesis ROWS : forall ar HIk, PECASMA.fam_ok L C IL LR ar HIk -> PECASMA.rows_open L ar HIk P.
Theorem lib_okFX_A (PayOk PayExport : list byte -> Prop) :
  PECSA.pay_in P PayOk -> PECSA.pay_out P PayExport ->
  lib_ok_stmtFX (PECASMA.fam_ok L C IL LR) L (PECASMA.LayA L P) PECASMA.TopLSA PayOk PayExport.
Proof.
ltac2:(KReplay.run1 (kr_t_UbjEncPmAsanLib ()) ["SCFG_1"; "A"] "h09PayExporth15PayOkh23FAMh33HIkh43PINh54POUTh62arp;1p;2p;7p;3p;Dp;4p;5p;6g0000j11Tg000Uj1BTg0013j13Tg001Vj10Tg0026j2ATg003Hj2:Tg004[j77j5=Tg005oj24Tg007Aj15Tg008Lj36Tg008fj12Tg009lj18Tg00:Lj19Tg00;aj7@Tg00=8j2?Tg00=RlD;Tg00>mj4<Tg00?Hj6>Tg00@`#1#1#1#B#3#0p-0[R0p,1PR1f1R2'A1:12g00AEg00BU#0R3#0g00C3[p,6SCFG_PR4p,1LR5p,1CR6p,2ILR7p,2LRR8P2f0R9F7g00DER:1451R;#5;65P;f2R<%24P2%83O1#9g00EXR3f6R=f5R>F@1?:5P4P5P6P7P8P<P2P1p,2LYp,3ILYp,3MCCp,2POp,5PMODEp,6NMAXOKP9p,4ROWSP<P2P9O3P=P>f4f3R>MD;C<W2W3W6P4P5P6P7P8D=P5P;P3P>P<E>eW5W4X00X10P2P9O2X00W1o"). Qed.
End A.

(* [comment removed for export] *)
End SCFG_1.
