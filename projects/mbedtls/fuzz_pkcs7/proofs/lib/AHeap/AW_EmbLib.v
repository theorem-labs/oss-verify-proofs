(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX SysStep ITree Nodes Frame.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtS AEvtA.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AModel AModelX.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys ASysS AKinv AKinvS AW_Unwind AW_Unwind2 AW_MmapFixed AW_Poison.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AW_CfgS AW_Populate AW_EmbCfg.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ATac.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.

From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_AW_EmbLib () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.option"; "OSSVerify.KrLib.AHeap.AW_EmbCfg.emb_step"; "OSSVerify.KrLib.AHeap.AW_EmbCfg.emb_fresh"; "OSSVerify.KrLib.AHeap.AW_EmbCfg.emb_geo"; "OSSVerify.KrLib.LibA.ALazy.crange"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.KrLib.AHeap.ACeil.ACEIL"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.Frame.ivl"; "stdpp.bitvector.definitions.bv"; "OSSVerify.KrLib.AHeap.AW_Populate.emb_cells"; "OSSVerify.KrLib.Lib.Frame.munch"; "OSSVerify.KrLib.Lib.Frame.wmono"; "OSSVerify.KrLib.A.AImg.asegs"; "OSSVerify.KrLib.Lib.Frame.disjoint_from"; "OSSVerify.KrLib.AHeap.AW_Populate.A_EMB"].
   (* [comment removed for export] *)
Section ARUN_1. Context {hAR : arun}.

(* [comment removed for export] *)
#[using="Type"] Lemma emb_buf_apart : ltac2:(CDefT.buildp (gd_tbl_AW_EmbLib ()) "PCS,P,$0.SpPEP,$0.PEB,$0.PECAP,$0.PESZ,$0.PP',$0.Pd',$0.Pcap',$0.Psz',$0.Pxa,(1.$0.)PT,$0.PCTX,$0.PSB,$0.PA,$0.Pn,$0.P,(2.R>.R=.R<.R;.R:.R9.R8.R7.R6.)P,(3.VhAR,R10.R7.)P,(4.VhAR,R?.R7.R6.R5.)P,(5.R12.R5.R4.)P,(6.=R5.)P,(7.(8.(9.R8.R7.)(9.(:.R7.R6.)(:.(:.R8.(;.+2.+25.))+1000.)))(7.(8.(9.R:.R7.)(9.(:.R7.R6.)(:.R:.+1000.)))(8.(9.R9.R7.)(9.(:.R7.R6.)(:.R9.+10000.)))))(8.(9.(:.R?.+10000.)(<.VhAR,))(7.(9.(:.R?.+10000.)R8.)(9.(:.R8.R7.)R?.)))")
(* [comment removed for export] *).
Proof.
  intros CS EP EB ECAP ESZ P' d' cap' sz' xa T CTX SB A n STEP FRESH GEO CR N0 IN.
  ddestruct STEP as (_ & _ & _ & [(E0 & a & -> & -> & ANZ) | (ENZ & -> & ->)]).
  - ddestruct (FRESH a eq_refl) as (F1 & F2 & F3 & F4 & F5). unfold kEmbBytes in *. split; [exact F2|].
    destruct (Z_le_gt_dec (a + 65536) A) as [|G1]; [left; assumption|]. destruct (Z_le_gt_dec (A + n) a) as [|G2]; [right; assumption|]. exfalso.
    apply (F5 (Z.max a A)); [apply CR; lia| lia].
  - ddestruct (GEO ENZ) as (G1 & G2 & G3 & G4 & G5 & G6). unfold kEmbBytes in *. split; [exact G2|]. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma djf_sub : forall W A n A' n', disjoint_from W A n -> A <= A' -> A' + n' <= A + n -> disjoint_from W A' n'.
Proof.
  induction W as [|[lo hi] W IH]; intros A n A' n' H H1 H2; cbn in *; [exact I|].
  destruct H as [H HW]. split; [clear - H H1 H2; lia| eapply IH; eauto].
Qed.
#[using="Type"] Lemma emb_cells_transport_w : ltac2:(CDefT.buildp (gd_tbl_AW_EmbLib ()) "PW,(=.$>.)Pm,P,(?.&40.)(1.(?.&8.))Pm',P,(?.&40.)(1.(?.&8.))PP,$0.Pd,$0.Pcap,$0.Psz,$0.P,(10.R4.R3.R2.R1.R6.)P,(11.R8.R7.R6.)P,(12.$13.R8.R7.)P,(14.R:.$15.+38.)(10.R8.R7.R6.R5.R9.)")
(* [comment removed for export] *).
Proof.
  (intros W m m' P d cap sz dd_H; ddestruct dd_H as (E1 & E2 & E3 & E4); intros MU WM DJ). unfold emb_cells.
  split; [eapply rw_cells_transport; [exact E1| exact MU| exact WM| eapply djf_sub; [exact DJ| |]; cbn; lia]|].
  split; [eapply rw_cells_transport; [exact E2| exact MU| exact WM| eapply djf_sub; [exact DJ| |]; cbn; lia]|].
  split; [eapply rw_cells_transport; [exact E3| exact MU| exact WM| eapply djf_sub; [exact DJ| |]; cbn; lia]|].
  intros D0. eapply wr_at_transport; [exact (E4 D0)| exact WM].
Qed.

End ARUN_1.
