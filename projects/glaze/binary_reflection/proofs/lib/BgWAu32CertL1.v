(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC OSSVerify.Proofs.glaze.binary_reflection.lib.BgU32. Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgU32.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import BgWA.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS. Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgWAi8CertS.BgWAX.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import BgWAu32.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
#[local] Notation CHKX c k := (check BSEGS (BgWA.IT cfg) ABOTH BgWA.NXF LIMIT ISP0 XN XE0 BgWA.XB (HScut c (XCUTS cfg INVm JS1m elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg JS0m) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg INVm JS1m elem) = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma cert_L1X : CHKX (BgWA.ceL1 cfg) 0 (BgWA.tin cfg ML) (XPLAN_L1 cfg JS0m) = COk (SHole 1).
Proof. rewrite IT_eq. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (BgWA.ceL1 cfg) 1 (XTL INVm) (XLOOPC cfg INVm JS1m elem) = COk (SHole 1).
Proof. rewrite IT_eq. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
(* [comment removed for export] *)
