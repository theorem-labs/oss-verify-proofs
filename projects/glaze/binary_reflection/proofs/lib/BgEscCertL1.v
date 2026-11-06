(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC OSSVerify.Proofs.glaze.binary_reflection.lib.BgEsc. Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeT OSSVerify.Proofs.glaze.binary_reflection.lib.BgStrResizeC.BgStrResizeA OSSVerify.Proofs.glaze.binary_reflection.lib.BgEsc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP. Import GPS.
Open Scope Z_scope.
#[local] Notation CHK m := (check BSEGS BgEsc.IT ABOTH BgEsc.NXF LIMIT ISP0 BgEsc.XN XE0 BgEsc.XB (HSce (BgEsc.ce m)) 0%nat BFUEL BgEsc.FUEL None).
#[local] Notation CHK1 := (check BSEGS BgEsc.IT ABOTH BgEsc.NXF LIMIT ISP0 BgEsc.XN XE0 BgEsc.XB (HSce BgEsc.ceL1) 0%nat BFUEL BgEsc.FUEL None).
#[local] Notation CHKc c k := (check BSEGS BgEsc.IT ABOTH BgEsc.NXF LIMIT ISP0 BgEsc.XN XE0 BgEsc.XB (HScut c BgEsc.CUTS_E k) 0%nat BFUEL BgEsc.FUEL None).
(* [comment removed for export] *)
Lemma esc_cert_L1 : CHKc BgEsc.ceL1 0 (BgEsc.tin ML) (BgEsc.planX ML) = COk (SHole 2).   (* [comment removed for export] *)
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 2))). Qed.
Lemma esc_cut_L : CHKc BgEsc.ceL1 1 (BgEsc.JSA ML ML) (BgEsc.CUTE (BgEsc.JSA ML ML) (BgEsc.afterA ML ML)) = COk (SHole 0).   (* [comment removed for export] *)
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
(* [comment removed for export] *)
