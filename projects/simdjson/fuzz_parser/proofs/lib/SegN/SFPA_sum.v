(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AxSymExec3.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegTmpl SegProg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require SFPA_defs SFPCA_defs PFFA_defs PFFCA_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Definition SFPAS : SP.summ :=
  SP.SUMY (SP.p_G SFPA_defs.SFPA) SFPA_defs.T0 (SP.p_ex SFPA_defs.SFPA) (SP.p_W SFPA_defs.SFPA) (SP.p_A SFPA_defs.SFPA)
    (SP.p_PS SFPA_defs.SFPA) false (SP.p_CR SFPA_defs.SFPA).
Definition SFPCAS : SP.summ :=
  SP.SUMY (SP.p_G SFPCA_defs.SFPCA) SFPCA_defs.T0 (SP.p_ex SFPCA_defs.SFPCA) (SP.p_W SFPCA_defs.SFPCA) (SP.p_A SFPCA_defs.SFPCA)
    (SP.p_PS SFPCA_defs.SFPCA) false (SP.p_CR SFPCA_defs.SFPCA).
Definition PFFAS : SP.summ :=
  SP.SUMY (SP.p_G PFFA_defs.PFFA) PFFA_defs.T0 (SP.p_ex PFFA_defs.PFFA) (SP.p_W PFFA_defs.PFFA) (SP.p_A PFFA_defs.PFFA)
    (SP.p_PS PFFA_defs.PFFA) false (SP.p_CR PFFA_defs.PFFA).
Definition PFFCAS : SP.summ :=
  SP.SUMY (SP.p_G PFFCA_defs.PFFCA) PFFCA_defs.T0 (SP.p_ex PFFCA_defs.PFFCA) (SP.p_W PFFCA_defs.PFFCA) (SP.p_A PFFCA_defs.PFFCA)
    (SP.p_PS PFFCA_defs.PFFCA) false (SP.p_CR PFFCA_defs.PFFCA).
