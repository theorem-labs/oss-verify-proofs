(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBCheck0 HBCheck1 BS6EndB0 BC3 BC3B0Lit CxfL9 CxfFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition c3b0_IT : itab := APC.mk_itab_ranges HASEGS c3_ranges.
Lemma c3b0_IT_ok : itab_sound HASEGS c3b0_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition c3b0_shape_ (_ : unit) : shape := (SCase (EVar 1) 1 (SCase (EVar 3) 63 (SCase (EVar 3) 0 (SEmitP 2 [SPLit [117; 115; 97; 103; 101; 58; 32; 32; 73; 78; 80; 85; 84; 10]] (SHole 20)) (SEmitP 2 [SPLit [117; 115; 97; 103; 101; 58; 32]; SPBlob 1; SPLit [32; 73; 78; 80; 85; 84; 10]] (SHole 20))) (SCase (EVar 3) 64 (SEmitP 2 [SPLit [117; 115; 97; 103; 101; 58; 32]; SPBlob 1; SPLit [32; 73; 78; 80; 85; 84; 10]] (SHole 20)) (SCase (EVar 3) 73 (SCase (EVar 3) 66 (SEmitP 2 [SPLit [117; 115; 97; 103; 101; 58; 32]; SPBlob 1; SPLit [32; 73; 78; 80; 85; 84; 10]] (SHole 20)) (SEmitP 2 [SPLit [117; 115; 97; 103; 101; 58; 32]; SPBlob 1; SPLit [32; 73; 78; 80; 85; 84; 10]] (SEmitP 2 [] (SHole 20)))) (SEmitP 2 [SPLit [117; 115; 97; 103; 101; 58; 32]; SPBlob 1] (SEmitP 2 [SPLit [32; 73; 78; 80; 85; 84; 10]] (SHole 20)))))) (SCase (EVar 1) 2 (SHole 98) (SCase (EVar 3) 63 (SCase (EVar 3) 0 (SEmitP 2 [SPLit [117; 115; 97; 103; 101; 58; 32; 32; 73; 78; 80; 85; 84; 10]] (SHole 20)) (SEmitP 2 [SPLit [117; 115; 97; 103; 101; 58; 32]; SPBlob 1; SPLit [32; 73; 78; 80; 85; 84; 10]] (SHole 20))) (SCase (EVar 3) 64 (SEmitP 2 [SPLit [117; 115; 97; 103; 101; 58; 32]; SPBlob 1; SPLit [32; 73; 78; 80; 85; 84; 10]] (SHole 20)) (SCase (EVar 3) 73 (SCase (EVar 3) 66 (SEmitP 2 [SPLit [117; 115; 97; 103; 101; 58; 32]; SPBlob 1; SPLit [32; 73; 78; 80; 85; 84; 10]] (SHole 20)) (SEmitP 2 [SPLit [117; 115; 97; 103; 101; 58; 32]; SPBlob 1; SPLit [32; 73; 78; 80; 85; 84; 10]] (SEmitP 2 [] (SHole 20)))) (SEmitP 2 [SPLit [117; 115; 97; 103; 101; 58; 32]; SPBlob 1] (SEmitP 2 [SPLit [32; 73; 78; 80; 85; 84; 10]] (SHole 20)))))))).
Abbreviation c3b0_shape := (c3b0_shape_ tt).
Lemma c3b0_cert :
  CAP.check HASEGS c3b0_IT HAT NX0 AsanInit.LIMIT ha1_XN ha1_XE ha1_XB C3B0_HS 0 true false true 400000 3000 None s6endb0 c3_top = COk c3b0_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk c3b0_shape)). Time Qed.
