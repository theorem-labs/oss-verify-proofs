(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.Common Require Import RunDraw.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U3B Require Import IfB_base IfB_wdefs IfB_wwrap IfB_top U2BIface_fit2_draft.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Theorem inflate_fast_proofB : inflate_fast_stmtA.
Proof.
  apply inflate_fast_proofA.
  intros RNG FR fc gp tp SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo rdL rdD fw payload m1 sd id ni ai no ao msg mode hw bw.
  unfold if_window_stmt.
  intros CX m fo x5 x6 x7 x10 x11 x24 x29 len dist op ci co hold bits INV0 WNZ LEN DIST EOP OP BCO CO258.
  eapply (if_window RNG FR fc gp tp SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo rdL rdD fw payload m1
                    sd id ni ai no ao msg mode hw bw CX WNZ); eassumption.
Qed.
End CANSEC1.
