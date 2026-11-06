(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)


Require Stdlib.ZArith.ZArith.
Require Stdlib.Lists.List.
Require Stdlib.Bool.Bool.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_usage__G1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Drv_usage_small_chk2.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_usage__G1.Drv_usage_small_states.

Lemma check_range_2 : check_range 17 17 = true.
Proof. unfold check_range. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.fast_forallb. Qed.
End Drv_usage_small_chk2.

Module Drv_usage_small_chk4.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_usage__G1.Drv_usage_small_states.

Lemma check_range_4 : check_range 51 16 = true.
Proof. unfold check_range. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.fast_forallb. Qed.
End Drv_usage_small_chk4.

Module Drv_usage_mid_chk.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_usage__G1.Drv_usage_mid_states.

Lemma check_range_mid : check_range_m 67 7 = true.
Proof. unfold check_range_m. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.fast_forallb. Qed.
End Drv_usage_mid_chk.
