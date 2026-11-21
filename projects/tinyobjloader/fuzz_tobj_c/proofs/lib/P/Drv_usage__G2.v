(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the usage path's per-length checks per CONFIG_RSEQ, for both values of the flag). *)


Require Stdlib.ZArith.ZArith.
Require Stdlib.Lists.List.
Require Stdlib.Bool.Bool.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_usage__G1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Drv_usage_small_chk2.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_usage__G1.Drv_usage_small_states.

Lemma check_range_2 : forall r, check_range r 17 17 = true.
Proof. intros [|]; unfold check_range; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.fast_forallb. Qed.
End Drv_usage_small_chk2.

Module Drv_usage_small_chk4.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_usage__G1.Drv_usage_small_states.

Lemma check_range_4 : forall r, check_range r 51 16 = true.
Proof. intros [|]; unfold check_range; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.fast_forallb. Qed.
End Drv_usage_small_chk4.

Module Drv_usage_mid_chk.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_usage__G1.Drv_usage_mid_states.

Lemma check_range_mid : forall r, check_range_m r 67 7 = true.
Proof. intros [|]; unfold check_range_m; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.fast_forallb. Qed.
End Drv_usage_mid_chk.
