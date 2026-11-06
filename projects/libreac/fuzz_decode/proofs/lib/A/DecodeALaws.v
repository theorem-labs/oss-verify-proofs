(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantClose.v:120-121 (grant_ML)
   and lib/A/Prog/GrantLibX.v:173, :211-212 (GX_XL0, grant_need) of a working branch, in the form of
   proofs/libreac/fuzz_boxreg/lib/A/Prog/BoxClose.v (H_CORE_A's zero cost; H_RT_ALLOC_A's model_laws_ok) of
   a working branch 5093e48ebf1, for libreac/fuzz_decode's ASan image. *)
(* Three named hypotheses of lib/A/DecodeClose.v, each a Lemma of the same name whose statement is the hypothesis's
   type at the values the composition binds the Section variables to (rule 24: no function proved; these are generic
   law instances, no image numeral):
   - HB_UNIVERSE_OK (DecodeClose.v:344) and HB_MODEL_LAWS (:346) at B := GrantB (lib/A/AD2l.v:16, the core's record):
     the ts_universe field (lib/A/AF0m.v:420) of GrantB_syms (AD2l.v:72), and Reusable/YG05.v:140 model_laws_ok;
   - HB_COST (:370) at the meter MT := Reusable/YCbp.v ameter_triv and the bound XL := dec_XL0 = fun _ => 0, the pair
     DecodeClose.v:118-119 names (donor lib/A/AD1q.v:46, bound at lib/A/AD2o.v:45; lib/A/ACfi.v:56 XL0, :61-66 XL0_HXL):
     ameter_triv charges 0 for every malloc and free, so every term of PL.dec_llvmf_cost is 0. *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG01 YG0f YG0d YG05 YC5d.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YCbp.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import AF0m AD2l.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require LLVMFuzzerTestOneInput_cg.
Open Scope Z_scope.

Module PL := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.LLVMFuzzerTestOneInput_cg.

(* The bound of one call of the entry function under the meter that counts nothing (fuzz_grant's GX_XL0). *)
Definition dec_XL0 : Z -> Z := fun _ => 0.

(* DecodeClose.v:344, at B := GrantB. *)
Lemma HB_UNIVERSE_OK : universe_ok (as_universe GrantB).
Proof. exact (ts_universe GrantB GrantB_syms). Qed.

(* DecodeClose.v:346, at B := GrantB. *)
Lemma HB_MODEL_LAWS : model_laws (as_universe GrantB).
Proof. exact (model_laws_ok (as_universe GrantB) HB_UNIVERSE_OK). Qed.

(* DecodeClose.v:370, at MT := YCbp.ameter_triv and XL := dec_XL0. *)
Lemma HB_COST : forall n, 0 <= n -> @PL.dec_llvmf_cost YCbp.ameter_triv n <= dec_XL0 n.
Proof.
  intros n _. unfold PL.dec_llvmf_cost, PL.dec_crt_cost_max, dec_XL0, YCbp.ameter_triv. cbn. lia.
Qed.
