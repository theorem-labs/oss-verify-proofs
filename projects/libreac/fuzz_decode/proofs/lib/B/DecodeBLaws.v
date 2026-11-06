(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantClose.v:120-121 (grant_ML)
   and lib/A/Prog/GrantLibX.v:173, :211-212 (GX_XL0, grant_need) of a working branch, in the form of
   proofs/libreac/fuzz_boxreg/lib/A/Prog/BoxClose.v (H_CORE_A's zero cost; H_RT_ALLOC_A's model_laws_ok) of
   a working branch 5093e48ebf1, for libreac/fuzz_decode's ASan+UBSan image; the twin of
   lib/A/DecodeALaws.v. *)
(* Three named hypotheses of lib/B/DecodeBClose.v, each a Lemma of the same name whose statement is the hypothesis's
   type at the values the composition binds the Section variables to (rule 24: no function proved; these are generic
   law instances, no image numeral):
   - HB_UNIVERSE_OK (DecodeBClose.v:338) and HB_MODEL_LAWS (:340) at B := TfibB (lib/B/YD2l.v:12, the image-B core's
     record, a working branch): the ts_universe field (lib/B/YF0m.v TfibSyms) of TfibB_syms (YD2l.v:68),
     and Reusable/YG05.v:140 model_laws_ok;
   - HB_COST (:364) at the meter MT := Reusable/YCbp.v ameter_triv and the bound XL := dec_XL0 = fun _ => 0, the pair
     DecodeBClose.v:118-119 names (donor lib/YD1q.v:46, bound at lib/YD2o.v:45; lib/YCfi.v:56 XL0, :61-66 XL0_HXL).
     DecodeBClose.v's MT is a Reusable/YC5d.v ameter_ops, so the meter is the Reusable one: the image-B core's
     lib/B/YCbp.v ameter_triv is a lib/B/YC5d.v ameter_ops, a different record type. ameter_triv charges 0 for every
     malloc and free, so every term of PL.dec_llvmf_cost is 0. *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG01 YG0f YG0d YG05 YC5d.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YCbp.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import YF0m YD2l.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require LLVMFuzzerTestOneInput_cg.
Open Scope Z_scope.

Module PL := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.LLVMFuzzerTestOneInput_cg.

(* The bound of one call of the entry function under the meter that counts nothing (fuzz_grant's GX_XL0). *)
Definition dec_XL0 : Z -> Z := fun _ => 0.

(* DecodeBClose.v:338, at B := TfibB. *)
Lemma HB_UNIVERSE_OK : universe_ok (as_universe TfibB).
Proof. exact (ts_universe TfibB TfibB_syms). Qed.

(* DecodeBClose.v:340, at B := TfibB. *)
Lemma HB_MODEL_LAWS : model_laws (as_universe TfibB).
Proof. exact (model_laws_ok (as_universe TfibB) HB_UNIVERSE_OK). Qed.

(* DecodeBClose.v:364, at MT := YCbp.ameter_triv and XL := dec_XL0. *)
Lemma HB_COST : forall n, 0 <= n -> @PL.dec_llvmf_cost YCbp.ameter_triv n <= dec_XL0 n.
Proof.
  intros n _. unfold PL.dec_llvmf_cost, PL.dec_crt_cost_max, dec_XL0, YCbp.ameter_triv. cbn. lia.
Qed.
