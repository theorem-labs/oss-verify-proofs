(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import PropExec AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.

Section Split.
Variables (SEGS : list Segment) (A : atable) (LIMIT : Z)
          (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (ISP : Z) (FS0 : Fs.Fs).

Lemma word_of_unsigned : forall (w : word) z, bv_unsigned w = z -> w = Z_to_bv 64 z.
Proof. intros w z H. rewrite <- H. symmetry. apply Z_to_bv_bv_unsigned. Qed.

(* [comment removed for export] *)
Theorem cs_ok_split2 : forall (ch : acs) (J : nat) (lo : Z),
  fact_ok (kn ch) (KRange (EVar J) lo (lo + 1)) = true -> s_log (a_ss ch) = [] ->
  forall E R FULL model, APS.cs_ok SEGS A LIMIT SINV argH ISP FS0 E ch R FULL model ->
    APS.cs_ok SEGS A LIMIT SINV argH ISP FS0 E (inst ch J (ELit lo)) R FULL model
    \/ APS.cs_ok SEGS A LIMIT SINV argH ISP FS0 E (inst ch J (ELit (lo + 1))) R FULL model.
Proof.
  intros ch J lo HF Hlog E R FULL model HC.
  pose proof (APS.fact_ok_sound SEGS E _ (kn ch) _ (APS.co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) HF) as K. cbn [kentry_ok edenot] in K.
  assert (C : bv_unsigned (ev E J) = lo \/ bv_unsigned (ev E J) = lo + 1) by lia.
  destruct C as [C|C]; [left | right];
    (apply (APS.cs_ok_inst_same SEGS A LIMIT SINV argH ISP FS0 E J _ ch R FULL model); [|exact Hlog | exact HC]);
    cbn [edenot]; symmetry; apply word_of_unsigned; exact C.
Qed.

End Split.
