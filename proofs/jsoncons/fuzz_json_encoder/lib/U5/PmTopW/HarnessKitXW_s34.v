(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Plain.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec HeapIface LibIface L5Defs L5Core PmLibDefs PmLibSpecs PmEncSpecs PmLibSpecsX PmLibSpecsW PmRef PmTopSpecsXW.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module HKXW16.

Lemma g0_es : PMES.g_es PMES.g0 = []. Proof. reflexivity. Qed.
Lemma g0_len : PMES.g_len PMES.g0 = 0. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma sink_len_bound : forall (M : word -> option byte) S2 rep (bound : Z),
  PMES.sink_at M S2 rep -> (forall b, In b (PML.srep_blocks rep) -> snd b <= bound) -> 23 <= bound ->
  PMES.len (PML.srep_chars rep) < bound.
Proof.
  intros M S2 rep bound (SA & _ & _) HB Hb. unfold PMES.len. destruct rep as [s | cap p s]; cbn [PML.srep_chars PML.str_at PML.srep_blocks] in *.
  - destruct SA as (L22 & _). lia.
  - destruct SA as (_ & _ & Lc). specialize (HB (p, cap) (or_introl eq_refl)). cbn [snd] in HB. lia.
Qed.

Section S.
Variable HI : heap_iface.
(* [comment removed for export] *)
Hypothesis HFIT : forall LB cr M VM A n, hi_heap HI LB cr M VM -> In (A, n) LB -> n <= 2 ^ 27 \/ n <= 2 ^ 34.

Theorem phi_of_read : forall (M : word -> option byte) V S2 (eg' : PMES.eghost) (LB : list (Z * Z)) cr VM (payload : list byte) (pay : Z),
  PMES.enc_inv M V S2 eg' ->
  hi_heap HI LB cr M VM -> (forall b, In b (PMES.g_lbv eg') -> In b LB) ->
  0 <= pay ->
  PMES.g_len eg' = PMES.g_len PMES.g0 + PMW.ind_run (PMES.g_es PMES.g0) (fst (fst (PMR.READ (PMXW.zs_of_bytes payload)))) + pay ->
  PMXW.phi_lim (2 ^ 34) payload.
Proof.
  intros M V S2 eg' LB cr VM payload pay (_ & _ & SINK & LEN & _) HH HIN Hpay HL.
  rewrite g0_es, g0_len in HL.
  assert (CAP : PMES.len (PML.srep_chars (PMES.g_rep eg')) < 2 ^ 34).
  { apply (sink_len_bound M S2 _ _ SINK); [|lia]. intros [p cap] Hb. cbn [snd].
    assert (Hin : In (p, cap) LB) by (apply HIN; unfold PMES.g_lbv; apply in_or_app; left; exact Hb).
    destruct (HFIT LB cr M VM p cap HH Hin); lia. }
  rewrite LEN in CAP.
  apply (PMXW.phi_lim_of_len (2 ^ 34) payload [] 0 pay (PMES.g_len eg') (2 ^ 34)); [reflexivity | reflexivity | reflexivity | exact Hpay | exact HL | exact CAP | lia].
Qed.
End S.
End HKXW16.
