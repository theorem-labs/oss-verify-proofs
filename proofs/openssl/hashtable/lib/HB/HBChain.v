(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanInit.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound HBPlanImage HBAtable.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

Section Chain.
  Variable SV : env -> (word -> option byte) -> Prop.
  Variable argH : env -> word -> bool.
  Variable ISP : Z.
  Variable fs : Fs.Fs.
  #[local] Notation CSOK := (cs_ok HASEGS HAT AsanInit.LIMIT SV argH ISP fs).

  (* [comment removed for export] *)
  Definition fx_hole (START END : acs) : Prop :=
    forall E R FULL m (T : TSet), CSOK E START R FULL m ->
      (forall E1 R1 FULL1 m1, env_agree (nxt START) E E1 -> CSOK E1 END R1 FULL1 m1 -> m_fs m1 = m_fs m ->
                              crz HASEGS (cfg_of HASEGS R1 (pc END) FULL1 m1) T) ->
      crz HASEGS (cfg_of HASEGS R (pc START) FULL m) T.

  (* [comment removed for export] *)
  Definition piece (START : acs) (T : env -> Fs.Fs -> TSet) : Prop :=
    forall E R FULL m, CSOK E START R FULL m -> crz HASEGS (cfg_of HASEGS R (pc START) FULL m) (T E (m_fs m)).

  Definition t_agree (T : env -> Fs.Fs -> TSet) : Prop := forall E E' fs0, env_agree NX0 E E' -> T E fs0 = T E' fs0.

  Lemma hole_compose : forall START END T, (NX0 <= nxt START)%nat -> t_agree T -> fx_hole START END -> piece END T -> piece START T.
  Proof.
    intros START END T Hnx HT HF HP E R FULL m HC.
    apply (HF E R FULL m (T E (m_fs m)) HC). intros E1 R1 FULL1 m1 Hag HC1 Hfs.
    rewrite (HT E E1 (m_fs m) (CXS.env_agree_le NX0 (nxt START) E E1 Hag Hnx)). rewrite <- Hfs. exact (HP E1 R1 FULL1 m1 HC1).
  Qed.
End Chain.
