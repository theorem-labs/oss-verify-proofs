(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import HeapIface HeapIfaceA L5Defs L5Core PmLibDefs PmCurDefs PmLibDefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutL5A.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module CKA2.
Section Ev.
Variable segs : list Segment.
Lemma ev_at_ag : forall (M M' : PMCUR.mem) V e, 0 <= V -> V + 48 <= 2 ^ 64 ->
  (forall a, V + 8 <= a < V + 48 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> PMCUR.ev_at segs M V e -> PMCUR.ev_at segs M' V e.
Proof.
  intros M M' V e H0 H1 AG (HD & HE). split.
  - intros k Hk. rewrite (AG (V + 8 + k)) by lia. exact (HD k Hk).
  - assert (U64 : forall k v, 8 <= k -> k + 8 <= 48 -> L5.u64_at segs M (V + k) v -> L5.u64_at segs M' (V + k) v).
    { intros k v Hk1 Hk2 Hu. apply (CL5A.u64_same segs M M' (V + k)); [lia | lia | intros y Hy; apply AG; lia | exact Hu]. }
    destruct e; cbn [PMCUR.ev_at] in HE |- *;
      repeat match goal with
             | H : _ /\ _ |- _ => destruct H
             end;
      repeat split;
      first [ apply (U64 8); [lia | lia | assumption]
            | apply (U64 32); [lia | lia | assumption]
            | apply (U64 40); [lia | lia | assumption]
            | apply (CL5A.u8_same segs M M' (V + 32)); [lia | lia | apply AG; lia | assumption] ].
Qed.
Lemma evp_ag : forall (M M' : PMCUR.mem) V lv w ps', 0 <= V -> V + 48 <= 2 ^ 64 ->
  (forall a, V + 8 <= a < V + 48 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> PMCUR.evp segs M V lv w ps' -> PMCUR.evp segs M' V lv w ps'.
Proof. intros M M' V lv w ps' H0 H1 AG (e & HE & HR). exists e. split; [exact (ev_at_ag M M' V e H0 H1 AG HE) | exact HR]. Qed.
Lemma cur_post_ag : forall ps ps' code (M M' : PMCUR.mem) V, 0 <= V -> V + 48 <= 2 ^ 64 ->
  (forall a, V + 8 <= a < V + 48 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> PMCUR.cur_post segs ps ps' code M V -> PMCUR.cur_post segs ps ps' code M' V.
Proof.
  intros ps ps' code M M' V H0 H1 AG (C1 & C2). split; [exact C1|]. intros Hc Hm. destruct (C2 Hc Hm) as [D|(W & EV)]; [left; exact D | right; split; [exact W | exact (evp_ag M M' V _ _ _ H0 H1 AG EV)]].
Qed.

Lemma ev_rel_set_win : forall lv w ps' win e, PMCUR.ev_rel lv w (PML.ps_set_win ps' win) e <-> PMCUR.ev_rel lv w ps' e.
Proof. intros lv w ps' win e. destruct ps', e; cbn [PMCUR.ev_rel PML.ps_set_win PMCUR.txt_ok PMCUR.after_value_st PML.ps_st PML.ps_level PML.ps_bptr PML.ps_buf]; tauto. Qed.
Lemma evp_set_win : forall (M : PMCUR.mem) V lv w ps' win, PMCUR.evp segs M V lv w ps' -> PMCUR.evp segs M V lv w (PML.ps_set_win ps' win).
Proof. intros M V lv w ps' win (e & HE & HR). exists e. split; [exact HE | exact (proj2 (ev_rel_set_win lv w ps' win e) HR)]. Qed.
Lemma wf_c_set_win : forall ps' win, PMCUR.wf_c ps' -> PMCUR.wf_c (PML.ps_set_win ps' win).
Proof. intros [] win H. exact H. Qed.
Lemma set_more_set_win : forall ps' m win, PMCUR.ps_set_more (PML.ps_set_win ps' win) m = PML.ps_set_win (PMCUR.ps_set_more ps' m) win.
Proof. intros [] m win. reflexivity. Qed.
End Ev.
End CKA2.
