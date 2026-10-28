(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import PmLibDefs_u PmCurDefs_u.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PSCC.
Definition mem := (word -> option byte).
Section F.
Variable segs : list Segment.
Lemma ev_at_agV : forall V (M1 M2 : mem) e, L5C.agree_on M1 M2 (V + 8) 40 -> 0 <= V -> V + 48 <= 2 ^ 64 ->
  PMCUR.ev_at segs M1 V e -> PMCUR.ev_at segs M2 V e.
Proof.
  intros V M1 M2 e AG H0 H1 (D & H). split; [exact (L5C.defined_agree M1 M2 _ _ AG D)|].
  assert (U64 : forall o v, 8 <= o -> o + 8 <= 48 -> L5.u64_at segs M1 (V + o) v -> L5.u64_at segs M2 (V + o) v).
  { intros o v Ho1 Ho2 X. apply (L5C.u64_at_agree segs M1 M2); [intros q Hq; apply AG; lia | lia | lia | exact X]. }
  assert (U8 : forall o v, 8 <= o -> o + 1 <= 48 -> L5.u8_at segs M1 (V + o) v -> L5.u8_at segs M2 (V + o) v).
  { intros o v Ho1 Ho2 X. apply (L5C.u8_at_agree segs M1 M2); [intros q Hq; apply AG; lia | lia | lia | exact X]. }
  destruct e; cbn iota beta in H |- *; repeat match goal with X : _ /\ _ |- _ => destruct X end;
    repeat split; first [ apply (U64 8); [lia | lia | assumption] | apply (U64 32); [lia | lia | assumption] | apply (U64 40); [lia | lia | assumption]
                        | apply (U8 32); [lia | lia | assumption] ].
Qed.
Lemma evp_agV : forall V (M1 M2 : mem) lv w ps', L5C.agree_on M1 M2 (V + 8) 40 -> 0 <= V -> V + 48 <= 2 ^ 64 ->
  PMCUR.evp segs M1 V lv w ps' -> PMCUR.evp segs M2 V lv w ps'.
Proof. intros V M1 M2 lv w ps' AG H0 H1 (e & X & Y). exists e. split; [exact (ev_at_agV V M1 M2 e AG H0 H1 X) | exact Y]. Qed.
End F.

Lemma ev_rel_same : forall lv w ps1 ps2 e, PMCUR.ev_rel lv w ps1 e ->
  PML.ps_st ps2 = PML.ps_st ps1 -> PML.ps_level ps2 = PML.ps_level ps1 -> PML.ps_bptr ps2 = PML.ps_bptr ps1 -> length (PML.ps_buf ps2) = length (PML.ps_buf ps1) ->
  PMCUR.ev_rel lv w ps2 e.
Proof.
  intros lv w ps1 ps2 e H Hs Hl Hb Hn.
  assert (T : forall p n, PMCUR.txt_ok w ps1 p n -> PMCUR.txt_ok w ps2 p n).
  { intros p n [(X1 & X2)|X]; [left; rewrite Hb, Hn; split; assumption | right; exact X]. }
  destruct e; cbn [PMCUR.ev_rel] in *; unfold PMCUR.after_value_st in *; rewrite ?Hs, ?Hl;
    first [ exact H | destruct H as (H1 & H2 & H3); split; [exact H1|]; split; [exact H2 | exact (T _ _ H3)]
          | destruct H as (H1 & H2 & H3 & H4); split; [exact H1|]; split; [exact H2|]; split; [exact H3 | exact (T _ _ H4)] ].
Qed.
Lemma evp_same : forall segs (M : mem) V lv w ps1 ps2, PMCUR.evp segs M V lv w ps1 ->
  PML.ps_st ps2 = PML.ps_st ps1 -> PML.ps_level ps2 = PML.ps_level ps1 -> PML.ps_bptr ps2 = PML.ps_bptr ps1 -> length (PML.ps_buf ps2) = length (PML.ps_buf ps1) ->
  PMCUR.evp segs M V lv w ps2.
Proof. intros segs M V lv w ps1 ps2 (e & X & Y) Hs Hl Hb Hn. exists e. split; [exact X | exact (ev_rel_same lv w ps1 ps2 e Y Hs Hl Hb Hn)]. Qed.

Lemma wfc_sm_same : forall ps1 ps2, PMCUR.wf_c (PMCUR.ps_set_more ps1 true) ->
  PML.ps_st ps2 = PML.ps_st ps1 -> PML.ps_sst ps2 = PML.ps_sst ps1 -> PML.ps_nst ps2 = PML.ps_nst ps1 -> PML.ps_level ps2 = PML.ps_level ps1 ->
  PML.ps_stack ps2 = PML.ps_stack ps1 -> PML.ps_scap ps2 = PML.ps_scap ps1 -> PML.ps_buf ps2 = PML.ps_buf ps1 ->
  PMCUR.wf_c (PMCUR.ps_set_more ps2 true).
Proof.
  intros [st1 sst1 nst1 m1 d1 l1 stk1 sb1 sc1 bc1 bp1 buf1 w1] [st2 sst2 nst2 m2 d2 l2 stk2 sb2 sc2 bc2 bp2 buf2 w2] H; cbn; intros -> -> -> -> -> -> ->. exact H.
Qed.

Lemma wfc_sm_same_nn : forall ps1 ps2, PMCUR.wf_c (PMCUR.ps_set_more ps1 true) -> PML.ps_st ps1 <> PML.ST_NUMBER ->
  PML.ps_st ps2 = PML.ps_st ps1 -> PML.ps_sst ps2 = PML.ps_sst ps1 -> PML.ps_nst ps2 = PML.ps_nst ps1 -> PML.ps_level ps2 = PML.ps_level ps1 ->
  PML.ps_stack ps2 = PML.ps_stack ps1 -> PML.ps_scap ps2 = PML.ps_scap ps1 ->
  PMCUR.wf_c (PMCUR.ps_set_more ps2 true).
Proof.
  intros [st1 sst1 nst1 m1 d1 l1 stk1 sb1 sc1 bc1 bp1 buf1 w1] [st2 sst2 nst2 m2 d2 l2 stk2 sb2 sc2 bc2 bp2 buf2 w2] ((W1 & W2 & W3 & W4 & (C & T & W5 & W6 & W7)) & HL) Hn;
    cbn in *; intros -> -> -> -> -> ->.
  split; [|exact HL]. unfold PML.wf_ps. cbn. split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. split; [exact W4|]. exists C, T. split; [exact W5|]. split; [exact W6|].
  intros Hm. destruct (W7 Hm) as (X1 & X2 & X3 & X4 & X5 & X6). repeat (split; [assumption|]). intros X. exfalso. exact (Hn X).
Qed.

Lemma ev_rel_not_num : forall lv w ps e, PMCUR.ev_rel lv w ps e -> PML.ps_st ps <> PML.ST_NUMBER.
Proof.
  intros lv w ps e H. unfold PML.ST_NUMBER. destruct e; cbn [PMCUR.ev_rel] in H; unfold PMCUR.after_value_st in H;
    repeat match goal with X : _ /\ _ |- _ => destruct X as [X _] end; cbn [In] in *;
    unfold PML.ST_ACCEPT, PML.ST_EXPECT_COMMA_OR_END, PML.ST_EXPECT_COLON, PML.ST_EXPECT_MEMBER_NAME_OR_END, PML.ST_EXPECT_VALUE_OR_END in *; lia.
Qed.
Lemma evp_not_num : forall segs (M : mem) V lv w ps, PMCUR.evp segs M V lv w ps -> PML.ps_st ps <> PML.ST_NUMBER.
Proof. intros segs M V lv w ps (e & _ & H). exact (ev_rel_not_num lv w ps e H). Qed.

Lemma ws_ok_same : forall ps1 ps2, PML.ws_ok ps1 -> PML.ps_more ps2 = PML.ps_more ps1 -> PML.ps_st ps2 = PML.ps_st ps1 -> PML.ps_stack ps2 = PML.ps_stack ps1 ->
  PML.ps_level ps2 = PML.ps_level ps1 -> PML.ws_ok ps2.
Proof. intros ps1 ps2 H Hm Hs Hk Hl. unfold PML.ws_ok in *. rewrite Hm, Hs, Hk, Hl. exact H. Qed.
End PSCC.
