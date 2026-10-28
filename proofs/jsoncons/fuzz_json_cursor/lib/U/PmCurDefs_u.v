(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import PmLibDefs_u.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMCUR.
Definition mem := (word -> option byte).

Definition ICS : list Z := [PML.ST_EXPECT_COMMA_OR_END; PML.ST_EXPECT_MEMBER_NAME_OR_END; PML.ST_EXPECT_MEMBER_NAME; PML.ST_EXPECT_COLON;
                            PML.ST_EXPECT_VALUE_OR_END; PML.ST_EXPECT_VALUE; PML.ST_MEMBER_NAME].

Definition lvl_ok (ps : PML.pstate) : Prop :=
  PML.ps_more ps = true -> (In (PML.ps_st ps) ICS \/ exists x, In x (PML.ps_stack ps) /\ In x ICS) -> 1 <= PML.ps_level ps.
Definition wf_c (ps : PML.pstate) : Prop := PML.wf_ps ps /\ lvl_ok ps.
Definition wf_c_stale (ps : PML.pstate) : Prop := PML.wf_ps_stale ps /\ lvl_ok ps.
Definition ps_set_more (ps : PML.pstate) (m : bool) : PML.pstate :=
  PML.PS (PML.ps_st ps) (PML.ps_sst ps) (PML.ps_nst ps) m (PML.ps_done ps) (PML.ps_level ps) (PML.ps_stack ps) (PML.ps_sb ps) (PML.ps_scap ps)
         (PML.ps_bcap ps) (PML.ps_bptr ps) (PML.ps_buf ps) (PML.ps_win ps).

Inductive sevent : Type :=
  | EvNull | EvBool (b : bool) | EvI64 (v : Z) | EvU64 (v : Z) | EvDbl (bits : Z)
  | EvStr (p n : Z) | EvKey (p n : Z) | EvBeginObj | EvEndObj | EvBeginArr | EvEndArr.

Definition txt_ok (w0 : option (Z * Z)) (ps' : PML.pstate) (p n : Z) : Prop :=
  (p = PML.ps_bptr ps' /\ n = Z.of_nat (length (PML.ps_buf ps'))) \/
  (exists p0 e0, w0 = Some (p0, e0) /\ p0 <= p /\ 0 <= n /\ p + n <= e0).
Definition after_value_st (ps' : PML.pstate) : Prop := In (PML.ps_st ps') [PML.ST_ACCEPT; PML.ST_EXPECT_COMMA_OR_END].

Definition ev_rel (lv0 : Z) (w0 : option (Z * Z)) (ps' : PML.pstate) (e : sevent) : Prop :=
  match e with
  | EvNull | EvBool _ | EvI64 _ | EvU64 _ | EvDbl _ => after_value_st ps' /\ PML.ps_level ps' = lv0
  | EvStr p n => after_value_st ps' /\ PML.ps_level ps' = lv0 /\ txt_ok w0 ps' p n
  | EvKey p n => PML.ps_st ps' = PML.ST_EXPECT_COLON /\ PML.ps_level ps' = lv0 /\ 1 <= lv0 /\ txt_ok w0 ps' p n
  | EvBeginObj => PML.ps_st ps' = PML.ST_EXPECT_MEMBER_NAME_OR_END /\ PML.ps_level ps' = lv0 + 1
  | EvBeginArr => PML.ps_st ps' = PML.ST_EXPECT_VALUE_OR_END /\ PML.ps_level ps' = lv0 + 1
  | EvEndObj | EvEndArr => after_value_st ps' /\ PML.ps_level ps' = lv0 - 1 /\ 1 <= lv0
  end.

Definition win_le (w0 w : option (Z * Z)) : Prop :=
  match w0, w with Some (p0, e0), Some (p, e) => p0 <= p /\ e = e0 | None, None => True | _, _ => False end.
Lemma txt_ok_mono : forall w0 w ps' p n, win_le w0 w -> txt_ok w ps' p n -> txt_ok w0 ps' p n.
Proof.
  intros w0 w ps' p n HW [H|(p1 & e1 & Hw & H1 & H2 & H3)]; [left; exact H|]. right. subst w.
  destruct w0 as [[p0 e0]|]; [|destruct HW]. destruct HW as (Hp & HE). subst e1. exists p0, e0. split; [reflexivity|]. split; [lia|]. split; lia.
Qed.
Lemma ev_rel_mono : forall lv w0 w ps' e, win_le w0 w -> ev_rel lv w ps' e -> ev_rel lv w0 ps' e.
Proof.
  intros lv w0 w ps' e HW H. destruct e; cbn [ev_rel] in *; try exact H.
  - destruct H as (H1 & H2 & H3). split; [exact H1|]. split; [exact H2 | exact (txt_ok_mono _ _ _ _ _ HW H3)].
  - destruct H as (H1 & H2 & H3 & H4). split; [exact H1|]. split; [exact H2|]. split; [exact H3 | exact (txt_ok_mono _ _ _ _ _ HW H4)].
Qed.

Definition scalar_ev (e : sevent) : Prop := match e with EvNull | EvBool _ | EvI64 _ | EvU64 _ | EvDbl _ => True | _ => False end.
Lemma ev_rel_scalar : forall lv w ps' e, scalar_ev e -> after_value_st ps' -> PML.ps_level ps' = lv -> ev_rel lv w ps' e.
Proof. intros lv w ps' e HS HA HL. destruct e; cbn [scalar_ev] in HS; try contradiction; cbn [ev_rel]; split; assumption. Qed.

Section Mem.
Variable segs : list Segment.

Definition vis_at_c (VT : Z) (M : mem) (V : Z) : Prop := L5.u64_at segs M V VT /\ L5.defined M V 48.
Definition ev_at (M : mem) (V : Z) (e : sevent) : Prop :=
  L5.defined M (V + 8) 40 /\
  match e with
  | EvNull => L5.u64_at segs M (V + 8) 4
  | EvBool b => L5.u64_at segs M (V + 8) 8 /\ L5.u8_at segs M (V + 32) (if b then 1 else 0)
  | EvI64 v => L5.u64_at segs M (V + 8) 16 /\ L5.u64_at segs M (V + 32) v
  | EvU64 v => L5.u64_at segs M (V + 8) 32 /\ L5.u64_at segs M (V + 32) v
  | EvDbl x => L5.u64_at segs M (V + 8) 128 /\ L5.u64_at segs M (V + 32) x
  | EvStr p n => L5.u64_at segs M (V + 8) 1 /\ L5.u64_at segs M (V + 32) p /\ L5.u64_at segs M (V + 40) n
  | EvKey p n => L5.u64_at segs M (V + 8) 4097 /\ L5.u64_at segs M (V + 32) p /\ L5.u64_at segs M (V + 40) n
  | EvBeginObj => L5.u64_at segs M (V + 8) 256
  | EvEndObj => L5.u64_at segs M (V + 8) 512
  | EvBeginArr => L5.u64_at segs M (V + 8) 1024
  | EvEndArr => L5.u64_at segs M (V + 8) 2048
  end.

Definition evp (M : mem) (V lv0 : Z) (w0 : option (Z * Z)) (ps' : PML.pstate) : Prop := exists e, ev_at M V e /\ ev_rel lv0 w0 ps' e.
Lemma evp_mono : forall M V lv w0 w ps', win_le w0 w -> evp M V lv w ps' -> evp M V lv w0 ps'.
Proof. intros M V lv w0 w ps' HW (e & H1 & H2). exists e. split; [exact H1 | exact (ev_rel_mono _ _ _ _ _ HW H2)]. Qed.

Definition cur_post (ps ps' : PML.pstate) (code : Z) (M' : mem) (V : Z) : Prop :=
  (code = 0 -> PML.ps_more ps' = true -> PML.ps_level ps' = PML.ps_level ps) /\
  (code = 0 -> PML.ps_more ps' = false ->
     (PML.ps_done ps' = true /\ PML.ps_st ps' = PML.ST_DONE /\ PML.ws_ok ps') \/
     (wf_c (ps_set_more ps' true) /\ evp M' V (PML.ps_level ps) (PML.ps_win ps) ps')).
End Mem.
End PMCUR.
