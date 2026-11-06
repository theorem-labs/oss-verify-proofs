(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec StoreOk MmapSim MallocDefs.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import EnframeDefs.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SymExec3 SymExec3Sound SymRun3.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SymPlan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Module SSL.
Import SX2. Import SX2S. Import SP.

Section WithSegs.
Variable RSEGS : list Segment.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition slot_ok (E : env) (M : word -> option byte) (s : sslot) : Prop :=
  let st := uE E (sl_start s) in let sd := uE E (sl_stride s) in let nn := uE E (sl_n s) in
  let o := uE E (sl_off s) in let W := uE E (sl_W s) in
  enframe_post RSEGS M (sl_idx s) nn sd st o
  /\ uE E (sl_p s) = st + 16 * o
  /\ (let (hb, hk) := split_lit (sl_start s) in uE E hb + hk = st)
  /\ (let (pb, pk) := split_lit (sl_p s) in uE E pb + pk = st + 16 * o)
  /\ sd = slot_stride (w_maplen W) (w_lastidx W) (w_sizeclass W)
  /\ ((w_maplen W = 0 \/ w_lastidx W <> 0) -> w_sizeclass W < 48)
  /\ 16 <= sd < 2 ^ 31 /\ sd mod 16 = 0 /\ st mod 16 = 0
  /\ 16 + sd * sl_idx s <= st /\ st + sd < 2 ^ 64
  /\ 0 <= sl_idx s < 32 /\ sd * sl_idx s + 4096 <= 16 * 65536.

Definition slots_ok (E : env) (M : word -> option byte) (ss : list sslot) : Prop :=
  Forall (slot_ok E M) ss.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u64_of_Z : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z : word) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned, bv_wrap64_mod. apply Z.mod_small. exact Hz. Qed.

(* [comment removed for export] *)
Definition hull_agree (M M' : word -> option byte) (st sd p nn : Z) : Prop :=
  forall x : word, st - 4 <= bv_unsigned x < st + sd - 4 ->
                   ~ (p <= bv_unsigned x < p + nn) -> M' x = M x.

Lemma enframe_post_agree : forall M M' idx nn sd st o,
  enframe_post RSEGS M idx nn sd st o ->
  4 <= st -> st + sd < 2 ^ 64 -> 0 <= nn ->
  hull_agree M M' st sd (st + 16 * o) nn ->
  enframe_post RSEGS M' idx nn sd st o.
Proof.
  intros M M' idx nn sd st o P Hst Hnw Hnn HA.
  destruct P as [pp pe pr pq Pm4 Pm3 Pm2 Pzr Pe5 Pe4 Ps3 Ps2 Pr]. subst pp pe pr pq.
  assert (B1 : forall a, st - 4 <= a < st + sd - 4 -> ~ (st + 16 * o <= a < st + 16 * o + nn) ->
               M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha Hn. apply HA; rewrite u64_of_Z by lia; assumption. }
  assert (RD : forall a k, st - 4 <= a -> a + Z.of_nat k <= st + sd - 4 ->
               (a + Z.of_nat k <= st + 16 * o \/ st + 16 * o + nn <= a) ->
               rdn RSEGS M' (Z_to_bv 64 a) k = rdn RSEGS M (Z_to_bv 64 a) k).
  { intros a k Ha Hk Hs. apply rdn_ext; [rewrite u64_of_Z by lia; lia|].
    intros x Hx. rewrite u64_of_Z in Hx by lia. apply HA; lia. }
  constructor; cbn zeta.
  - rewrite B1 by lia. exact Pm4.
  - rewrite B1 by lia. exact Pm3.
  - rewrite RD by (cbn; lia). exact Pm2.
  - intros Hr. rewrite B1 by lia. exact (Pzr Hr).
  - intros Hr. rewrite B1 by lia. exact (Pe5 Hr).
  - intros Hr. rewrite RD by (cbn; lia). exact (Pe4 Hr).
  - intros Ho. rewrite B1 by lia. exact (Ps3 Ho).
  - intros Ho. rewrite RD by (cbn; lia). exact (Ps2 Ho).
  - exact Pr.
Qed.

Lemma slot_ok_agree : forall E M M' s,
  slot_ok E M s ->
  hull_agree M M' (uE E (sl_start s)) (uE E (sl_stride s)) (uE E (sl_p s)) (uE E (sl_n s)) ->
  slot_ok E M' s.
Proof.
  intros E M M' s HS HA. unfold slot_ok in *.
  destruct HS as (P & REST). split; [| exact REST].
  destruct REST as (Hp & Hh & Hpp & Hsd & Hsc & Hsd2 & Hmod & Hmod2 & Hlo & Hnw & Hidx & Hq).
  pose proof (u64_range (edenot E (sl_n s))) as Hn. unfold uE in *.
  destruct (split_lit (sl_start s)) as [hb hk]. destruct (split_lit (sl_p s)) as [pb pk].
  eapply enframe_post_agree; [exact P | nia | lia | lia |].
  rewrite <- Hp. exact HA.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma split_lit_u : forall E e b k, split_lit e = (b, k) ->
  edenot E e = Z_to_bv 64 (bv_unsigned (edenot E b) + k).
Proof.
  intros E e b k H.
  assert (G : forall e' : expr, edenot E e' = Z_to_bv 64 (bv_unsigned (edenot E e') + 0)).
  { intros e'. rewrite Z.add_0_r. symmetry. apply Z_to_bv_bv_unsigned. }
  unfold split_lit in H.
  destruct e; try (injection H as <- <-; apply G).
  - injection H as <- <-. cbn [edenot]. rewrite u64_of_Z by lia. rewrite Z.add_0_l. reflexivity.
  - lazymatch type of H with (match ?o with _ => _ end = _) => destruct o end; try (injection H as <- <-; apply G).
    lazymatch type of H with (match ?y with _ => _ end = _) => destruct y end; try (injection H as <- <-; apply G).
    injection H as <- <-. cbn [edenot]. rewrite alu_add. unfold v_add. apply bv_eq.
    rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Z.add_mod_idemp_r by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma slot_keep_b_sound : forall E M0 k ub uk un s,
  know_ok RSEGS E M0 k -> slot_keep_b k ub uk un s = true ->
  forall M, slot_ok E M s ->
  let a := estart E (SA ub uk) in let len := elenZ E un in
  let st := uE E (sl_start s) in let sd := uE E (sl_stride s) in
  let p := uE E (sl_p s) in let nn := uE E (sl_n s) in
  (a + len <= st - 4 \/ st + sd - 4 <= a) \/ (p <= a /\ a + len <= p + nn).
Proof.
  intros E M0 k ub uk un s Hk H M HS. cbv zeta.
  unfold slot_ok in HS. destruct HS as (P & Hp & Hh & Hpp & _).
  unfold slot_keep_b in H.
  destruct (split_lit (sl_start s)) as [hb hk] eqn:Hs1.
  lazymatch type of H with (if ?c then _ else _) = _ => destruct c eqn:Hap end.
  - left. pose proof (ranges_apart_x_sound RSEGS E M0 k ub uk un hb (hk - 4) (sl_stride s) Hk Hap) as A.
    unfold estart, elenZ in *. cbn [a_base a_off] in *. unfold uE in *. lia.
  - right. destruct (split_lit (sl_p s)) as [pb pk] eqn:Hs2.
    pose proof (xinside_sound RSEGS E M0 k ub uk un pb pk (sl_n s) Hk H) as [A B].
    unfold estart, elenZ in *. cbn [a_base a_off] in *. unfold uE in *. lia.
Qed.

Lemma slot_apart_b_sound : forall E M0 k ub uk un s,
  know_ok RSEGS E M0 k -> slot_apart_b k ub uk un s = true ->
  forall M, slot_ok E M s ->
  let a := estart E (SA ub uk) in let len := elenZ E un in
  let st := uE E (sl_start s) in let sd := uE E (sl_stride s) in
  a + len <= st - 4 \/ st + sd - 4 <= a.
Proof.
  intros E M0 k ub uk un s Hk H M HS. cbv zeta.
  unfold slot_ok in HS. destruct HS as (P & Hp & Hh & Hpp & _).
  unfold slot_apart_b in H.
  destruct (split_lit (sl_start s)) as [hb hk] eqn:Hs1.
  pose proof (ranges_apart_x_sound RSEGS E M0 k ub uk un hb (hk - 4) (sl_stride s) Hk H) as A.
  unfold estart, elenZ in *. cbn [a_base a_off] in *. unfold uE in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mod_within (M M' : word -> option byte) (a len : Z) : Prop :=
  forall x : word, (bv_unsigned x < a \/ a + len <= bv_unsigned x) -> M' x = M x.

Lemma slot_ok_mod : forall E M0 k ub uk un s M M',
  know_ok RSEGS E M0 k -> slot_keep_b k ub uk un s = true ->
  slot_ok E M s -> mod_within M M' (estart E (SA ub uk)) (elenZ E un) ->
  slot_ok E M' s.
Proof.
  intros E M0 k ub uk un s M M' Hk Hb HS Hmod.
  pose proof (slot_keep_b_sound E M0 k ub uk un s Hk Hb M HS) as D. cbv zeta in D.
  eapply slot_ok_agree; [exact HS|].
  intros x Hx Hnu. apply Hmod. lia.
Qed.

Lemma slots_keep_sound : forall E M0 k ub uk un ss M M',
  know_ok RSEGS E M0 k -> slots_ok E M ss ->
  mod_within M M' (estart E (SA ub uk)) (elenZ E un) ->
  slots_ok E M' (slots_keep k ub uk un ss).
Proof.
  intros E M0 k ub uk un ss M M' Hk HS Hmod. unfold slots_keep, slots_ok in *.
  apply Forall_forall. intros s Hin. apply filter_In in Hin as [Hin Hb].
  eapply slot_ok_mod; [exact Hk | exact Hb | | exact Hmod].
  exact (proj1 (Forall_forall _ _) HS s Hin).
Qed.

Lemma wbytes_mod_within : forall M (a : word) bs,
  bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64 ->
  mod_within M (wbytes M a bs) (bv_unsigned a) (Z.of_nat (length bs)).
Proof. intros M a bs Hnw x Hx. apply wbytes_out; [exact Hnw | exact Hx]. Qed.

(* [comment removed for export] *)
Lemma slots_carry_sound : forall E M0 k log ss M,
  know_ok RSEGS E M0 k -> log_flat E log -> slots_ok E M ss ->
  slots_ok E (mem_denot E M log) (slots_carry k log ss).
Proof.
  intros E M0 k log ss M Hk. rewrite slots_carry_eq. (* [comment removed for export] *)
  induction log as [|[[b o] w v] older IH]; intros Hlf HS; cbn [mem_denot slots_carry_ref].
  - exact HS.
  - cbn [log_flat] in Hlf. destruct Hlf as (Hw & Hfl & Hlf').
    specialize (IH Hlf' HS).
    eapply slots_keep_sound; [exact Hk | exact IH |].
    pose proof (flat_u E (SA b o) (Z.of_nat w) Hfl) as U.
    intros x Hx. apply wbytes_out.
    + rewrite length_N_to_le_bytes, U. destruct Hfl as (F1 & F2 & F3 & F4). lia.
    + rewrite length_N_to_le_bytes, U. unfold elenZ in Hx. cbn [edenot] in Hx.
      rewrite u64_of_Z in Hx by lia. exact Hx.
Qed.

(* [comment removed for export] *)
Lemma slots_unfill_sound : forall E M0 k ub un ss M,
  know_ok RSEGS E M0 k -> slots_ok E M ss ->
  flat E (SA ub 0) (elenZ E un) ->
  slots_ok E (unfill (edenot E ub) (edenot E un) M) (slots_unfill k ub 0 un ss).
Proof.
  intros E M0 k ub un ss M Hk HS Hfl. unfold slots_unfill, slots_ok in *.
  apply Forall_forall. intros s Hin. apply filter_In in Hin as [Hin Hb].
  pose proof (proj1 (Forall_forall _ _) HS s Hin) as HSs.
  pose proof (slot_apart_b_sound E M0 k ub 0 un s Hk Hb M HSs) as D. cbv zeta in D.
  eapply slot_ok_agree; [exact HSs|].
  intros x Hx _. apply unfill_out.
  unfold estart, elenZ in D. cbn [a_base a_off] in D. unfold uE in *. lia.
Qed.

(* [comment removed for export] *)
Lemma sp_expr_vars_lt_eq : forall b e, SP.expr_vars_lt b e = SymRun3.expr_vars_lt b e.
Proof. intros b e. induction e; cbn; try rewrite IHe1, IHe2; try rewrite IHe; reflexivity. Qed.

Lemma uE_agree : forall b E E' e, env_agree b E E' -> SP.expr_vars_lt b e = true -> uE E' e = uE E e.
Proof.
  intros b E E' e Hag Hv. unfold uE. rewrite (edenot_agree b E E' e Hag); [reflexivity|].
  rewrite <- sp_expr_vars_lt_eq. exact Hv.
Qed.

Lemma split_lit_vars : forall b e hb hk, split_lit e = (hb, hk) -> SP.expr_vars_lt b e = true -> SP.expr_vars_lt b hb = true.
Proof.
  intros b e hb hk H Hv. unfold split_lit in H.
  destruct e; try (injection H as <- <-; first [exact Hv | reflexivity]).
  - lazymatch type of H with (match ?o with _ => _ end = _) => destruct o end; try (injection H as <- <-; exact Hv).
    lazymatch type of H with (match ?y with _ => _ end = _) => destruct y end; try (injection H as <- <-; exact Hv).
    injection H as <- <-. cbn [SP.expr_vars_lt] in Hv. apply andb_prop in Hv as [H1 _]. exact H1.
Qed.

Lemma slot_ok_ext : forall b E E' M s,
  env_agree b E E' -> slot_vars_lt b s = true -> slot_ok E M s -> slot_ok E' M s.
Proof.
  intros b E E' M s Hag Hv HS. unfold slot_vars_lt in Hv.
  apply andb_prop in Hv as [Hv H6]. apply andb_prop in Hv as [Hv H5]. apply andb_prop in Hv as [Hv H4].
  apply andb_prop in Hv as [Hv H3]. apply andb_prop in Hv as [H1 H2].
  unfold slot_ok in *.
  rewrite !(uE_agree b E E' _ Hag) by assumption.
  destruct (split_lit (sl_start s)) as [hb hk] eqn:Hs1. destruct (split_lit (sl_p s)) as [pb pk] eqn:Hs2.
  rewrite (uE_agree b E E' hb Hag) by (eapply split_lit_vars; [exact Hs1 | exact H1]).
  rewrite (uE_agree b E E' pb Hag) by (eapply split_lit_vars; [exact Hs2 | exact H6]).
  exact HS.
Qed.

Lemma slots_ok_ext : forall b E E' M ss,
  env_agree b E E' -> slots_vars_lt b ss = true -> slots_ok E M ss -> slots_ok E' M ss.
Proof.
  intros b E E' M ss Hag Hv HS. unfold slots_ok, slots_vars_lt in *.
  apply Forall_forall. intros s Hin.
  eapply slot_ok_ext; [exact Hag | | exact (proj1 (Forall_forall _ _) HS s Hin)].
  exact (proj1 (forallb_forall _ _) Hv s Hin).
Qed.

(* [comment removed for export] *)
Lemma slots_ok_filter : forall E M f ss, slots_ok E M ss -> slots_ok E M (List.filter f ss).
Proof.
  intros E M f ss HS. unfold slots_ok in *. apply Forall_forall. intros s Hin.
  apply filter_In in Hin as [Hin _]. exact (proj1 (Forall_forall _ _) HS s Hin).
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End WithSegs.
End SSL.
