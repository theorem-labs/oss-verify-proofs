(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.skcms.iccprofile_info.images Require Plain.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg Nodes MmapSim AllocSim FileSim AgentLib ShapeLaws Spec LibWritev RefNodes RefExitBase.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require SymExec3 SymExec3Sound SymRun3 SymDrive3 SymPlan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require MallocDefs RefEnframeBase.
From Stdlib Require Zify.
Unset Nia Cache.  (* [comment removed for export] *)

Module SymSlots.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode.
Import OSSVerify.skcms.iccprofile_info.images.Plain.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MmapSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MallocDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefEnframeBase.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec3 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec3Sound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRun3.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymPlan.
Import Stdlib.micromega.Zify.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Open Scope Z_scope.

Module SSL.
Import SX2. Import SX2S. Import SP.

#[local] Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithFP1. Context {FP : PropExec.FPState}.
Definition slot_ok (E : env) (M : word -> option byte) (s : sslot) : Prop :=
  let st := uE E (sl_start s) in let sd := uE E (sl_stride s) in let nn := uE E (sl_n s) in
  let o := uE E (sl_off s) in let W := uE E (sl_W s) in
  enframe_post M (sl_idx s) nn sd st o
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
  enframe_post M idx nn sd st o ->
  4 <= st -> st + sd < 2 ^ 64 -> 0 <= nn ->
  hull_agree M M' st sd (st + 16 * o) nn ->
  enframe_post M' idx nn sd st o.
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
End WithFP1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].
End SSL.
End SymSlots.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.skcms.iccprofile_info.images Require Import Plain.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import
  PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg Nodes
  MmapSim AllocSim FileSim AgentLib ShapeLaws Spec LibWritev RefNodes RefExitBase.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import SymExec3 SymExec3Sound SymRun3 SymDrive3 SymPlan. Import SymSlots.
From Stdlib Require Import Zify.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Open Scope Z_scope.

Module SPSA.
Import SX2. Import SX2S. Import SP. Import SSL.

#[local] Abbreviation RSEGS := Plain.M.loaded_segments.

Section WithFP1. Context {FP : PropExec.FPState}.
Section NX0.
Variable nx0 : nat.
(* [comment removed for export] *)
Variable IT : itab.
Hypothesis IT_ok : itab_sound RSEGS IT.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition Wz (fd : Z) (bs : list Z) : list event := map (fun z => WriteEv (Z_to_bv 64 fd) (Z_to_bv 8 z)) bs.

Fixpoint sd (E : env) (fs : Fs.Fs) (s : shape) : TSet :=
  match s with
  | SNil => t_nil
  | SExit c => t_exit (Z_to_bv 64 c) fs
  | SEmit fd bs s' => t_emit (Wz fd bs) (sd E fs s')
  | SAlt2 a b => t_alt2 (sd E fs a) (sd E fs b)
  | SCase e mid s1 s2 => if (bv_unsigned (edenot E e) <=? mid)%Z then sd E fs s1 else sd E fs s2
  end.

Lemma sd_has_nil : forall E fs s, sd E fs s [].
Proof.
  intros E fs s. induction s; cbn [sd].
  - reflexivity.
  - apply t_exit_has_nil.
  - apply t_emit_has_nil.
  - apply t_alt2_has_nil_l. exact IHs1.
  - destruct (_ <=? _)%Z; assumption.
Qed.

Lemma salt2_sound : forall E fs a b,
  t_eq (t_alt2 (sd E fs a) (sd E fs b)) (sd E fs (salt2 a b)).
Proof.
  intros E fs a b. unfold salt2.
  destruct a; [cbn [sd]; apply t_alt2_nil_l; apply sd_has_nil|..];
  (destruct b; [cbn [sd]; apply t_alt2_nil_r; first [apply t_exit_has_nil | apply t_emit_has_nil
                  | apply t_alt2_has_nil_l; apply sd_has_nil | cbn [sd]; destruct (_ <=? _)%Z; apply sd_has_nil] | apply t_eq_refl ..]).
Qed.

(* [comment removed for export] *)
Fixpoint shape_vars_lt (b : nat) (s : shape) : bool :=
  match s with
  | SNil | SExit _ => true
  | SEmit _ _ s' => shape_vars_lt b s'
  | SAlt2 x y => shape_vars_lt b x && shape_vars_lt b y
  | SCase e _ x y => expr_vars_lt b e && shape_vars_lt b x && shape_vars_lt b y
  end.

(* [comment removed for export] *)
Lemma expr_vars_lt_eq : forall b e, SP.expr_vars_lt b e = SymRun3.expr_vars_lt b e.
Proof. intros b e. induction e; cbn; try rewrite IHe1, IHe2; try rewrite IHe; reflexivity. Qed.

Lemma sd_agree : forall b E E' fs s,
  env_agree b E E' -> shape_vars_lt b s = true -> sd E fs s = sd E' fs s.
Proof.
  intros b E E' fs s Hag. induction s; cbn [shape_vars_lt sd]; intros H; try reflexivity.
  - rewrite IHs by exact H. reflexivity.
  - apply andb_prop in H as [H1 H2]. rewrite IHs1, IHs2 by assumption. reflexivity.
  - apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    rewrite IHs1, IHs2 by assumption.
    rewrite (edenot_agree b E E' e Hag) by (rewrite <- expr_vars_lt_eq; exact H1). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition fds_std : list (word * FdEntry) :=
  [(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
   (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))].

(* [comment removed for export] *)
Definition iv_disjoint (p q : word * word) : Prop :=
  bv_unsigned (fst p) + bv_unsigned (snd p) <= bv_unsigned (fst q)
  \/ bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned (fst p).

Inductive seps : list (word * word) -> Prop :=
| seps_nil : seps []
| seps_cons : forall p l, Forall (iv_disjoint p) l -> seps l -> seps (p :: l).

Definition smap_ok (E : env) (maps : list (word * word)) (m : smap) : Prop :=
  let a := bv_unsigned (edenot E (sm_base m)) in
  let L := bv_unsigned (edenot E (sm_len m)) in
  0 < L < 2 ^ 64 /\ a + L <= 2 ^ 64 /\
  if sm_exact m then In (edenot E (sm_base m), edenot E (sm_len m)) maps
  else exists lo sz, In (lo, sz) maps /\ bv_unsigned lo <= a /\ a + L <= bv_unsigned lo + bv_unsigned sz.

Record vm_ok (E : env) (ms : list smap) (nmaps live : Z) (VM : VmMaps) : Prop := VM_OK {
  vo_res   : vm_reserved VM = segments_reserved RSEGS;
  vo_maps  : Forall (smap_ok E (vm_maps VM)) ms;
  vo_len   : Z.of_nat (length (vm_maps VM)) <= nmaps;
  vo_live  : vm_live_bytes VM <= live;
  vo_small : Forall (fun p => 0 < bv_unsigned (snd p) <= 2 ^ 30) (vm_maps VM);
  vo_nw    : Forall (fun p => bv_unsigned (fst p) + bv_unsigned (snd p) <= 2 ^ 64) (vm_maps VM);
  vo_seps  : seps (vm_maps VM);
  vo_limit : 2 ^ 31 <= vm_limit VM;
  vo_sp    : vm_init_sp VM = edenot E (EVar 0);  (* [comment removed for export] *)
  vo_sprange : 0x7fff80000000 <= bv_unsigned (vm_init_sp VM) <= 0x800000000000   (* [comment removed for export] *)
}.

Record cs_ok (E : env) (cs : cstate) (R : bvmap 5 word) (M : word -> option byte) (model : Model) : Prop := CS_OK {
  co_regs : regs_ok E (s_regs (c_ss cs)) R;
  co_know : know_ok RSEGS E M (s_know (c_ss cs));
  co_log  : s_log (c_ss cs) = [];
  co_halt : m_halted model = None;
  co_lazy : m_vm_lazy model = [];
  co_mat  : m_vm_materialized model = [];
  co_fds  : m_fds model = fds_std;
  co_vm   : vm_ok E (c_maps cs) (c_nmaps cs) (c_live cs) (m_vmmaps model);
  co_slots : slots_ok E M (c_slots cs)                       (* [comment removed for export] *)
}.

Definition cfg_of (R : bvmap 5 word) (p : Z) (M : word -> option byte) (model : Model) : config :=
  mkCfg (mkst R (Z_to_bv 64 p) M (seg_rom RSEGS)) model.

(* [comment removed for export] *)
Record std_model (VM : VmMaps) (model : Model) : Prop := STD_MODEL {
  stdm_fds  : m_fds model = fds_std;
  stdm_vm   : m_vmmaps model = VM;
  stdm_halt : m_halted model = None;
  stdm_lazy : m_vm_lazy model = [];
  stdm_mat  : m_vm_materialized model = []
}.

Lemma std_model_mk : forall VM stdin0 fs0 tid rlim,
  std_model VM (mkModel fds_std VM stdin0 fs0 None tid rlim).
Proof. intros. constructor; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma scs_denot_nil : forall base E, scs_denot RSEGS base E [].
Proof. intros. constructor. Qed.

Lemma run_block_sound : forall bfuel stops cs cs' E R M model,
  run_block RSEGS IT bfuel stops cs = Some cs' -> cs_ok E cs R M model ->
  exists R' M',
    msteps RSEGS (mkst R (Z_to_bv 64 (pc cs)) M (seg_rom RSEGS)) (mkst R' (Z_to_bv 64 (pc cs')) M' (seg_rom RSEGS))
    /\ cs_ok E cs' R' M' model
    /\ c_maps cs' = c_maps cs.
Proof.
  intros bfuel stops cs cs' E R M model Hrb HC.
  destruct HC as [HR HK HL Hh Hlz Hmt Hf HV HS]. unfold run_block in Hrb. rewrite sym_execT'_eq in Hrb. (* [comment removed for export] *)
  set (ss' := sym_execT RSEGS IT bfuel true stops (c_ss cs)) in Hrb.
  destruct (carry (s_log ss') (s_know ss') []) as [[kn' scs] hs] eqn:Hc.
  destruct scs; [|discriminate]. injection Hrb as <-.
  destruct (c_ss cs) as [p sr log k nx] eqn:Hss. cbn [s_log] in HL. subst log.
  pose proof (sym_execT_ex RSEGS IT bfuel true stops (SS p sr [] k nx) E M (seg_rom RSEGS)
                (mkst R (Z_to_bv 64 p) M (seg_rom RSEGS)) IT_ok
                (st_ok_entry RSEGS E M (seg_rom RSEGS) p sr k nx R HR HK)) as HX.
  cbn zeta in HX. fold ss' in HX. destruct HX as (R' & HR' & Hlf & HK' & Hms).
  exists R', (mem_denot E M (s_log ss')).
  unfold pc. rewrite Hss. cbn [c_ss s_pc].
  split; [exact Hms|]. split; [|reflexivity].
  assert (HKc : know_ok RSEGS E (mem_denot E M (s_log ss')) kn').
  { eapply (carry_sound RSEGS E M); [exact Hc | exact Hlf | exact HK' | apply scs_denot_nil]. }
  constructor; cbn [c_ss s_regs s_know s_log c_maps c_nmaps c_live c_slots]; try assumption; try reflexivity.
  eapply slots_carry_sound; [exact HKc | exact Hlf | exact HS].
Qed.


(* [comment removed for export] *)

Lemma cs_gc_ok : forall E cs R M model, cs_ok E cs R M model -> cs_ok E (cs_gc cs) R M model.
Proof.
  intros E cs R M model [HR HK HL Hh Hlz Hmt Hf HV HS]. unfold cs_gc.
  destruct (split_lit (reg cs 2)) as [spb spk].
  constructor; cbn [set_kn c_ss s_regs s_know s_log c_maps c_nmaps c_live c_slots]; try assumption; try reflexivity.
  unfold know_ok in *. apply Forall_forall. intros K Hin. apply filter_In in Hin as [Hin _].
  exact (proj1 (Forall_forall _ _) HK K Hin).
Qed.

Lemma pc_cs_gc : forall cs, pc (cs_gc cs) = pc cs.
Proof. intros cs. unfold cs_gc. destruct (split_lit (reg cs 2)); reflexivity. Qed.

Lemma c_maps_cs_gc : forall cs, c_maps (cs_gc cs) = c_maps cs.
Proof. intros cs. unfold cs_gc. destruct (split_lit (reg cs 2)); reflexivity. Qed.

Lemma run_block_gc_sound : forall bfuel stops cs cs' E R M model,
  run_block_gc RSEGS IT bfuel stops cs = Some cs' -> cs_ok E cs R M model ->
  exists R' M',
    msteps RSEGS (mkst R (Z_to_bv 64 (pc cs)) M (seg_rom RSEGS)) (mkst R' (Z_to_bv 64 (pc cs')) M' (seg_rom RSEGS))
    /\ cs_ok E cs' R' M' model
    /\ c_maps cs' = c_maps cs.
Proof.
  intros bfuel stops cs cs' E R M model H HC. unfold run_block_gc in H.
  destruct (run_block RSEGS IT bfuel stops cs) as [cs1|] eqn:Hrb; [|discriminate]. injection H as <-.
  destruct (run_block_sound bfuel stops cs cs1 E R M model Hrb HC) as (R' & M' & Hms & HC1 & Hmaps).
  exists R', M'. rewrite pc_cs_gc, c_maps_cs_gc. split; [exact Hms|]. split; [apply cs_gc_ok; exact HC1 | exact Hmaps].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ext1 (E : env) (v : nat) (a : word) : env :=
  Env (fun n => if Nat.eqb n v then a else ev E n) (eb E).

Lemma ext1_agree : forall E v a, env_agree v E (ext1 E v a).
Proof.
  intros E v a. split; [|reflexivity]. intros n Hn. cbn [ext1 ev].
  destruct (Nat.eqb_spec n v); [lia | reflexivity].
Qed.

Lemma ext1_at : forall E v a, ev (ext1 E v a) v = a.
Proof. intros. cbn [ext1 ev]. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma env_agree_le : forall b b' E E', env_agree b' E E' -> (b <= b')%nat -> env_agree b E E'.
Proof. intros b b' E E' [H1 H2] Hle. split; [|exact H2]. intros n Hn. apply H1. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma ridx_lit : forall n, (n < 32)%nat -> ridx (Z_to_bv 5 (Z.of_nat n)) = n.
Proof.
  intros n Hn. unfold ridx. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 5) with 32%Z. rewrite Z.mod_small by lia. lia.
Qed.

Lemma reg_sound : forall E cs R M model n,
  cs_ok E cs R M model -> (0 < n < 32)%nat ->
  getr R (Z_to_bv 5 (Z.of_nat n)) = edenot E (reg cs n).
Proof.
  intros E cs R M model n HC Hn. rewrite (co_regs _ _ _ _ _ HC). unfold sr_get, reg.
  assert (Hnz : bv_eqb (Z_to_bv 5 (Z.of_nat n)) 0%bv = false).
  { unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 5) with 32%Z. rewrite Z.mod_small by lia.
    replace (bv_unsigned (0%bv : bv 5)) with 0%Z by reflexivity. lia. }
  rewrite Hnz. rewrite ridx_lit by lia. reflexivity.
Qed.

Lemma lit_of_sound : forall E e z, lit_of e = Some z -> edenot E e = Z_to_bv 64 z /\ (0 <= z < two64)%Z.
Proof.
  intros E e z H. destruct e; try discriminate. cbn [lit_of] in H. injection H as <-.
  split; [| unfold two64; apply Z.mod_pos_bound; lia].
  cbn [edenot]. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. unfold two64.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma reg_lit_sound : forall E cs R M model n z,
  cs_ok E cs R M model -> (0 < n < 32)%nat -> reg_lit cs n = Some z ->
  getr R (Z_to_bv 5 (Z.of_nat n)) = Z_to_bv 64 z /\ (0 <= z < two64)%Z.
Proof.
  intros E cs R M model n z HC Hn H. unfold reg_lit in H.
  destruct (lit_of_sound E (reg cs n) z H) as [He Hz]. rewrite (reg_sound E cs R M model n HC Hn), He. auto.
Qed.

Lemma is_ecall_at_sound : forall cs, is_ecall_at RSEGS cs = true ->
  exists w, fetch_word RSEGS (Z_to_bv 64 (pc cs)) = Some w /\ is_ecall w = true
            /\ (0 <= pc cs)%Z /\ (pc cs + 4 < 2 ^ 64)%Z.
Proof.
  intros cs H. unfold is_ecall_at in H.
  apply andb_prop in H as [H Hf]. apply andb_prop in H as [H0 H4].
  apply Z.leb_le in H0. apply Z.ltb_lt in H4. unfold two64 in H4.
  destruct (fetch_word RSEGS (Z_to_bv 64 (pc cs))) as [w|]; [|discriminate].
  exists w. auto.
Qed.

(* [comment removed for export] *)
Lemma cs_ok_set_reg_pc : forall E cs R M model n e v p,
  cs_ok E cs R M model -> (0 < n < 32)%nat -> edenot E e = v ->
  cs_ok E (set_pc (set_reg cs n e) p) (regupd R (Z_to_bv 5 (Z.of_nat n)) v) M model.
Proof.
  intros E cs R M model n e v p HC Hn He. destruct HC as [HR HK HL Hh Hlz Hmt Hf HV HS].
  constructor; cbn [set_pc set_reg c_ss s_regs s_know s_log c_maps c_nmaps c_live c_slots]; try assumption; try reflexivity.
  replace (sr_upd (s_regs (c_ss cs)) n e) with (sr_upd (s_regs (c_ss cs)) (ridx (Z_to_bv 5 (Z.of_nat n))) e)
    by (rewrite ridx_lit by lia; reflexivity).
  apply regs_ok_set; [exact HR | | exact He].
  intros Hz. apply (f_equal bv_unsigned) in Hz. rewrite Z_to_bv_unsigned in Hz. unfold bv_wrap in Hz.
  change (bv_modulus 5) with 32%Z in Hz. rewrite Z.mod_small in Hz by lia.
  replace (bv_unsigned (0%bv : bv 5)) with 0%Z in Hz by reflexivity. lia.
Qed.

Lemma pc_set_pc : forall cs n e p, pc (set_pc (set_reg cs n e) p) = p.
Proof. reflexivity. Qed.

Lemma v_addi_pc : forall p, (0 <= p)%Z -> (p + 4 < 2 ^ 64)%Z -> v_addi (Z_to_bv 64 p) 4 = Z_to_bv 64 (p + 4).
Proof. intros. apply v_addi_pc4; assumption. Qed.

Lemma m_fs_mmap_model : forall a n m, m_fs (mmap_model a n m) = m_fs m.
Proof. reflexivity. Qed.
Lemma m_fs_munmap_model : forall a n m, m_fs (munmap_model a n m) = m_fs m.
Proof. reflexivity. Qed.

Lemma split_sound : forall cs e mid lo hi E R M model,
  cs_ok E cs R M model -> erange (kn cs) e = Some (lo, hi) ->
  (bv_unsigned (edenot E e) <= mid -> cs_ok E (set_kn cs (KRange e lo mid :: kn cs)) R M model)
  /\ (mid < bv_unsigned (edenot E e) -> cs_ok E (set_kn cs (KRange e (mid + 1) hi :: kn cs)) R M model).
Proof.
  intros cs e mid lo hi E R M model HC Hr.
  destruct HC as [HR HK HL Hh Hlz Hmt Hf HV HS].
  pose proof (erange_sound RSEGS E M (kn cs) e lo hi HK Hr) as Hb.
  split; intros Hm; constructor; cbn [set_kn c_ss s_regs s_know s_log c_maps c_nmaps c_live c_slots]; try assumption; try reflexivity;
    (constructor; [cbn [kentry_ok]; lia | exact HK]).
Qed.


End NX0.
End WithFP1.

End SPSA.
