(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Mem Frame Cells Step. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require RzCPS.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_state RT_main_shape.
From OssFuzzTheorems.Proofs.openssl.ct.lib.VCommon Require Import FastWord.
From OssFuzzTheorems.Proofs.openssl.ct.lib.VCommon.Ax Require Import ExTrie ExBytes AxLazy AxLin AxVal AxBytes AxMem AxZZ AxScan AxState AxSys AxLz AxModelRel.
From OssFuzzTheorems.Proofs.openssl.ct.lib.AxA Require Import AxExport AxExportM AxExportH AxExportQ AxExportV.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtAxA Require Import AxExportS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Section Facts.
Hypothesis Hlow : segs_low ctasegs.
Variable fs0 : Fs.Fs.
Variable LIM : Z.
Variable ρ : valuation.
Variable B : AST.
Variable ms : machine_state.
Variable model : Model.
Hypothesis HR : R ctasegs amodel (MR ctasegs fs0 ρ) LIM ρ B (mkCfg ms model).
Variable W : list (lin * Z).
Variable J : Z.
Variable F : bforms.
Variable maps0 : list (word * word).

Definition Lm : layoutA := L_of ρ F maps0 (A' ρ W J).
Definition AFull : list (Z * Z) := AF ρ W J (allow_main Lm).
Definition mM : mem := AxExport.mX ms model AFull.

Local Notation vis := (AxExport.vis model AFull).
Let Hsat : sat ρ (a_facts B) := r_sat _ _ _ _ _ _ _ HR.

(* [comment removed for export] *)
Hypothesis Hpos : forall C, In C (a_mem B) -> 0 < to_Z (rg_n C).
Hypothesis HwL : has_wit (a_facts B) ls_beg ls_end (a_mem B) = true.
Hypothesis HwH : has_wit (a_facts B) hs_beg hs_hi (a_mem B) = true.
Hypothesis Hsp : 0x7fff80000000 <= l_sp0 Lm <= 2 ^ 47.     (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition q_at (f : lin) (n : Z) : option (region * int) := q_find B (snd f) (wofZ (fst f)) (of_Z n).

Lemma q_at_spec (f : lin) (n : Z) (Rq : region) (x : int) : 0 < n < 2 ^ 62 -> 0 <= leval ρ f < 2 ^ 64 ->
  q_at f n = Some (Rq, x) ->
  In Rq (a_mem B) /\ is_entry Rq = false /\ leval ρ f = rbase ρ Rq + to_Z x /\ to_Z x + n <= to_Z (rg_n Rq).
Proof.
  intros Hn Hf H. unfold q_at in H.
  assert (En : to_Z (of_Z n) = n) by (apply phi_of_Z_small; lia).
  destruct (q_find_spec ctasegs fs0 LIM ρ B ms model HR (snd f) (wofZ (fst f)) (of_Z n) Rq x ltac:(lia) H) as (H1 & H2 & H3 & H4).
  split; [exact H1|]. split; [exact H2|]. split; [|lia].
  rewrite <- H3. unfold smod, leval. rewrite wZ_wofZ. unfold FastWord.two64. rewrite Zplus_mod_idemp_r.
  rewrite Z.mod_small; [lia | unfold leval in Hf; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rng_ok (f : lin) (size : Z) : bool :=
  match lrange (a_facts B) f with Some (lo, hi) => (0 <=? lo) &&& (hi + size <=? 140737488355328) | None => false end.

Definition vis_sa (a : saddr) (n : Z) : bool :=
  match a with
  | SAsh b off sh =>
      (0 <=? sh) &&& (0 <=? n) &&&
      match b with
      | LB_lit => (0x10000 <=? off) &&& (off + 8 * (sh + n) <=? SEGTOP_A)
      | LB_SB => (0 <=? off) &&& (off + 8 * (sh + n) <=? 2 ^ 37) &&& rng_ok (bf_SB F) (2 ^ 37)
      | LB_FSB => (0 <=? off) &&& (off + 8 * (sh + n) <=? 0xb09000) &&& rng_ok (bf_FSB F) 0xb09000
      | LB_ACEIL => (0 <=? off) &&& (off + 8 * (sh + n) <=? STACK_WIN)
      | LB_sp0 => (- STACK_WIN <=? off) &&& (off + 8 * (sh + n) <=? 0)
      | _ => false
      end
  | SA LB_lit off => (0 <=? n) &&& (pg_dn (shad 0x10000) <=? off) &&& (off + n <=? pg_up (shad SEGTOP_A))
  | _ => false
  end.

Lemma pg_dn_spec (z : Z) : pg_dn z <= z /\ pg_dn z mod 4096 = 0.
Proof. exact (pdn_spec z). Qed.
Lemma pg_up_spec (z : Z) : z <= pg_up z /\ pg_up z mod 4096 = 0.
Proof. destruct (pup_spec z) as (H1 & H2 & _). split; assumption. Qed.

(* [comment removed for export] *)
Lemma shad_in (lo hi x sh n z : Z) : lo <= x -> 0 <= sh -> x + 8 * (sh + n) <= hi -> shad x + sh <= z < shad x + sh + n ->
  pg_dn (shad lo) <= z < pg_up (shad hi).
Proof.
  intros H1 H2 H3 Hz. destruct (pg_dn_spec (shad lo)) as [D1 _]. destruct (pg_up_spec (shad hi)) as [U1 _].
  assert (E : shad (x + 8 * (sh + n)) = shad x + sh + n) by (unfold shad; rewrite (Z.mul_comm 8), Z.div_add by lia; lia).
  assert (M1 : shad lo <= shad x) by (unfold shad; pose proof (Z.div_le_mono lo x 8 ltac:(lia) H1); lia).
  assert (M2 : shad (x + 8 * (sh + n)) <= shad hi) by (unfold shad; pose proof (Z.div_le_mono _ _ 8 ltac:(lia) H3); lia).
  lia.
Qed.

Lemma in_allow_main (k : nat) (iv : Z * Z) : nth_error (allow_main Lm) k = Some iv -> In iv (allow_main Lm).
Proof. apply nth_error_In. Qed.

Theorem vis_sa_sound (a : saddr) (n : Z) : vis_sa a n = true ->
  0 <= den_addr Lm a /\ den_addr Lm a + n <= 2 ^ 47 /\ vis (den_addr Lm a) (den_addr Lm a + n).
Proof.
  assert (HX : forall lo hi x sh, In (pg_dn (shad lo), pg_up (shad hi)) (allow_main Lm) -> 0 <= lo -> lo <= x -> 0 <= sh -> 0 <= n ->
             x + 8 * (sh + n) <= hi -> hi <= 2 ^ 47 ->
             0 <= shad x + sh /\ shad x + sh + n <= 2 ^ 47 /\ vis (shad x + sh) (shad x + sh + n)).
  { intros lo hi x sh HIn H0 H1 H2 Hn H3 H4.
    assert (B1 : 0 <= shad x) by (unfold shad, SHB; pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)); lia).
    assert (B2 : shad x + sh + n <= shad hi).
    { replace (shad x + sh + n) with (shad (x + 8 * (sh + n))) by (unfold shad; rewrite (Z.mul_comm 8), Z.div_add by lia; lia).
      unfold shad. pose proof (Z.div_le_mono _ _ 8 ltac:(lia) H3). lia. }
    assert (B3 : shad hi < 2 ^ 47) by (unfold shad, SHB; pose proof (Z.div_le_mono _ _ 8 ltac:(lia) H4); change (2 ^ 47 / 8) with (2 ^ 44) in *; lia).
    split; [lia|]. split; [lia|]. intros z Hz.
    apply (vis_X ρ model W J (allow_main Lm) _ _ z HIn (proj2 (pg_dn_spec _)) (proj2 (pg_up_spec _))); [|lia].
    exact (shad_in lo hi x sh n z H1 H2 H3 Hz). }
  destruct a as [b off|b off sh]; cbn [vis_sa].
  - destruct b; try discriminate. intros H. apply land_true in H as [H H3]. apply land_true in H as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. cbn [den_addr den_base]. rewrite Z.add_0_l.
    destruct (pg_dn_spec (shad 0x10000)) as [D1 D2]. destruct (pg_up_spec (shad SEGTOP_A)) as [U1 U2].
    assert (P0 : 0 <= pg_dn (shad 0x10000)) by (vm_compute; discriminate).
    assert (P1 : pg_up (shad SEGTOP_A) < 2 ^ 47) by (vm_compute; reflexivity).
    split; [lia|]. split; [lia|]. intros z Hz.
    apply (vis_X ρ model W J (allow_main Lm) _ _ z (in_allow_main 0 _ eq_refl) D2 U2); lia.
  - intros H. apply land_true in H as [H Hb]. apply land_true in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    cbn [den_addr]. destruct b; try discriminate Hb.
    + (* [comment removed for export] *)
      apply land_true in Hb as [H3 H4]. apply Z.leb_le in H3. apply Z.leb_le in H4. cbn [den_base]. rewrite Z.add_0_l.
      apply (HX 0x10000 SEGTOP_A off sh (in_allow_main 0 _ eq_refl)); try lia. unfold SEGTOP_A. lia.
    + (* [comment removed for export] *)
      apply land_true in Hb as [H3 H4]. apply Z.leb_le in H3. apply Z.leb_le in H4. cbn [den_base].
      apply (HX (l_ACEIL Lm) (2 ^ 47) (l_sp0 Lm + off) sh (in_allow_main 3 _ eq_refl)); unfold l_ACEIL, STACK_WIN in *; lia.
    + (* [comment removed for export] *)
      apply land_true in Hb as [Hb Hr]. apply land_true in Hb as [H3 H4]. apply Z.leb_le in H3. apply Z.leb_le in H4. cbn [den_base].
      unfold rng_ok in Hr. destruct (lrange (a_facts B) (bf_SB F)) as [[lo hi]|] eqn:El; [|discriminate Hr].
      apply land_true in Hr as [R1 R2]. apply Z.leb_le in R1. apply Z.leb_le in R2.
      pose proof (lrange_sound ρ _ _ Hsat _ El) as Xr. cbn [fst snd] in Xr. change 140737488355328 with (2 ^ 47) in R2.
      apply (HX (l_SB Lm) (l_SB Lm + 2 ^ 37) (l_SB Lm + off) sh (in_allow_main 1 _ eq_refl)); unfold Lm, L_of in *; cbn [l_SB] in *; lia.
    + (* [comment removed for export] *)
      apply land_true in Hb as [Hb Hr]. apply land_true in Hb as [H3 H4]. apply Z.leb_le in H3. apply Z.leb_le in H4. cbn [den_base].
      unfold rng_ok in Hr. destruct (lrange (a_facts B) (bf_FSB F)) as [[lo hi]|] eqn:El; [|discriminate Hr].
      apply land_true in Hr as [R1 R2]. apply Z.leb_le in R1. apply Z.leb_le in R2.
      pose proof (lrange_sound ρ _ _ Hsat _ El) as Xr. cbn [fst snd] in Xr. change 140737488355328 with (2 ^ 47) in R2.
      apply (HX (l_FSB Lm) (l_FSB Lm + 0xb09000) (l_FSB Lm + off) sh (in_allow_main 2 _ eq_refl)); unfold Lm, L_of in *; cbn [l_FSB] in *; lia.
    + (* [comment removed for export] *)
      apply land_true in Hb as [H3 H4]. apply Z.leb_le in H3. apply Z.leb_le in H4. cbn [den_base].
      apply (HX (l_ACEIL Lm) (2 ^ 47) (l_ACEIL Lm + off) sh (in_allow_main 3 _ eq_refl)); unfold l_ACEIL, STACK_WIN in *; lia.
Qed.

(* [comment removed for export] *)
Definition vis_any (top : Z) (a : saddr) (f : lin) (n : Z) : bool := vis_ok B W top f n ||| vis_sa a n.

Lemma vis_any_sound (top : Z) (a : saddr) (f : lin) (n : Z) : sa_form F a = Some f -> vis_any top a f n = true ->
  0 <= den_addr Lm a /\ den_addr Lm a + n <= 2 ^ 47 /\ vis (den_addr Lm a) (den_addr Lm a + n).
Proof.
  intros Hf H. apply lor_true in H as [H|H]; [|exact (vis_sa_sound a n H)].
  pose proof (sa_form_sound ρ F maps0 (A' ρ W J) a f Hf) as EA. fold Lm in EA. rewrite <- EA.
  destruct (vis_ok_sound ctasegs fs0 LIM ρ B ms model HR W J (allow_main Lm) top f n H) as (V1 & V2 & V3). repeat split; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition chk_cells (wr : bool) (top : Z) (e : saddr * list scell) : bool :=
  match sa_form F (fst e), exp_cells F (snd e) with
  | Some f, Some es =>
      let n := Z.of_nat (length es) in
      (0 <? n) &&& (n <? 1099511627776) &&& vis_any top (fst e) f n &&&
      match q_at f n with
      | Some (Rq, x) => (negb wr ||| rk_writable (rg_kind Rq)) &&& exp_ok ctasegs Rq x es
      | None => false
      end
  | _, _ => false
  end.

Lemma chk_cells_sound (wr : bool) (top : Z) (e : saddr * list scell) : chk_cells wr top e = true ->
  exists junks, cells_at ctasegs mM (den_addr Lm (fst e)) (den_cells Lm (snd e) junks)
    /\ (wr = true -> wr_at ctasegs mM (den_addr Lm (fst e)) (Z.of_nat (cells_size (den_cells Lm (snd e) junks)))).
Proof.
  unfold chk_cells. destruct (sa_form F (fst e)) as [f|] eqn:Ef; [|discriminate]. destruct (exp_cells F (snd e)) as [es|] eqn:Ee; [|discriminate].
  cbv zeta. intros H. apply land_true in H as [H Hq]. apply land_true in H as [H Hv]. apply land_true in H as [N1 N2].
  apply Z.ltb_lt in N1. apply Z.ltb_lt in N2.
  destruct (vis_any_sound top (fst e) f _ Ef Hv) as (V1 & V2 & V3).
  pose proof (sa_form_sound ρ F maps0 (A' ρ W J) (fst e) f Ef) as EA. fold Lm in EA.
  destruct (q_at f (Z.of_nat (length es))) as [[Rq x]|] eqn:Eq; [|discriminate Hq]. apply land_true in Hq as [Hk Hok].
  destruct (q_at_spec f (Z.of_nat (length es)) Rq x ltac:(lia) ltac:(rewrite EA; lia) Eq) as (Q1 & Q2 & Q3 & Q4).
  destruct (export_bytes_at ctasegs fs0 LIM ρ B ms model HR AFull Rq es x (den_addr Lm (fst e)) Q1 Q2 Q4 ltac:(rewrite <- EA; exact Q3) V3 Hok)
    as (bs & HF & Hb & Hw).
  destruct (exp_cells_sound ρ F maps0 (A' ρ W J) (snd e) es bs Ee HF) as (junks & C1 & C2). fold Lm in C1, C2.
  exists junks. split; [split; [exact C1 | rewrite C2; exact Hb]|].
  intros ->. cbn [negb] in Hk. cbv iota in Hk. pose proof (exp_cells_size ρ F maps0 (A' ρ W J) (snd e) es junks Ee C1) as ES. fold Lm in ES.
  rewrite <- ES. exact (Hw Hk).
Qed.

Definition chk_rw (top : Z) (e : saddr * list scell) : bool := chk_cells true top e.
Definition chk_ro (top : Z) (e : saddr * list scell) : bool := chk_cells false top e.

Theorem chk_rw_sound (top : Z) (e : saddr * list scell) : chk_rw top e = true -> rw_fact Lm mM e.
Proof.
  intros H. destruct (chk_cells_sound true top e H) as (junks & C & Wr). exists junks. split; [exact C | exact (Wr eq_refl)].
Qed.

Theorem chk_ro_sound (top : Z) (e : saddr * list scell) : chk_ro top e = true -> ro_fact Lm mM e.
Proof. intros H. destruct (chk_cells_sound false top e H) as (junks & C & _). exists junks. exact C. Qed.

Definition chk_zero (top : Z) (e : saddr * Z) : bool :=
  match sa_form F (fst e) with
  | Some f =>
      let n := snd e in
      (0 <? n) &&& (n <? 1099511627776) &&& vis_any top (fst e) f n &&&
      match q_at f n with
      | Some (Rq, x) => zero_ok Rq (to_Z x) n
                        ||| ((n <=? 65536) &&& rk_writable (rg_kind Rq) &&& exp_ok ctasegs Rq x (repeat (EL 0) (Z.to_nat n)))   (* [comment removed for export] *)
      | None => false
      end
  | None => false
  end.

Lemma all_EL0 (k : nat) (bs : list byte) : Forall2 (xbe_den ρ) (repeat (EL 0) k) bs -> bs = repeat (Z_to_bv 8 0) k.
Proof.
  revert bs. induction k as [|k IH]; intros bs H; cbn [repeat] in *; inversion H as [|? b ? bs' Hb Hr]; subst; [reflexivity|].
  cbn [xbe_den] in Hb. subst b. f_equal. exact (IH _ Hr).
Qed.

Theorem chk_zero_sound (top : Z) (e : saddr * Z) : chk_zero top e = true -> zero_fact Lm mM e.
Proof.
  unfold chk_zero. destruct (sa_form F (fst e)) as [f|] eqn:Ef; [|discriminate]. cbv zeta. intros H.
  apply land_true in H as [H Hq]. apply land_true in H as [H Hv]. apply land_true in H as [N1 N2]. apply Z.ltb_lt in N1. apply Z.ltb_lt in N2.
  destruct (vis_any_sound top (fst e) f _ Ef Hv) as (V1 & V2 & V3).
  pose proof (sa_form_sound ρ F maps0 (A' ρ W J) (fst e) f Ef) as EA. fold Lm in EA.
  destruct (q_at f (snd e)) as [[Rq x]|] eqn:Eq; [|discriminate Hq].
  destruct (q_at_spec f (snd e) Rq x ltac:(lia) ltac:(rewrite EA; lia) Eq) as (Q1 & Q2 & Q3 & Q4).
  apply lor_true in Hq as [Hq|Hq].
  - exact (export_zero ctasegs fs0 LIM ρ B ms model HR AFull Rq x (snd e) (den_addr Lm (fst e)) Q1 Q2 ltac:(lia) Q4 ltac:(rewrite <- EA; exact Q3) V3 Hq).
  - apply land_true in Hq as [Hq Hok]. apply land_true in Hq as [_ Hk].
    assert (EL' : Z.of_nat (length (repeat (EL 0) (Z.to_nat (snd e)))) = snd e) by (rewrite repeat_length, Z2Nat.id by lia; reflexivity).
    destruct (export_bytes_at ctasegs fs0 LIM ρ B ms model HR AFull Rq (repeat (EL 0) (Z.to_nat (snd e))) x (den_addr Lm (fst e)) Q1 Q2
                ltac:(rewrite EL'; exact Q4) ltac:(rewrite <- EA; exact Q3) ltac:(rewrite EL'; exact V3) Hok) as (bs & HF & Hb & Hw).
    rewrite (all_EL0 _ bs HF) in Hb. unfold zero_fact. split; [exact Hb|]. rewrite EL' in Hw. exact (Hw Hk).
Qed.

(* [comment removed for export] *)
Definition in_part (f : lin) (n : Z) : bool :=
  match lrange (a_facts B) f with
  | Some (lo, hi) => ((ls_beg <=? lo) &&& (hi + n <=? ls_end)) ||| ((hs_beg <=? lo) &&& (hi + n <=? hs_hi))
  | None => false
  end.

(* [comment removed for export] *)
Definition is_stackwin (e : saddr * saddr) : bool :=
  match e with (SAsh LB_ACEIL 0 0, SAsh LB_lit hi 0) => hi =? 140737488355328 | _ => false end.

Lemma stackwin_stk : stk ctasegs mM (shad (l_ACEIL Lm)) (shad (2 ^ 47)).
Proof.
  assert (EA : l_ACEIL Lm = l_sp0 Lm - 8388608) by reflexivity.
  assert (Hd : 17591916560384 <= l_ACEIL Lm / 8) by (apply Z.div_le_lower_bound; lia).
  assert (Hu : l_ACEIL Lm / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; [lia|]; change (8 * 2 ^ 44) with (2 ^ 47); lia).
  change (2 ^ 44) with 17592186044416 in Hu.
  apply (sh_stk ctasegs Hlow fs0 LIM ρ B ms model HR W J (allow_main Lm) HwL HwH).
  - intros z Hz. right. unfold shad, SHB, hs_beg, hs_hi in *. change (2 ^ 47 / 8) with 17592186044416 in Hz. lia.
  - intros z Hz.
    apply (vis_X ρ model W J (allow_main Lm) (pg_dn (shad (l_ACEIL Lm))) (pg_up (shad (2 ^ 47))) z (in_allow_main 3 _ eq_refl)
             (proj2 (pg_dn_spec _)) (proj2 (pg_up_spec _))).
    + destruct (pg_dn_spec (shad (l_ACEIL Lm))) as [D1 _]. destruct (pg_up_spec (shad (2 ^ 47))) as [U1 _]. lia.
    + unfold shad, SHB in *. change (2 ^ 47 / 8) with 17592186044416 in Hz. change (2 ^ 47) with 140737488355328. lia.
  - unfold shad, SHB. lia.
  - unfold shad, SHB. change (2 ^ 47 / 8) with 17592186044416. lia.
Qed.

Definition chk_stk1 (top : Z) (e : saddr * saddr) : bool :=
  match sa_form F (fst e), sa_form F (snd e) with
  | Some f, Some g =>
      let n := fst g - fst f in
      teqb (snd f) (snd g) &&& (0 <? n) &&& (n <? 1099511627776) &&& vis_any top (fst e) f n &&&
      (match q_at f n with Some (Rq, x) => rk_writable (rg_kind Rq) | None => false end ||| in_part f n)
  | _, _ => false
  end.

Definition chk_stk (top : Z) (e : saddr * saddr) : bool := chk_stk1 top e ||| is_stackwin e.

Lemma is_stackwin_sound (e : saddr * saddr) : is_stackwin e = true -> stk_fact Lm mM e.
Proof.
  intros H. unfold is_stackwin in H. destruct e as [[b off|b off sh] [b' off'|b' off' sh']]; try discriminate H;
    destruct b; try discriminate H; destruct off; try discriminate H; destruct sh; try discriminate H.
  destruct b'; try discriminate H. destruct sh'; try discriminate H. apply Z.eqb_eq in H. subst off'.
  unfold stk_fact. cbn [fst snd den_addr den_base]. rewrite !Z.add_0_r, Z.add_0_l. change 140737488355328 with (2 ^ 47). exact stackwin_stk.
Qed.

Theorem chk_stk_sound (top : Z) (e : saddr * saddr) : chk_stk top e = true -> stk_fact Lm mM e.
Proof.
  unfold chk_stk. intros H0. apply lor_true in H0 as [H0|H0]; [|exact (is_stackwin_sound e H0)]. revert H0.
  unfold chk_stk1. destruct (sa_form F (fst e)) as [f|] eqn:Ef; [|discriminate]. destruct (sa_form F (snd e)) as [g|] eqn:Eg; [|discriminate].
  cbv zeta. intros H. apply land_true in H as [H Hq]. apply land_true in H as [H Hv]. apply land_true in H as [H N2]. apply land_true in H as [Ht N1].
  apply teqb_eq in Ht. apply Z.ltb_lt in N1. apply Z.ltb_lt in N2.
  destruct (vis_any_sound top (fst e) f _ Ef Hv) as (V1 & V2 & V3).
  pose proof (sa_form_sound ρ F maps0 (A' ρ W J) (fst e) f Ef) as EA. pose proof (sa_form_sound ρ F maps0 (A' ρ W J) (snd e) g Eg) as EB.
  fold Lm in EA, EB.
  assert (Ehi : den_addr Lm (snd e) = den_addr Lm (fst e) + (fst g - fst f)).
  { rewrite <- EA, <- EB. destruct f as [cf tf]. destruct g as [cg tg]. unfold leval. cbn [fst snd] in *. subst tg. lia. }
  unfold stk_fact. rewrite Ehi.
  apply lor_true in Hq as [Hq|Hq].
  - destruct (q_at f (fst g - fst f)) as [[Rq x]|] eqn:Eq; [|discriminate Hq].
    destruct (q_at_spec f (fst g - fst f) Rq x ltac:(lia) ltac:(rewrite EA; lia) Eq) as (Q1 & Q2 & Q3 & Q4).
    assert (N0 : 0 <= fst g - fst f) by lia.
    exact (export_stk ctasegs fs0 LIM ρ B ms model HR AFull Rq x (fst g - fst f) (den_addr Lm (fst e)) Q1 Q2 N0 Q4 ltac:(rewrite <- EA; exact Q3) V3 Hq).
  - unfold in_part in Hq. destruct (lrange (a_facts B) f) as [[lo hi]|] eqn:El; [|discriminate Hq].
    pose proof (lrange_sound ρ _ _ Hsat _ El) as Xr. cbn [fst snd] in Xr. rewrite EA in Xr.
    apply (sh_stk ctasegs Hlow fs0 LIM ρ B ms model HR W J (allow_main Lm) HwL HwH); [|exact V3|lia|lia].
    intros z Hz. apply lor_true in Hq as [Hq|Hq]; apply land_true in Hq as [P1 P2]; apply Z.leb_le in P1; apply Z.leb_le in P2; [left | right]; lia.
Qed.

(* [comment removed for export] *)
Corollary chk_rw_all (top : Z) (l : list (saddr * list scell)) : forallb (chk_rw top) l = true -> Forall (rw_fact Lm mM) l.
Proof. intros H. apply Forall_forall. intros e He. rewrite forallb_forall in H. exact (chk_rw_sound top e (H e He)). Qed.
Corollary chk_ro_all (top : Z) (l : list (saddr * list scell)) : forallb (chk_ro top) l = true -> Forall (ro_fact Lm mM) l.
Proof. intros H. apply Forall_forall. intros e He. rewrite forallb_forall in H. exact (chk_ro_sound top e (H e He)). Qed.
Corollary chk_zero_all (top : Z) (l : list (saddr * Z)) : forallb (chk_zero top) l = true -> Forall (zero_fact Lm mM) l.
Proof. intros H. apply Forall_forall. intros e He. rewrite forallb_forall in H. exact (chk_zero_sound top e (H e He)). Qed.
Corollary chk_stk_all (top : Z) (l : list (saddr * saddr)) : forallb (chk_stk top) l = true -> Forall (stk_fact Lm mM) l.
Proof. intros H. apply Forall_forall. intros e He. rewrite forallb_forall in H. exact (chk_stk_sound top e (H e He)). Qed.

End Facts.
