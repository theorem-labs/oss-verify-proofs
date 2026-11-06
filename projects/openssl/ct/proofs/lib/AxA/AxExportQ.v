(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From OSSVerify.Proofs.openssl.ct.lib.AS Require Import AsanAcct.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Mem Frame RzCPS.
From OSSVerify.Proofs.openssl.ct.lib.VCommon Require Import FastWord.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import ExTrie ExBytes AxLazy AxLin AxVal AxBytes AxMem AxRng AxScan AxState AxSys AxModelRel.
From OSSVerify.Proofs.openssl.ct.lib.AxA Require Import AxExport.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

(* [comment removed for export] *)
Inductive xbe : Type :=
| EL (c : Z)                              (* [comment removed for export] *)
| EF (ts : terms) (o : w64) (j : nat)     (* [comment removed for export] *)
| EA.                                     (* [comment removed for export] *)

Definition xbe_ok (x : xb) (e : xbe) : bool :=
  match e with
  | EA => true
  | EL c => match x with BL c' => (to_Z c' =? c) | _ => false end
  | EF ts o j =>
      match x with
      | BF ts' o' j' => Nat.eqb j j' &&& w_eqb o o' &&& teqb ts ts'
      | BL c' => match ts with [] => (to_Z c' =? zbyte (wZ o) j) | _ => false end
      | BT => false
      end
  end.

Section ExportQ.
Variable segs : list Segment.
Variable fs0 : Fs.Fs.
Variable LIM : Z.
Variable ρ : valuation.
Variable B : AST.
Variable ms : machine_state.
Variable model : Model.
Hypothesis HR : R segs amodel (MR segs fs0 ρ) LIM ρ B (mkCfg ms model).
Variable A' : list (Z * Z).

Local Notation mX := (AxExport.mX ms model A').
Local Notation vis := (AxExport.vis model A').

Definition xbe_den (e : xbe) (b : byte) : Prop :=
  match e with
  | EL c => b = Z_to_bv 8 c
  | EF ts o j => bv_unsigned b = zbyte (smod ρ ts o) j
  | EA => True
  end.

Lemma xbe_ok_sound (x : xb) (e : xbe) (b : byte) : xbe_ok x e = true -> xb_bv ρ x b -> xbe_den e b.
Proof.
  destruct e as [c|ts o j|]; cbn [xbe_ok xbe_den]; [| |intros _ _; exact I].
  - destruct x as [c'| |]; try discriminate. intros H Hx. apply Z.eqb_eq in H. subst c. exact (xb_lit ρ c' b Hx).
  - destruct x as [c'| |ts' o' j']; try discriminate.
    + destruct ts; [|discriminate]. intros H Hx. apply Z.eqb_eq in H. unfold xb_bv in Hx. cbn [xb_z] in Hx. rewrite Hx, H.
      unfold smod. cbn [teval]. rewrite Z.add_0_l, Z.mod_small by apply wZ_range. reflexivity.
    + intros H Hx. apply land_true in H as [H H3]. apply land_true in H as [H1 H2].
      apply Nat.eqb_eq in H1. rewrite w_eqb_spec in H2. apply Z.eqb_eq in H2. apply wZ_inj in H2. apply teqb_eq in H3. subst.
      exact Hx.
Qed.

(* [comment removed for export] *)
Definition q_find (ts : terms) (o : w64) (n : int) : option (region * int) :=
  match find_reg (a_mem B) ts o n 0 with Some (_, Rq, x) => Some (Rq, x) | None => None end.

Lemma q_find_spec (ts : terms) (o : w64) (n : int) (Rq : region) (x : int) : 0 < to_Z n ->
  q_find ts o n = Some (Rq, x) ->
  In Rq (a_mem B) /\ is_entry Rq = false /\ smod ρ ts o = rbase ρ Rq + to_Z x /\ to_Z x + to_Z n <= to_Z (rg_n Rq).
Proof.
  unfold q_find. intros Hn H. destruct (find_reg (a_mem B) ts o n 0) as [[[i R0] x0]|] eqn:E; [|discriminate]. injection H as -> ->.
  destruct (find_reg_spec _ _ _ _ _ _ _ _ E) as (_ & Hnth & Hoff).
  pose proof (nth_error_In _ _ Hnth) as HIn.
  pose proof (r_mem _ _ _ _ _ _ _ HR) as [Hrok _]. cbn [cfg_ms] in Hrok.
  pose proof (regions_ok_in ρ _ Rq Hrok HIn) as Hwf.
  assert (Ha : bv_unsigned (wz (smod ρ ts o)) = smod ρ ts o) by (apply u_wz; apply smod_range).
  destruct (roff_addr ρ Rq ts o n x (wz (smod ρ ts o)) Hn Hwf Ha Hoff) as [A1 A2].
  split; [exact HIn|]. split; [exact (roff_ne _ _ _ _ _ Hoff)|]. split; [rewrite <- Ha; exact A1 | exact A2].
Qed.

Lemma region_bounds (Rq : region) : In Rq (a_mem B) -> 0 <= rbase ρ Rq /\ rbase ρ Rq + to_Z (rg_n Rq) <= 2 ^ 64 /\ to_Z (rg_n Rq) < 2 ^ 47.
Proof.
  intros HIn. pose proof (r_mem _ _ _ _ _ _ _ HR) as [Hrok _]. cbn [cfg_ms] in Hrok.
  destruct (regions_ok_in ρ _ Rq Hrok HIn) as (W1 & W2 & _). unfold rbase. pose proof (smod_range ρ (rg_ts Rq) (rg_bo Rq)) as S.
  unfold rbase, FastWord.two64 in *. repeat split; lia.
Qed.

(* [comment removed for export] *)
Fixpoint exp_ok (Rq : region) (x : int) (es : list xbe) : bool :=
  match es with
  | [] => true
  | e :: r => xbe_ok (rbyte segs Rq x) e &&& exp_ok Rq (x + 1)%uint63 r
  end.

Theorem export_exp (Rq : region) : In Rq (a_mem B) -> is_entry Rq = false ->
  forall (es : list xbe) (x : int), to_Z x + Z.of_nat (length es) <= to_Z (rg_n Rq) ->
  vis (rbase ρ Rq + to_Z x) (rbase ρ Rq + to_Z x + Z.of_nat (length es)) ->
  exp_ok Rq x es = true ->
  exists bs, Forall2 xbe_den es bs
    /\ (forall i, (i < length es)%nat -> Mem.mrd segs mX (wz (rbase ρ Rq + to_Z x + Z.of_nat i)) = nth_error bs i)
    /\ (rk_writable (rg_kind Rq) = true ->
        forall i, 0 <= i < Z.of_nat (length es) -> wview segs mX (wz (rbase ρ Rq + to_Z x + i)) <> None).
Proof.
  intros HIn He. destruct (region_bounds Rq HIn) as (B0 & B1 & B2).
  induction es as [|e r IH]; intros x Hfit Hvis Hok.
  - exists []. split; [constructor|]. split; [intros i Hi; cbn in Hi; lia | intros _ i Hi; cbn in Hi; lia].
  - cbn [exp_ok] in Hok. apply land_true in Hok as [Hok1 Hok2]. cbn [length] in Hfit, Hvis. rewrite Nat2Z.inj_succ in Hfit, Hvis.
    pose proof (to_Z_bounded x) as Bx.
    assert (Ex1 : to_Z (x + 1)%uint63 = to_Z x + 1) by (apply int_add_1; lia).
    assert (Hx0 : to_Z x < to_Z (rg_n Rq)) by lia.
    assert (Hv0 : RzCPS.HID A' model (wz (rbase ρ Rq + to_Z x)) = false) by (apply Hvis; lia).
    destruct (export_byte segs fs0 LIM ρ B ms model HR A' Rq x HIn He Hx0 Hv0) as [[b [Hb Hx]] Hw].
    destruct (IH (x + 1)%uint63 ltac:(lia) ltac:(intros z Hz; apply Hvis; lia) Hok2) as (bs & F & Hrd & Hwr).
    exists (b :: bs). split; [constructor; [exact (xbe_ok_sound _ _ _ Hok1 Hx) | exact F]|]. split.
    + intros i Hi. destruct i as [|i]; cbn [nth_error].
      * rewrite Z.add_0_r. exact Hb.
      * cbn [length] in Hi. rewrite <- (Hrd i ltac:(lia)). f_equal. f_equal. rewrite Ex1. lia.
    + intros Hk i Hi. destruct (Z.eq_dec i 0) as [->|Hi0]; [rewrite Z.add_0_r; exact (Hw Hk)|].
      replace (rbase ρ Rq + to_Z x + i) with (rbase ρ Rq + to_Z (x + 1)%uint63 + (i - 1)) by lia. apply (Hwr Hk). cbn [length] in Hi. lia.
Qed.

(* [comment removed for export] *)
Corollary export_bytes_at (Rq : region) (es : list xbe) (x : int) (A : Z) : In Rq (a_mem B) -> is_entry Rq = false ->
  to_Z x + Z.of_nat (length es) <= to_Z (rg_n Rq) -> A = rbase ρ Rq + to_Z x -> vis A (A + Z.of_nat (length es)) ->
  exp_ok Rq x es = true ->
  exists bs, Forall2 xbe_den es bs /\ Mem.bytes_at segs mX A bs
    /\ (rk_writable (rg_kind Rq) = true -> Mem.wr_at segs mX A (Z.of_nat (length es))).
Proof.
  intros HIn He Hfit -> Hvis Hok. destruct (region_bounds Rq HIn) as (B0 & B1 & B2). pose proof (to_Z_bounded x) as Bx.
  destruct (export_exp Rq HIn He es x Hfit Hvis Hok) as (bs & F & Hrd & Hwr). exists bs. split; [exact F|].
  pose proof (Forall2_length F) as HL. split.
  - unfold Mem.bytes_at. split; [lia|]. split; [rewrite <- HL; lia|]. intros i Hi. rewrite <- HL in Hi. exact (Hrd i Hi).
  - intros Hk. unfold Mem.wr_at. split; [lia|]. split; [lia|]. intros i Hi. exact (Hwr Hk i Hi).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition zero_ok (Rq : region) (x n : Z) : bool :=
  match rg_kind Rq with
  | KZero | KShadow => rng_all (fun _ c => cell_is0 c) (rg_d Rq) (rg_cells Rq) (x / 8) ((x + n - 1) / 8)
  | _ => false
  end.

Lemma zero_ok_byte (Rq : region) (x n : Z) (y : int) : In Rq (a_mem B) -> zero_ok Rq x n = true ->
  x <= to_Z y < x + n -> to_Z y < to_Z (rg_n Rq) -> rbyte segs Rq y = BL 0%uint63.
Proof.
  intros HIn H Hy Hn. pose proof (r_mem _ _ _ _ _ _ _ HR) as [Hrok _]. cbn [cfg_ms] in Hrok.
  destruct (regions_ok_in ρ _ Rq Hrok HIn) as (_ & _ & W3 & _).
  unfold zero_ok in H. unfold rbyte, get_cell_opt.
  destruct (iget (rg_d Rq) (rg_cells Rq) (y >> 3)%uint63) as [c|] eqn:Eg.
  - assert (Hc : cell_is0 c = true).
    { destruct (rg_kind Rq); try discriminate H;
        refine (rng_all_iget (fun _ c => cell_is0 c) _ _ _ _ (y >> 3)%uint63 c H _ (key_small Rq y W3 Hn) Eg);
        rewrite phi_lsr3; split; apply Z.div_le_mono; lia. }
    apply (cell_is0_byte c _ Hc). apply i2n_lt8.
  - destruct (rg_kind Rq); try discriminate H; reflexivity.
Qed.

Theorem export_zero (Rq : region) (x : int) (n : Z) (A : Z) : In Rq (a_mem B) -> is_entry Rq = false -> 0 <= n ->
  to_Z x + n <= to_Z (rg_n Rq) -> A = rbase ρ Rq + to_Z x -> vis A (A + n) -> zero_ok Rq (to_Z x) n = true ->
  Mem.bytes_at segs mX A (repeat (Z_to_bv 8 0) (Z.to_nat n)) /\ Mem.wr_at segs mX A n.
Proof.
  intros HIn He Hn0 Hfit -> Hvis Hok. destruct (region_bounds Rq HIn) as (B0 & B1 & B2). pose proof (to_Z_bounded x) as Bx.
  assert (Hkw : rk_writable (rg_kind Rq) = true) by (unfold zero_ok in Hok; destruct (rg_kind Rq); try discriminate Hok; reflexivity).
  assert (Hbyte : forall i, 0 <= i < n ->
            Mem.mrd segs mX (wz (rbase ρ Rq + to_Z x + i)) = Some (Z_to_bv 8 0) /\ wview segs mX (wz (rbase ρ Rq + to_Z x + i)) <> None).
  { intros i Hi. set (y := of_Z (to_Z x + i)).
    assert (Ey : to_Z y = to_Z x + i) by (unfold y; apply phi_of_Z_small; lia).
    destruct (export_byte segs fs0 LIM ρ B ms model HR A' Rq y HIn He ltac:(lia) ltac:(rewrite Ey, Z.add_assoc; apply Hvis; lia)) as [[b [Hb Hx]] Hw].
    rewrite (zero_ok_byte Rq (to_Z x) n y HIn Hok ltac:(lia) ltac:(lia)) in Hx. rewrite (xb_lit ρ _ b Hx) in Hb.
    rewrite Ey, Z.add_assoc in Hb, Hw. split; [exact Hb | exact (Hw Hkw)]. }
  split.
  - unfold Mem.bytes_at. rewrite repeat_length, Z2Nat.id by lia. split; [lia|]. split; [lia|]. intros i Hi.
    change (Mem.wa (rbase ρ Rq + to_Z x + Z.of_nat i)) with (wz (rbase ρ Rq + to_Z x + Z.of_nat i)).
    rewrite (proj1 (Hbyte (Z.of_nat i) ltac:(lia))). symmetry. apply nth_error_repeat. exact Hi.
  - unfold Mem.wr_at. split; [lia|]. split; [lia|]. intros i Hi. exact (proj2 (Hbyte i Hi)).
Qed.

(* [comment removed for export] *)
Theorem export_stk (Rq : region) (x : int) (n : Z) (A : Z) : In Rq (a_mem B) -> is_entry Rq = false -> 0 <= n ->
  to_Z x + n <= to_Z (rg_n Rq) -> A = rbase ρ Rq + to_Z x -> vis A (A + n) -> rk_writable (rg_kind Rq) = true ->
  Frame.stk segs mX A (A + n).
Proof.
  intros HIn He Hn0 Hfit -> Hvis Hkw. destruct (region_bounds Rq HIn) as (B0 & B1 & B2). pose proof (to_Z_bounded x) as Bx.
  unfold Frame.stk. split; [lia|]. split; [lia|]. intros a Ha. set (y := of_Z (a - rbase ρ Rq)).
  assert (Ey : to_Z y = a - rbase ρ Rq) by (unfold y; apply phi_of_Z_small; lia).
  destruct (export_byte segs fs0 LIM ρ B ms model HR A' Rq y HIn He ltac:(lia) ltac:(rewrite Ey; replace (rbase ρ Rq + (a - rbase ρ Rq)) with a by lia; apply Hvis; lia)) as [[b [Hb _]] Hw].
  rewrite Ey in Hb, Hw. replace (rbase ρ Rq + (a - rbase ρ Rq)) with a in Hb, Hw by lia.
  split; [exact (Hw Hkw) | exists b; exact Hb].
Qed.

End ExportQ.
