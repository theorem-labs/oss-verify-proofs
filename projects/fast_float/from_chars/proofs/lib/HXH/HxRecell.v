(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxMem FxFold FxRgs FxFacts FxImg FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFold OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame.
From OSSVerify.Proofs.fast_float.from_chars.lib.HXH Require Import HxRebyte.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition bv8c (l : lin) : list bval := List.map (fun j => BV l (Z.of_nat j)) (seq 0 8).
Definition put8_rg (o : Z) (l : lin) (R : region) : region := RG (rg_base R) (rg_size R) (rg_kind R) (put_bytes (rg_cont R) o (bv8c l)).
(* [comment removed for export] *)
Definition decl (k : Z) (n : positive) : lin := ladd (lscale (2 ^ k) (lvar n)) (lvar (Pos.succ n)).

Definition cell_in (R : region) (o : Z) : bool :=
  (Z.leb 0 o && match is_const (rg_size R) with Some z => Z.leb (o + 8) z | None => false end)%bool.

Definition hx_dec (i : nat) (o k : Z) (S : sst) : option sst :=
  match nth_error (s_rgs S) i with
  | Some R =>
      let n := s_next S in
      let K := SST (s_pc S) (s_regs S) (upd_nth (s_rgs S) i (put8_rg o (decl k n) R))
                   (FRange (lvar (Pos.succ n)) 0 (2 ^ k - 1) :: FRange (lvar n) 0 (2 ^ (64 - k) - 1) :: s_facts S)
                   (Pos.succ (Pos.succ n)) (s_resv S) in
      if (cell_in R o && Z.ltb 0 k && Z.ltb k 64 && state_wf S && state_wf K)%bool then Some K else None
  | None => None
  end.

Definition hx_trk (i : nat) (o : Z) (S : sst) : option sst :=
  match nth_error (s_rgs S) i with
  | Some R =>
      let n := s_next S in
      let K := SST (s_pc S) (s_regs S) (upd_nth (s_rgs S) i (put8_rg o (lvar n) R)) (s_facts S) (Pos.succ n) (s_resv S) in
      if (cell_in R o && state_wf S && state_wf K)%bool then Some K else None
  | None => None
  end.

(* [comment removed for export] *)
Definition cell_lin (c : tree bval) (o : Z) : option lin :=
  match tget (okey o) c with
  | Some (BV l 0) => if forallb (fun j => match tget (okey (o + Z.of_nat j)) c with
                                          | Some (BV l' j') => (lin_eqb l' l && Z.eqb j' (Z.of_nat j))%bool
                                          | _ => false end) (seq 0 8)
                     then Some l else None
  | _ => None
  end.
Definition hx_repl (i : nat) (o : Z) (l' : lin) (S : sst) : option sst :=
  match nth_error (s_rgs S) i with
  | Some R =>
      match cell_lin (rg_cont R) o with
      | Some l =>
          let K := SST (s_pc S) (s_regs S) (upd_nth (s_rgs S) i (put8_rg o l' R)) (s_facts S) (s_next S) (s_resv S) in
          if (cell_in R o && fact_implied (s_facts S) (FRange (lsub l l') 0 0) && state_wf K)%bool then Some K else None
      | None => None
      end
  | None => None
  end.

Definition all_bk0t (c : tree bval) : bool := tforall (fun _ v => match v with BK z => Z.eqb z 0 | _ => false end) c.
Definition hx_unz (i : nat) (S : sst) : option sst :=
  match nth_error (s_rgs S) i with
  | Some R => match rg_kind R with
              | RZ => if all_bk0t (rg_cont R)
                      then Some (SST (s_pc S) (s_regs S) (upd_nth (s_rgs S) i (RG (rg_base R) (rg_size R) RZ TEmpty)) (s_facts S) (s_next S) (s_resv S))
                      else None
              | _ => None
              end
  | None => None
  end.

(* [comment removed for export] *)
Definition all_bk0n (c : tree bval) (n : Z) : bool :=
  forallb (fun j => match tget (okey (Z.of_nat j)) c with Some (BK 0) => true | _ => false end) (seq 0 (Z.to_nat n)).
Definition hx_promz (i : nat) (S : sst) : option sst :=
  match nth_error (s_rgs S) i with
  | Some R => match rg_kind R, is_const (rg_size R) with
              | RW, Some n => if (Z.leb 0 n && Z.leb n 65536 && all_bk0n (rg_cont R) n)%bool
                              then Some (SST (s_pc S) (s_regs S) (upd_nth (s_rgs S) i (RG (rg_base R) (rg_size R) RZ TEmpty)) (s_facts S) (s_next S) (s_resv S))
                              else None
              | _, _ => None
              end
  | None => None
  end.

(* [comment removed for export] *)
Definition PSK : positive := 40.
Definition hx_psr (l : lin) (S : sst) : option sst :=
  Some (SST (s_pc S) (rset (s_regs S) PSK l) (s_rgs S) (s_facts S) (s_next S) (s_resv S)).

Section Cell.
Variable segs : list Segment.

#[using="Type"] Lemma nth_bv8c : forall l j, (j < 8)%nat -> nth_error (bv8c l) j = Some (BV l (Z.of_nat j)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros l j Hj. unfold bv8c. rewrite nth_error_map, nth_error_seq by lia. cbn [Nat.add].
  rewrite (proj2 (Nat.ltb_lt _ _)) by lia. reflexivity.
Qed.
#[using="Type"] Lemma len_bv8c : forall l, length (bv8c l) = 8%nat.
Proof. LiaFast.lf_pins LiaFast.u0. intros l. unfold bv8c. rewrite length_map, length_seq. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rg_rd1 : forall E m R i, rg_ok segs E m R -> 0 <= i < rsz E R ->
  exists b, rd1 segs m (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + i)) = Some b.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m R i (H1 & H2 & H3 & H4) Hi. pose proof (H3 i Hi) as X.
  destruct (rd1 segs m (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + i))) as [b|] eqn:Hb; [exists b; reflexivity|exfalso].
  destruct (rg_kind R).
  - exact (proj1 X eq_refl).
  - destruct X as [X1 X2]. unfold rd1 in Hb. rewrite X1 in Hb. exact (X2 Hb).
  - exact (proj1 (proj1 X) eq_refl).
  - exact (proj1 (proj1 X) eq_refl).
  - exact (X eq_refl).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma put8_rg_ok : forall E m R o l z, 0 <= o -> is_const (rg_size R) = Some z -> o + 8 <= z -> rg_ok segs E m R ->
  (forall j, 0 <= j < 8 -> rd1 segs m (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + (o + j))) = Some (bden E (BV l j))) ->
  rg_ok segs E m (put8_rg o l R).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m R o l z Ho Hzc Hsz HR Hb. pose proof HR as (H1 & H2 & H3 & H4).
  unfold put8_rg, rg_ok. cbn [rg_base rg_size rg_kind rg_cont]. unfold rsz in *. cbn [rg_size rg_base] in *.
  assert (Hrz : bv_unsigned (lden E (rg_size R)) = z) by exact (is_const_u E (rg_size R) z Hzc).
  assert (Hin : forall p, (Z.leb o (Zpos p - 1) && Z.ltb (Zpos p - 1) (o + Z.of_nat (length (bv8c l))))%bool = true ->
             nth_error (bv8c l) (Z.to_nat (Zpos p - 1 - o)) = Some (BV l (Zpos p - 1 - o)) /\ 0 <= Zpos p - 1 - o < 8).
  { intros p Hp. apply andb_prop in Hp as [Hp1 Hp2]. apply Z.leb_le in Hp1. apply Z.ltb_lt in Hp2. rewrite len_bv8c in Hp2.
    split; [|lia]. rewrite nth_bv8c by lia. rewrite Z2Nat.id by lia. reflexivity. }
  split; [exact H1|]. split; [exact H2|]. split.
  - intros i Hi. pose proof (H3 i Hi) as X. destruct (rg_kind R); try exact X.
    + destruct X as [X1 X2]. split; [exact X1|]. intros Hnone. apply X2. rewrite put_bytes_spec in Hnone by exact Ho.
      destruct (Z.leb o (Zpos (okey i) - 1) && Z.ltb (Zpos (okey i) - 1) (o + Z.of_nat (length (bv8c l))))%bool eqn:Hp.
      * destruct (Hin _ Hp) as (Y & _). rewrite Y in Hnone. discriminate.
      * exact Hnone.
    + destruct X as [X1 X2]. split; [exact X1|]. intros Hnone. apply X2. rewrite put_bytes_spec in Hnone by exact Ho.
      destruct (Z.leb o (Zpos (okey i) - 1) && Z.ltb (Zpos (okey i) - 1) (o + Z.of_nat (length (bv8c l))))%bool eqn:Hp.
      * destruct (Hin _ Hp) as (Y & _). rewrite Y in Hnone. discriminate.
      * exact Hnone.
  - intros p v Hp. rewrite put_bytes_spec in Hp by exact Ho.
    destruct (Z.leb o (Zpos p - 1) && Z.ltb (Zpos p - 1) (o + Z.of_nat (length (bv8c l))))%bool eqn:Hq.
    + destruct (Hin _ Hq) as (Y1 & Y2). rewrite Y1 in Hp. injection Hp as <-.
      split; [rewrite Hrz; lia|]. rewrite <- (Hb (Zpos p - 1 - o) Y2). f_equal. f_equal. lia.
    + exact (H4 p v Hp).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma cell_bytes : forall E m R o z, 0 <= o -> is_const (rg_size R) = Some z -> o + 8 <= z -> rg_ok segs E m R ->
  exists bs, length bs = 8%nat /\ Forall (fun b => 0 <= b < 256) bs /\
    forall j, (j < 8)%nat -> rd1 segs m (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + (o + Z.of_nat j))) = Some (Z_to_bv 8 (nth j bs 0)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m R o z Ho Hzc Hsz HR.
  assert (Hrz : rsz E R = z) by (unfold rsz; exact (is_const_u E (rg_size R) z Hzc)).
  assert (Hx : forall j, (j < 8)%nat -> exists b, 0 <= b < 256 /\
             rd1 segs m (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + (o + Z.of_nat j))) = Some (Z_to_bv 8 b)).
  { intros j Hj. destruct (rg_rd1 E m R (o + Z.of_nat j) HR ltac:(rewrite Hrz; lia)) as [b Hb].
    exists (bv_unsigned b). split; [pose proof (bv_unsigned_in_range 8 b) as X; change (bv_modulus 8) with 256 in X; lia|].
    rewrite Hb. f_equal. symmetry. apply Z_to_bv_bv_unsigned. }
  destruct (Hx 0%nat ltac:(lia)) as (b0 & B0 & R0). destruct (Hx 1%nat ltac:(lia)) as (b1 & B1 & R1).
  destruct (Hx 2%nat ltac:(lia)) as (b2 & B2 & R2). destruct (Hx 3%nat ltac:(lia)) as (b3 & B3 & R3).
  destruct (Hx 4%nat ltac:(lia)) as (b4 & B4 & R4). destruct (Hx 5%nat ltac:(lia)) as (b5 & B5 & R5).
  destruct (Hx 6%nat ltac:(lia)) as (b6 & B6 & R6). destruct (Hx 7%nat ltac:(lia)) as (b7 & B7 & R7).
  exists [b0; b1; b2; b3; b4; b5; b6; b7]. split; [reflexivity|]. split; [repeat (apply Forall_cons; [assumption|]); apply Forall_nil|].
  intros j Hj. do 8 (destruct j as [|j]; [assumption|]). lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma bden_cval : forall E l bs j, length bs = 8%nat -> Forall (fun b => 0 <= b < 256) bs -> bv_unsigned (lden E l) = cval bs ->
  (j < 8)%nat -> bden E (BV l (Z.of_nat j)) = Z_to_bv 8 (nth j bs 0).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E l bs j Hlen Hbs Hv Hj. cbn [bden]. rewrite Hv. apply bv_eq. rewrite !Z_to_bv_unsigned.
  unfold bv_wrap. change (bv_modulus 8) with 256.
  pose proof (cval_byte bs j Hbs ltac:(lia)) as CB. rewrite CB.
  assert (Hnb : 0 <= nth j bs 0 < 256) by (rewrite Forall_forall in Hbs; apply Hbs; apply nth_In; lia).
  symmetry. apply Z.mod_small. exact Hnb.
Qed.
#[using="Type"] Lemma cval8_bound : forall bs, length bs = 8%nat -> Forall (fun b => 0 <= b < 256) bs -> 0 <= cval bs < two64.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros bs Hlen Hbs. pose proof (cval_bound bs Hbs) as X. rewrite Hlen in X. change (256 ^ Z.of_nat 8) with 18446744073709551616 in X.
  unfold two64. lia.
Qed.
End Cell.

Section CellRule.
Variable segs : list Segment.

Definition updv (E : valu) (x : positive) (v : word) : valu := fun y => if Pos.eqb y x then v else E y.
#[using="Type"] Lemma updv_agree : forall E n x v, (n <= x)%positive -> agree n E (updv E x v).
Proof. LiaFast.lf_pins LiaFast.u0. intros E n x v Hx y Hy. unfold updv. destruct (Pos.eqb y x) eqn:Q; [apply Pos.eqb_eq in Q; lia | reflexivity]. Qed.
#[using="Type"] Lemma agree_trans' : forall n E1 E2 E3, agree n E1 E2 -> agree n E2 E3 -> agree n E1 E3.
Proof. LiaFast.lf_pins LiaFast.u0. intros n E1 E2 E3 H1 H2 x Hx. rewrite (H1 x Hx). exact (H2 x Hx). Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma cell_sden0 : forall S i R o l z E E2 ms facts' n',
  nth_error (s_rgs S) i = Some R -> 0 <= o -> is_const (rg_size R) = Some z -> o + 8 <= z ->
  state_wf S = true -> agree (s_next S) E E2 -> sden0 segs E S ms ->
  (forall j, 0 <= j < 8 -> rd1 segs (ms_mem ms) (Z_to_bv 64 (bv_unsigned (lden E2 (rg_base R)) + (o + j))) = Some (bden E2 (BV l j))) ->
  Forall (fact_ok E2) facts' ->
  sden0 segs E2 (SST (s_pc S) (s_regs S) (upd_nth (s_rgs S) i (put8_rg o l R)) (facts' ++ s_facts S) n' (s_resv S)) ms.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros S i R o l z E E2 ms facts' n' Hn Ho Hzc Hsz Hw Ha Hd Hb Hf'.
  pose proof (sden0_agree segs S E E2 ms Hw Ha Hd) as (Hpc0 & Hsvc0 & Hresv0 & HR0 & HG0 & HD0 & HF0 & Hfrm0).
  unfold sden0. cbn [s_pc s_regs s_rgs s_facts s_resv s_next].
  refine (conj Hpc0 (conj Hsvc0 (conj Hresv0 (conj HR0 (conj _ (conj _ (conj _ Hfrm0))))))).
  - apply (upd_nth_forall (rg_ok segs E2 (ms_mem ms)) (s_rgs S) i R (put8_rg o l R) Hn); [|exact HG0].
    rewrite Forall_forall in HG0. exact (put8_rg_ok segs E2 (ms_mem ms) R o l z Ho Hzc Hsz (HG0 R (nth_error_In _ _ Hn)) Hb).
  - exact (rgs_disj_upd E2 (s_rgs S) i (put8_rg o l R) R Hn eq_refl eq_refl HD0).
  - apply Forall_app. split; [exact Hf' | exact HF0].
Qed.

#[using="Type"] Theorem hx_dec_ok : forall i o k S K, hx_dec i o k S = Some K ->
  hcall_rule0 segs S K /\ (s_next S <= s_next K)%positive /\ shape (s_rgs K) = shape (s_rgs S).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros i o k S K H. unfold hx_dec in H.
  destruct (nth_error (s_rgs S) i) as [R|] eqn:Hn; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end. injection H as <-.
  apply andb_prop in Hc as [Hc HwK]. apply andb_prop in Hc as [Hc HwS]. apply andb_prop in Hc as [Hc Hk64].
  apply andb_prop in Hc as [Hci Hk0]. apply Z.ltb_lt in Hk0, Hk64.
  unfold cell_in in Hci. apply andb_prop in Hci as [Ho Hsz]. apply Z.leb_le in Ho.
  destruct (is_const (rg_size R)) as [z|] eqn:Hzc; [|discriminate]. apply Z.leb_le in Hsz.
  split; [|split; [cbn [s_next]; lia | cbn [s_rgs]; exact (shape_upd_rg _ i R (put8_rg o _ R) Hn eq_refl eq_refl)]].
  intros E ms Hd. pose proof (sden_0 _ _ _ _ Hd) as Hd0.
  pose proof Hd0 as (_ & _ & _ & _ & HG0 & _). rewrite Forall_forall in HG0. pose proof (HG0 R (nth_error_In _ _ Hn)) as HR.
  destruct (cell_bytes segs E (ms_mem ms) R o z Ho Hzc Hsz HR) as (bs & Hlen & Hbs & Hrd).
  pose proof (cval8_bound bs Hlen Hbs) as Hv. set (v := cval bs) in *.
  set (n := s_next S) in *.
  set (E1 := updv E n (Z_to_bv 64 (v / 2 ^ k))). set (E2 := updv E1 (Pos.succ n) (Z_to_bv 64 (v mod 2 ^ k))).
  assert (Ha : agree n E E2).
  { apply (agree_trans' n E E1 E2); [apply updv_agree; lia | apply updv_agree; lia]. }
  assert (Hpk : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  assert (Hq : 0 <= v / 2 ^ k < 2 ^ (64 - k)).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. rewrite <- Z.pow_add_r by lia.
    replace (k + (64 - k)) with 64 by lia. change (2 ^ 64) with two64. lia. }
  assert (Hq64 : 2 ^ (64 - k) <= two64).
  { assert (X : 2 ^ (64 - k) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia). change (2 ^ 64) with two64 in X. exact X. }
  assert (Hr : 0 <= v mod 2 ^ k < 2 ^ k) by (apply Z.mod_pos_bound; lia).
  assert (Hk64' : 2 ^ k <= two64).
  { assert (X : 2 ^ k <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia). change (2 ^ 64) with two64 in X. exact X. }
  assert (HX : bv_unsigned (E2 n) = v / 2 ^ k).
  { unfold E2, E1, updv. replace (Pos.eqb n (Pos.succ n)) with false by (symmetry; apply Pos.eqb_neq; lia). rewrite Pos.eqb_refl.
    rewrite u_Z_to_bv. apply Z.mod_small. lia. }
  assert (HY : bv_unsigned (E2 (Pos.succ n)) = v mod 2 ^ k).
  { unfold E2, updv. rewrite Pos.eqb_refl. rewrite u_Z_to_bv. apply Z.mod_small. lia. }
  assert (Hl : bv_unsigned (lden E2 (decl k n)) = v).
  { unfold decl. rewrite lden_ladd, lden_lscale, !lden_lvar. rewrite bv_add_unsigned. unfold bv_wrap. change (bv_modulus 64) with two64.
    rewrite u_Z_to_bv, HX, HY. rewrite (Z.mod_small (2 ^ k * (v / 2 ^ k))).
    - rewrite <- (Z.div_mod v (2 ^ k)) by lia. apply Z.mod_small. exact Hv.
    - pose proof (Z.div_mod v (2 ^ k) ltac:(lia)) as DM. split; [apply Z.mul_nonneg_nonneg; lia | lia]. }
  exists ms, E2. split; [apply ist_refl|]. split; [|split; [exact Ha | intros x _; reflexivity]].
  apply (sden0_sden segs _ E2 ms HwK).
  change (FRange (lvar (Pos.succ n)) 0 (2 ^ k - 1) :: FRange (lvar n) 0 (2 ^ (64 - k) - 1) :: s_facts S)
    with ([FRange (lvar (Pos.succ n)) 0 (2 ^ k - 1); FRange (lvar n) 0 (2 ^ (64 - k) - 1)] ++ s_facts S).
  apply (cell_sden0 S i R o (decl k n) z E E2 ms _ _ Hn Ho Hzc Hsz HwS Ha Hd0).
  - intros j Hj. assert (Hbase : lden E2 (rg_base R) = lden E (rg_base R)).
    { symmetry. apply (lden_agree n); [|exact Ha]. unfold state_wf in HwS. apply andb_prop in HwS as [HwS _]. apply andb_prop in HwS as [HwS _].
      apply andb_prop in HwS as [_ Hwg]. rewrite forallb_forall in Hwg. pose proof (Hwg R (nth_error_In _ _ Hn)) as X.
      unfold rwf in X. repeat (apply andb_prop in X as [X ?]). assumption. }
    rewrite Hbase. replace j with (Z.of_nat (Z.to_nat j)) by lia. rewrite (Hrd (Z.to_nat j) ltac:(lia)).
    f_equal. symmetry. exact (bden_cval E2 (decl k n) bs (Z.to_nat j) Hlen Hbs Hl ltac:(lia)).
  - constructor; [|constructor; [|constructor]]; cbn [fact_ok]; rewrite lden_lvar; [rewrite HY | rewrite HX]; lia.
Qed.

#[using="Type"] Theorem hx_trk_ok : forall i o S K, hx_trk i o S = Some K ->
  hcall_rule0 segs S K /\ (s_next S <= s_next K)%positive /\ shape (s_rgs K) = shape (s_rgs S).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros i o S K H. unfold hx_trk in H.
  destruct (nth_error (s_rgs S) i) as [R|] eqn:Hn; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end. injection H as <-.
  apply andb_prop in Hc as [Hc HwK]. apply andb_prop in Hc as [Hci HwS].
  unfold cell_in in Hci. apply andb_prop in Hci as [Ho Hsz]. apply Z.leb_le in Ho.
  destruct (is_const (rg_size R)) as [z|] eqn:Hzc; [|discriminate]. apply Z.leb_le in Hsz.
  split; [|split; [cbn [s_next]; lia | cbn [s_rgs]; exact (shape_upd_rg _ i R (put8_rg o _ R) Hn eq_refl eq_refl)]].
  intros E ms Hd. pose proof (sden_0 _ _ _ _ Hd) as Hd0.
  pose proof Hd0 as (_ & _ & _ & _ & HG0 & _). rewrite Forall_forall in HG0. pose proof (HG0 R (nth_error_In _ _ Hn)) as HR.
  destruct (cell_bytes segs E (ms_mem ms) R o z Ho Hzc Hsz HR) as (bs & Hlen & Hbs & Hrd).
  pose proof (cval8_bound bs Hlen Hbs) as Hv. set (v := cval bs) in *.
  set (n := s_next S) in *. set (E2 := updv E n (Z_to_bv 64 v)).
  assert (Ha : agree n E E2) by (apply updv_agree; lia).
  assert (Hl : bv_unsigned (lden E2 (lvar n)) = v).
  { rewrite lden_lvar. unfold E2, updv. rewrite Pos.eqb_refl. rewrite u_Z_to_bv. apply Z.mod_small. exact Hv. }
  exists ms, E2. split; [apply ist_refl|]. split; [|split; [exact Ha | intros x _; reflexivity]].
  apply (sden0_sden segs _ E2 ms HwK).
  change (s_facts S) with ([] ++ s_facts S).
  apply (cell_sden0 S i R o (lvar n) z E E2 ms [] _ Hn Ho Hzc Hsz HwS Ha Hd0); [|constructor].
  intros j Hj. assert (Hbase : lden E2 (rg_base R) = lden E (rg_base R)).
  { symmetry. apply (lden_agree n); [|exact Ha]. unfold state_wf in HwS. apply andb_prop in HwS as [HwS _]. apply andb_prop in HwS as [HwS _].
    apply andb_prop in HwS as [_ Hwg]. rewrite forallb_forall in Hwg. pose proof (Hwg R (nth_error_In _ _ Hn)) as X.
    unfold rwf in X. repeat (apply andb_prop in X as [X ?]). assumption. }
  rewrite Hbase. replace j with (Z.of_nat (Z.to_nat j)) by lia. rewrite (Hrd (Z.to_nat j) ltac:(lia)).
  f_equal. symmetry. exact (bden_cval E2 (lvar n) bs (Z.to_nat j) Hlen Hbs Hl ltac:(lia)).
Qed.

#[using="Type"] Lemma cell_lin_spec : forall c o l, cell_lin c o = Some l -> forall j, (j < 8)%nat -> tget (okey (o + Z.of_nat j)) c = Some (BV l (Z.of_nat j)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros c o l H j Hj. unfold cell_lin in H.
  destruct (tget (okey o) c) as [[b|l0 j0]|]; try discriminate. destruct j0; try discriminate.
  match type of H with (if ?x then _ else _) = _ => destruct x eqn:Hf; [|discriminate] end. injection H as ->.
  rewrite forallb_forall in Hf. pose proof (Hf j ltac:(apply in_seq; lia)) as X.
  destruct (tget (okey (o + Z.of_nat j)) c) as [[b|l' j']|]; try discriminate.
  apply andb_prop in X as [X1 X2]. apply lin_eqb_eq in X1. apply Z.eqb_eq in X2. subst. reflexivity.
Qed.

#[using="Type"] Theorem hx_repl_ok : forall i o l' S K, hx_repl i o l' S = Some K ->
  hcall_rule0 segs S K /\ (s_next S <= s_next K)%positive /\ shape (s_rgs K) = shape (s_rgs S).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros i o l' S K H. unfold hx_repl in H.
  destruct (nth_error (s_rgs S) i) as [R|] eqn:Hn; [|discriminate].
  destruct (cell_lin (rg_cont R) o) as [l|] eqn:Hcl; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end. injection H as <-.
  apply andb_prop in Hc as [Hc HwK]. apply andb_prop in Hc as [Hci Himp].
  unfold cell_in in Hci. apply andb_prop in Hci as [Ho Hsz]. apply Z.leb_le in Ho.
  destruct (is_const (rg_size R)) as [z|] eqn:Hzc; [|discriminate]. apply Z.leb_le in Hsz.
  split; [|split; [cbn [s_next]; lia | cbn [s_rgs]; exact (shape_upd_rg _ i R (put8_rg o _ R) Hn eq_refl eq_refl)]].
  intros E ms Hd. exists ms, E. split; [apply ist_refl|]. split; [|split; [intros x Hx; reflexivity | intros x _; reflexivity]].
  apply (sden0_sden segs _ E ms HwK).
  pose proof (sden_0 _ _ _ _ Hd) as (Hpc0 & Hsvc0 & Hresv0 & HR0 & HG0 & HD0 & HF0 & Hfrm0).
  unfold sden0. cbn [s_pc s_regs s_rgs s_facts s_resv s_next].
  refine (conj Hpc0 (conj Hsvc0 (conj Hresv0 (conj HR0 (conj _ (conj _ (conj HF0 Hfrm0))))))).
  - apply (upd_nth_forall (rg_ok segs E (ms_mem ms)) (s_rgs S) i R (put8_rg o l' R) Hn); [|exact HG0].
    rewrite Forall_forall in HG0. pose proof (HG0 R (nth_error_In _ _ Hn)) as HR.
    apply (put8_rg_ok segs E (ms_mem ms) R o l' z Ho Hzc Hsz HR).
    intros j Hj. pose proof HR as (_ & _ & _ & H4).
    pose proof (cell_lin_spec _ _ _ Hcl (Z.to_nat j) ltac:(lia)) as Ht. rewrite Z2Nat.id in Ht by lia.
    destruct (H4 _ _ Ht) as (_ & Hm). replace (Zpos (okey (o + j)) - 1) with (o + j) in Hm by (unfold okey; lia).
    rewrite Hm. f_equal. cbn [bden].
    pose proof (fact_implied_ok E (s_facts S) _ HF0 Himp) as Hz. cbn [fact_ok] in Hz.
    assert (Heq : lden E l = lden E l').
    { rewrite lden_lsub in Hz. apply bv_eq. rewrite bv_sub_unsigned in Hz. unfold bv_wrap in Hz. change (bv_modulus 64) with two64 in Hz.
      pose proof (u_range E l) as B1. pose proof (u_range E l') as B2.
      assert (Hm0 : (bv_unsigned (lden E l) - bv_unsigned (lden E l')) mod two64 = 0) by lia.
      apply Z.mod_divide in Hm0; [|unfold two64; lia]. destruct Hm0 as [q Hq]. unfold two64 in *. nia. }
    rewrite Heq. reflexivity.
  - exact (rgs_disj_upd E (s_rgs S) i (put8_rg o l' R) R Hn eq_refl eq_refl HD0).
Qed.

#[using="Type"] Theorem hx_unz_ok : forall i S K, hx_unz i S = Some K ->
  hcall_rule0 segs S K /\ (s_next S <= s_next K)%positive /\ shape (s_rgs K) = shape (s_rgs S).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros i S K H. unfold hx_unz in H.
  destruct (nth_error (s_rgs S) i) as [R|] eqn:Hn; [|discriminate].
  destruct (rg_kind R) eqn:Hk; try discriminate.
  destruct (all_bk0t (rg_cont R)) eqn:Hz; [|discriminate]. injection H as <-.
  split; [|split; [cbn [s_next]; lia | cbn [s_rgs]; exact (shape_upd_rg _ i R (RG (rg_base R) (rg_size R) RZ TEmpty) Hn eq_refl eq_refl)]].
  intros E ms Hd. exists ms, E. split; [apply ist_refl|]. split; [|split; [intros x Hx; reflexivity | intros x _; reflexivity]].
  intros E' Ha. pose proof (Hd E' Ha) as (Hpc0 & Hsvc0 & Hresv0 & HR0 & HG0 & HD0 & HF0 & Hfrm0).
  unfold sden0. cbn [s_pc s_regs s_rgs s_facts s_resv s_next].
  refine (conj Hpc0 (conj Hsvc0 (conj Hresv0 (conj HR0 (conj _ (conj _ (conj HF0 Hfrm0))))))).
  - apply (upd_nth_forall (rg_ok segs E' (ms_mem ms)) (s_rgs S) i R _ Hn); [|exact HG0].
    rewrite Forall_forall in HG0. pose proof (HG0 R (nth_error_In _ _ Hn)) as (H1 & H2 & H3 & H4).
    unfold rg_ok. cbn [rg_base rg_size rg_kind rg_cont]. unfold rsz in *. cbn [rg_size rg_base] in *.
    split; [exact H1|]. split; [exact H2|]. split.
    + intros j Hj. pose proof (H3 j Hj) as X. rewrite Hk in X. destruct X as [X1 X2]. split; [exact X1|]. intros _.
      destruct (tget (okey j) (rg_cont R)) as [v|] eqn:Ht; [|exact (X2 eq_refl)].
      destruct (H4 _ _ Ht) as (_ & Hm). replace (Zpos (okey j) - 1) with j in Hm by (unfold okey; lia).
      rewrite Hm. f_equal. unfold all_bk0t in Hz. pose proof (tforall_spec _ _ Hz _ _ Ht) as Y. cbn in Y.
      destruct v as [b|]; [|discriminate]. apply Z.eqb_eq in Y. subst b. reflexivity.
    + intros p v Hp. rewrite tget_empty in Hp. discriminate.
  - exact (rgs_disj_upd E' (s_rgs S) i (RG (rg_base R) (rg_size R) RZ TEmpty) R Hn eq_refl eq_refl HD0).
Qed.
#[using="Type"] Theorem hx_promz_ok : forall i S K, hx_promz i S = Some K ->
  hcall_rule0 segs S K /\ (s_next S <= s_next K)%positive /\ shape (s_rgs K) = shape (s_rgs S).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros i S K H. unfold hx_promz in H.
  destruct (nth_error (s_rgs S) i) as [R|] eqn:Hn; [|discriminate].
  destruct (rg_kind R) eqn:Hk; try discriminate. destruct (is_const (rg_size R)) as [n|] eqn:Hzc; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end. injection H as <-.
  apply andb_prop in Hc as [Hc Hz]. apply andb_prop in Hc as [Hn0 Hn1]. apply Z.leb_le in Hn0, Hn1.
  split; [|split; [cbn [s_next]; lia | cbn [s_rgs]; exact (shape_upd_rg _ i R (RG (rg_base R) (rg_size R) RZ TEmpty) Hn eq_refl eq_refl)]].
  intros E ms Hd. exists ms, E. split; [apply ist_refl|]. split; [|split; [intros x Hx; reflexivity | intros x _; reflexivity]].
  intros E' Ha. pose proof (Hd E' Ha) as (Hpc0 & Hsvc0 & Hresv0 & HR0 & HG0 & HD0 & HF0 & Hfrm0).
  unfold sden0. cbn [s_pc s_regs s_rgs s_facts s_resv s_next].
  refine (conj Hpc0 (conj Hsvc0 (conj Hresv0 (conj HR0 (conj _ (conj _ (conj HF0 Hfrm0))))))).
  - apply (upd_nth_forall (rg_ok segs E' (ms_mem ms)) (s_rgs S) i R _ Hn); [|exact HG0].
    rewrite Forall_forall in HG0. pose proof (HG0 R (nth_error_In _ _ Hn)) as (H1 & H2 & H3 & H4).
    unfold rg_ok. cbn [rg_base rg_size rg_kind rg_cont]. unfold rsz in *. cbn [rg_size rg_base] in *.
    assert (Hrz : bv_unsigned (lden E' (rg_size R)) = n) by exact (is_const_u E' (rg_size R) n Hzc).
    split; [exact H1|]. split; [exact H2|]. split.
    + intros j Hj. pose proof (H3 j Hj) as X. rewrite Hk in X. split; [exact X|]. intros _.
      unfold all_bk0n in Hz. rewrite forallb_forall in Hz. pose proof (Hz (Z.to_nat j) ltac:(apply in_seq; lia)) as Y.
      rewrite Z2Nat.id in Y by lia.
      destruct (tget (okey j) (rg_cont R)) as [[b|l0 j0]|] eqn:Ht; try discriminate. destruct b as [|b|b]; try discriminate.
      destruct (H4 _ _ Ht) as (_ & Hm). replace (Zpos (okey j) - 1) with j in Hm by (unfold okey; lia). rewrite Hm. reflexivity.
    + intros p v Hp. rewrite tget_empty in Hp. discriminate.
  - exact (rgs_disj_upd E' (s_rgs S) i (RG (rg_base R) (rg_size R) RZ TEmpty) R Hn eq_refl eq_refl HD0).
Qed.

#[using="Type"] Lemma rkey_ne_psk : forall r : reg, rkey r <> PSK.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros r. destruct (decide (r = 0%bv)) as [->|Hr]; [change (rkey 0%bv) with xH; discriminate|].
  destruct (rkey_succ r Hr) as (k & Hk & Ek). rewrite Ek. unfold PSK. intros Hc.
  assert (X : Pos.to_nat (Pos.of_succ_nat k) = Pos.to_nat 40) by (rewrite Hc; reflexivity).
  rewrite SuccNat2Pos.id_succ in X. change (Pos.to_nat 40) with 40%nat in X. lia.
Qed.
#[using="Type"] Theorem hx_psr_ok : forall l S K, hx_psr l S = Some K ->
  hcall_rule0 segs S K /\ (s_next S <= s_next K)%positive /\ shape (s_rgs K) = shape (s_rgs S).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros l S K H. unfold hx_psr in H. remember (rset (s_regs S) PSK l) as R' eqn:ER in H. injection H as <-.
  split; [|split; [cbn [s_next]; lia | reflexivity]].
  intros E ms Hd. exists ms, E. split; [apply ist_refl|]. split; [|split; [intros x Hx; reflexivity | intros x _; reflexivity]].
  intros E' Ha. pose proof (Hd E' Ha) as (Hpc0 & Hsvc0 & Hresv0 & HR0 & HG0 & HD0 & HF0 & Hfrm0).
  unfold sden0. cbn [s_pc s_regs s_rgs s_facts s_resv s_next].
  refine (conj Hpc0 (conj Hsvc0 (conj Hresv0 (conj _ (conj HG0 (conj HD0 (conj HF0 Hfrm0))))))).
  unfold regs_ok. intros r. rewrite ER. rewrite rget_rset_other by (apply rkey_ne_psk). exact (HR0 r).
Qed.
End CellRule.
