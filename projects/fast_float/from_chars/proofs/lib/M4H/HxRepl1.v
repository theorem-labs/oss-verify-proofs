(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec FxLin FxCore FxSubst FxSound FxMem FxStep FxEnt FxRgs FxFacts FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.HXH Require Import HxRebyte.

Module HxPsrK.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec FxLin FxCore FxSubst FxSound FxMem FxStep FxEnt FxRgs FxFacts FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.HXH Require Import HxRebyte.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition hx_psrk (k : positive) (l : lin) (S : sst) : option sst :=
  if (Pos.ltb 32 k && lwf (s_next S) l)%bool
  then Some (SST (s_pc S) (rset (s_regs S) k l) (s_rgs S) (s_facts S) (s_next S) (s_resv S)) else None.

Lemma rkey_ne_big : forall (r : reg) (k : positive), (32 < k)%positive -> rkey r <> k.
Proof.
  intros r k Hk. destruct (decide (r = 0%bv)) as [->|Hr].
  - change (rkey 0%bv) with xH. lia.
  - destruct (rkey_succ r Hr) as (j & Hj & Ej). rewrite Ej. intros Hc.
    assert (X : Pos.to_nat (Pos.of_succ_nat j) = Pos.to_nat k) by (rewrite Hc; reflexivity).
    rewrite SuccNat2Pos.id_succ in X. lia.
Qed.

Section Rule.
Variable segs : list Segment.
#[using="Type"] Theorem hx_psrk_ok : forall k l S K, hx_psrk k l S = Some K ->
  hcall_rule0 segs S K /\ (s_next S <= s_next K)%positive /\ shape (s_rgs K) = shape (s_rgs S).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros k l S K H. unfold hx_psrk in H.
  destruct (Pos.ltb 32 k && lwf (s_next S) l)%bool eqn:Hc; [|discriminate].
  apply andb_prop in Hc as [Hk _]. apply Pos.ltb_lt in Hk.
  remember (rset (s_regs S) k l) as R' eqn:ER in H. injection H as <-.
  split; [|split; [cbn [s_next]; lia | reflexivity]].
  intros E ms Hd. exists ms, E. split; [apply ist_refl|]. split; [|split; [intros x Hx; reflexivity | intros x _; reflexivity]].
  intros E' Ha. pose proof (Hd E' Ha) as (Hpc0 & Hsvc0 & Hresv0 & HR0 & HG0 & HD0 & HF0 & Hfrm0).
  unfold sden0. cbn [s_pc s_regs s_rgs s_facts s_resv s_next].
  refine (conj Hpc0 (conj Hsvc0 (conj Hresv0 (conj _ (conj HG0 (conj HD0 (conj HF0 Hfrm0))))))).
  unfold regs_ok. intros r. rewrite ER. rewrite rget_rset_other by (apply rkey_ne_big; exact Hk). exact (HR0 r).
Qed.
End Rule.
End HxPsrK.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition repl1_rg (o : Z) (l' : lin) (R : region) : region := RG (rg_base R) (rg_size R) (rg_kind R) (put_bytes (rg_cont R) o [BV l' 0]).
Definition hx_repl1 (i : nat) (o : Z) (l' : lin) (S : sst) : option sst :=
  match nth_error (s_rgs S) i with
  | Some R => match tget (okey o) (rg_cont R) with
              | Some (BV l 0) =>
                  let K := SST (s_pc S) (s_regs S) (upd_nth (s_rgs S) i (repl1_rg o l' R)) (s_facts S) (s_next S) (s_resv S) in
                  if (Z.leb 0 o && fact_implied (s_facts S) (FRange (lsub l l') 0 0) && lwf (s_next S) l')%bool then Some K else None
              | _ => None
              end
  | None => None
  end.

Section R.
Variable segs : list Segment.

#[using="Type"] Lemma repl1_rg_ok : forall E m R o l l', 0 <= o -> tget (okey o) (rg_cont R) = Some (BV l 0) -> lden E l = lden E l' ->
  rg_ok segs E m R -> rg_ok segs E m (repl1_rg o l' R).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m R o l l' Ho Ht Hl HR. pose proof HR as (H1 & H2 & H3 & H4). unfold repl1_rg. unfold rg_ok. cbn [rg_base rg_size rg_kind rg_cont]. unfold rsz in *. cbn [rg_size rg_base] in *.
  assert (Hin : forall p, (Z.leb o (Zpos p - 1) && Z.ltb (Zpos p - 1) (o + Z.of_nat (length [BV l' 0])))%bool = true -> p = okey o).
  { intros p Hp. apply andb_prop in Hp as [Hp1 Hp2]. apply Z.leb_le in Hp1. apply Z.ltb_lt in Hp2. cbn [length] in Hp2.
    unfold okey. apply Pos2Z.inj. rewrite Z2Pos.id by lia. lia. }
  split; [exact H1|]. split; [exact H2|]. split.
  - intros i Hi. pose proof (H3 i Hi) as X. destruct (rg_kind R); try exact X.
    + destruct X as [X1 X2]. split; [exact X1|]. intros Hn. apply X2. rewrite put_bytes_spec in Hn by exact Ho.
      destruct (Z.leb o (Zpos (okey i) - 1) && Z.ltb (Zpos (okey i) - 1) (o + Z.of_nat (length [BV l' 0])))%bool eqn:Hp.
      * assert (E0 : Zpos (okey i) - 1 - o = 0) by (apply andb_prop in Hp as [P1 P2]; apply Z.leb_le in P1; apply Z.ltb_lt in P2; cbn [length] in P2; lia).
        rewrite E0 in Hn. cbn in Hn. discriminate.
      * exact Hn.
    + destruct X as [X1 X2]. split; [exact X1|]. intros Hn. apply X2. rewrite put_bytes_spec in Hn by exact Ho.
      destruct (Z.leb o (Zpos (okey i) - 1) && Z.ltb (Zpos (okey i) - 1) (o + Z.of_nat (length [BV l' 0])))%bool eqn:Hp.
      * assert (E0 : Zpos (okey i) - 1 - o = 0) by (apply andb_prop in Hp as [P1 P2]; apply Z.leb_le in P1; apply Z.ltb_lt in P2; cbn [length] in P2; lia).
        rewrite E0 in Hn. cbn in Hn. discriminate.
      * exact Hn.
  - intros p v Hp. rewrite put_bytes_spec in Hp by exact Ho.
    destruct (Z.leb o (Zpos p - 1) && Z.ltb (Zpos p - 1) (o + Z.of_nat (length [BV l' 0])))%bool eqn:Hq.
    + assert (E0 : Zpos p - 1 - o = 0) by (apply andb_prop in Hq as [P1 P2]; apply Z.leb_le in P1; apply Z.ltb_lt in P2; cbn [length] in P2; lia).
      pose proof (Hin _ Hq) as E1. rewrite E0 in Hp. cbn in Hp. injection Hp as <-. rewrite E1.
      destruct (H4 _ _ Ht) as (Z1 & Z2). split; [exact Z1|]. rewrite Z2. cbn [bden]. rewrite Hl. reflexivity.
    + exact (H4 p v Hp).
Qed.

#[using="Type"] Theorem hx_repl1_ok : forall i o l' S K, hx_repl1 i o l' S = Some K ->
  hcall_rule0 segs S K /\ (s_next S <= s_next K)%positive /\ shape (s_rgs K) = shape (s_rgs S).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros i o l' S K H. unfold hx_repl1 in H.
  destruct (nth_error (s_rgs S) i) as [R|] eqn:Hn; [|discriminate].
  destruct (tget (okey o) (rg_cont R)) as [[c|l j]|] eqn:Ht; try discriminate.
  destruct j as [|j|j]; try discriminate.
  destruct (Z.leb 0 o && fact_implied (s_facts S) (FRange (lsub l l') 0 0) && lwf (s_next S) l')%bool eqn:Hc; [|discriminate]. injection H as <-.
  apply andb_prop in Hc as [Hc Hw]. apply andb_prop in Hc as [Ho Hf]. apply Z.leb_le in Ho.
  split; [|split; [cbn [s_next]; apply Pos.le_refl | cbn [s_rgs]; exact (shape_upd_rg _ i R (repl1_rg o l' R) Hn eq_refl eq_refl)]].
  intros E ms Hd. exists ms, E. split; [apply ist_refl|]. split; [|split; [intros x Hx; reflexivity | intros x _; reflexivity]].
  intros E' Ha. pose proof (Hd E' Ha) as (Hpc0 & Hsvc0 & Hresv0 & HR0 & HG0 & HD0 & HF0 & Hfrm0).
  unfold sden0. cbn [s_pc s_regs s_rgs s_facts s_resv s_next].
  refine (conj Hpc0 (conj Hsvc0 (conj Hresv0 (conj HR0 (conj _ (conj _ (conj HF0 Hfrm0))))))).
  - apply (upd_nth_forall (rg_ok segs E' (ms_mem ms)) (s_rgs S) i R (repl1_rg o l' R) Hn); [|exact HG0].
    rewrite Forall_forall in HG0. apply (repl1_rg_ok E' (ms_mem ms) R o l l' Ho Ht); [|apply HG0; exact (nth_error_In _ _ Hn)].
    pose proof (fact_implied_ok E' _ _ HF0 Hf) as X. cbn [fact_ok] in X. rewrite lden_lsub in X.
    apply bv_eq. rewrite bv_sub_unsigned in X. unfold bv_wrap in X.
    pose proof (bv_unsigned_in_range _ (lden E' l)) as B1. pose proof (bv_unsigned_in_range _ (lden E' l')) as B2. unfold bv_modulus in *.
    assert (Hm : (bv_unsigned (lden E' l) - bv_unsigned (lden E' l')) mod 2 ^ Z.of_N 64 = 0) by lia.
    change (2 ^ Z.of_N 64) with 18446744073709551616 in *. Z.div_mod_to_equations. lia.
  - exact (rgs_disj_upd E' (s_rgs S) i (repl1_rg o l' R) R Hn eq_refl eq_refl HD0).
Qed.
End R.
