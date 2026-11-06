(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.openssl.ct.lib.VCommon Require Import PropExec FastWord FastWordSem.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import ExTrie ExBytes.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxLazy AxLin AxRel AxVal AxBytes AxMem AxMemC AxZZ AxScan AxSymz.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition off_miss (s : store) (d : lin) (N n : Z) : option ivl :=
  if rbetween 3 s d (-4611686018427387903) (- N) then Some (-4611686018427387903, - N)
  else if rbetween 3 s d n 4611686018427387903 then Some (n, 4611686018427387903)
  else None.

Lemma off_miss_sound (ρ : valuation) (s : store) (d : lin) (N n : Z) :
  sat ρ s -> forall i, off_miss s d N n = Some i -> fst i <= leval ρ d <= snd i.
Proof.
  intros Hs i H. unfold off_miss in H.
  destruct (rbetween 3 s d (-4611686018427387903) (- N)) eqn:E1.
  { injection H as <-. exact (rbetween_sound ρ s 3 _ _ _ Hs E1). }
  destruct (rbetween 3 s d n 4611686018427387903) eqn:E2; [|discriminate].
  injection H as <-. exact (rbetween_sound ρ s 3 _ _ _ Hs E2).
Qed.

(* [comment removed for export] *)
Definition bg_misses (s : store) (ts : terms) (o : w64) (n : Z) (R : region) : bool :=
  negb (is_shadow R) |||
  match off_miss s (lsub (wS (rg_bo R), rg_ts R) (wS o, ts)) (to_Z (rg_n R)) n with
  | Some (lo, hi) => (- 4611686018427387904 <? lo) && (hi <? 4611686018427387904) && ((hi + to_Z (rg_n R) <=? 0) || (n <=? lo))
  | None => false
  end.

(* [comment removed for export] *)
Definition hs_witness (s : store) (A : list region) : bool := hs_wit s A.

Section WithSegs.
Variable segs : list Segment.

Definition a_load4 (s : store) (A : list region) (v : xv) (n : nat) : option (list xb) :=
  match a_load3 segs s A v n with
  | Some l => Some l
  | None =>
      match xaddr v with
      | Some (ts, o) =>
          if in_hs s ts o (Z.of_nat n) &&& lforall (bg_misses s ts o (Z.of_nat n)) A &&& hs_witness s A
          then Some (repeat (BL 0%uint63) n) else a_load_symz s A v n
      | None => a_load_symz s A v n      (* [comment removed for export] *)
      end
  end.

Lemma a_load4_length (s : store) (A : list region) (v : xv) (n : nat) (l : list xb) : a_load4 s A v n = Some l -> length l = n.
Proof.
  unfold a_load4. destruct (a_load3 segs s A v n) as [l0|] eqn:E.
  - intros H. injection H as <-. exact (a_load3_length segs s A v n l0 E).
  - destruct (xaddr v) as [[ts o]|]; [|apply a_load_symz_length].
    destruct (in_hs s ts o (Z.of_nat n) &&& lforall (bg_misses s ts o (Z.of_nat n)) A &&& hs_witness s A); [|apply a_load_symz_length].
    intros H. injection H as <-. apply repeat_length.
Qed.

(* [comment removed for export] *)
Lemma hs_mapped (ρ : valuation) (s : store) (A : list region) (m : word -> option byte) :
  segs_low segs -> sat ρ s -> RMem segs ρ A m -> hs_ok ρ A m -> hs_witness s A = true ->
  forall z, hs_beg <= z < hs_hi -> m (wz z) <> None.
Proof.
  intros Hlow Hs HM Hhs Esh. destruct (hs_old_of_wit ρ s A m Esh Hhs) as [_ [_ [_ P4]]].
  apply hs_wit_ex in Esh as (R & HRin & Hsh & Hpos & Hb).
  destruct (in_hs_l_ex ρ s _ _ _ Hs Hb) as (lb & hb & Hrb & Hb1 & Hb2).
  assert (Hrb' : rbase ρ R = leval ρ (wS (rg_bo R), rg_ts R)).
  { unfold rbase, smod. rewrite <- (wS_mod (rg_bo R)). rewrite Zplus_mod_idemp_r.
    replace (teval ρ (rg_ts R) + wS (rg_bo R)) with (leval ρ (wS (rg_bo R), rg_ts R)) by (unfold leval; cbn [fst snd]; ring).
    apply Z.mod_small. unfold hs_beg, hs_hi, two64 in *. lia. }
  destruct HM as [_ HR]. rewrite Forall_forall in HR.
  destruct (RRegion_sh segs ρ m R Hsh (HR R HRin) 0%uint63 ltac:(change (to_Z 0%uint63) with 0; lia)) as [_ Hw].
  assert (Hwr : rk_writable (rg_kind R) = true) by (unfold is_shadow in Hsh; destruct (rg_kind R); try discriminate; reflexivity).
  specialize (Hw Hwr). change (to_Z 0%uint63) with 0 in Hw. rewrite Z.add_0_r in Hw.
  assert (Hm0 : m (wz (rbase ρ R)) <> None)
    by (apply (wview_mapped segs); [exact Hlow | right; rewrite Hrb'; unfold hs_beg, hs_hi in *; lia | rewrite Hrb'; unfold hs_beg, hs_hi, two64 in *; lia | exact Hw]).
  destruct P4 as [P4|P4]; [exact P4|]. exfalso. apply Hm0. apply P4. rewrite Hrb'. unfold hs_beg, hs_hi in *. lia.
Qed.

Lemma bg_misses_sound (ρ : valuation) (s : store) (ts : terms) (o : w64) (n : Z) (R : region) :
  sat ρ s -> region_wf ρ R -> hs_beg <= leval ρ (wS o, ts) -> leval ρ (wS o, ts) + n <= hs_hi -> 0 <= n ->
  bg_misses s ts o n R = true -> is_shadow R = true ->
  forall z, leval ρ (wS o, ts) <= z < leval ρ (wS o, ts) + n -> ~ in_rg ρ R z.
Proof.
  intros Hs Hwf Hf0 Hf1 Hn H Hsh z Hz Hc. unfold bg_misses in H. rewrite Hsh in H. cbn [negb orb] in H.
  destruct (off_miss s (lsub (wS (rg_bo R), rg_ts R) (wS o, ts)) (to_Z (rg_n R)) n) as [[lo hi]|] eqn:El; [|discriminate].
  apply andb_prop in H as [H Hm]. apply andb_prop in H as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2.
  pose proof (off_miss_sound ρ s _ _ _ Hs _ El) as Hr. cbn [fst snd] in Hr. rewrite leval_lsub in Hr.
  set (f := leval ρ (wS o, ts)) in *. set (d := leval ρ (wS (rg_bo R), rg_ts R) - f) in *.
  destruct Hwf as [W1 [W2 _]]. unfold in_rg in Hc.
  assert (Eb : rbase ρ R = (leval ρ (wS (rg_bo R), rg_ts R)) mod two64).
  { unfold rbase, smod, leval. cbn [fst snd]. rewrite <- (wS_mod (rg_bo R)). rewrite Zplus_mod_idemp_r. f_equal. ring. }
  pose proof (smod_range ρ (rg_ts R) (rg_bo R)) as Hsr. fold (rbase ρ R) in Hsr.
  pose proof (to_Z_bounded (rg_n R)) as Hnb. change wB with (2 ^ 63) in Hnb.
  unfold hs_beg, hs_hi, two64 in *.
  assert (Hlv : leval ρ (wS (rg_bo R), rg_ts R) = f + d) by (unfold d; ring).
  rewrite Hlv in Eb.
  destruct (Z_lt_le_dec (f + d) 0) as [Hneg|Hnn]; [|destruct (Z_lt_le_dec (f + d) 18446744073709551616) as [Hlt|Hge]].
  - rewrite <- (Z.mod_unique (f + d) 18446744073709551616 (-1) (f + d + 18446744073709551616)) in Eb by lia.
    apply orb_prop in Hm as [Hm|Hm]; apply Z.leb_le in Hm; lia.
  - rewrite Z.mod_small in Eb by lia. apply orb_prop in Hm as [Hm|Hm]; apply Z.leb_le in Hm; lia.
  - rewrite <- (Z.mod_unique (f + d) 18446744073709551616 1 (f + d - 18446744073709551616)) in Eb by lia.
    apply orb_prop in Hm as [Hm|Hm]; apply Z.leb_le in Hm; lia.
Qed.

Lemma rdn_zeros (m : word -> option byte) (n : nat) : forall (f : Z),
  (forall z, f <= z < f + Z.of_nat n -> m (wz z) = Some (Z_to_bv 8 0)) -> rdn segs m (wz f) n = Some (repeat (Z_to_bv 8 0) n).
Proof.
  induction n as [|n IH]; intros f Hz; [reflexivity|].
  cbn [rdn repeat]. rewrite (Hz f ltac:(lia)). rewrite wz_succ. rewrite IH; [reflexivity|].
  intros z Hzr. apply Hz. lia.
Qed.

Lemma a_load4_sound (ρ : valuation) (s : store) (A : list region) (m : word -> option byte) (v : xv) (a : bv 64) (n : nat) (l : list xb) :
  segs_low segs -> sat ρ s -> RMem segs ρ A m -> hs_ok ρ A m -> xv_val ρ v a -> (1 <= n < 1000)%nat -> a_load4 s A v n = Some l ->
  exists bs, rdn segs m a n = Some bs /\ Forall2 (xb_bv ρ) l bs.
Proof.
  intros Hlow Hs HM Hhs Hv Hn H. unfold a_load4 in H. destruct (a_load3 segs s A v n) as [l0|] eqn:E.
  - injection H as <-. exact (a_load3_sound segs ρ s A m v a n l0 Hs HM Hv Hn E).
  - destruct (xaddr v) as [[ts o]|] eqn:Ea; [|exact (a_load_symz_sound segs ρ s A m v a n l Hs HM Hv H)].
    destruct (in_hs s ts o (Z.of_nat n) &&& lforall (bg_misses s ts o (Z.of_nat n)) A &&& hs_witness s A) eqn:Ec;
      [|exact (a_load_symz_sound segs ρ s A m v a n l Hs HM Hv H)].
    injection H as <-. apply land_true in Ec as [Ec Hwit]. apply land_true in Ec as [Eh Hbg]. pose proof (lforall_forall _ _ Hbg) as Hbg'. clear Hbg. rename Hbg' into Hbg.
    destruct (in_hs_ex ρ s ts o _ Hs Eh) as (lo & hi & Hr & Eh1 & Eh2).
    set (f := leval ρ (wS o, ts)) in *.
    assert (Ha : bv_unsigned a = f).
    { rewrite (xaddr_val ρ v a ts o Hv Ea). unfold smod. rewrite <- (wS_mod o). rewrite Zplus_mod_idemp_r.
      replace (teval ρ ts + wS o) with f by (unfold f, leval; cbn [fst snd]; ring).
      apply Z.mod_small. unfold hs_beg, hs_hi, two64 in *. lia. }
    pose proof (hs_mapped ρ s A m Hlow Hs HM Hhs Hwit) as HSm.
    assert (Hz : forall z, f <= z < f + Z.of_nat n -> m (wz z) = Some (Z_to_bv 8 0)).
    { intros z Hzr. destruct (hs_old_of_wit ρ s A m Hwit Hhs) as [_ [P2 _]].
      assert (Hss : in_ss z) by (right; unfold hs_beg, hs_hi in *; lia).
      assert (Hnot : forall R, In R A -> is_shadow R = true -> ~ in_rg ρ R z).
      { intros R HIn Hsh. destruct HM as [Hok _].
        assert (Hwf : region_wf ρ R).
        { clear -Hok HIn. induction A as [|R0 A' IH]; [destruct HIn|]. destruct Hok as [W [_ Hok']].
          destruct HIn as [<-|HIn]; [exact W | apply IH; assumption]. }
        exact (bg_misses_sound ρ s ts o (Z.of_nat n) R Hs Hwf ltac:(unfold f in *; lia) ltac:(unfold f in *; lia) ltac:(lia) (Hbg R HIn) Hsh z Hzr). }
      destruct (P2 z Hss Hnot) as [X|X]; [exfalso; exact (HSm z ltac:(unfold hs_beg, hs_hi in *; lia) X) | exact X]. }
    exists (repeat (Z_to_bv 8 0) n). split.
    + assert (Haw : a = wz f) by (apply bv_eq; rewrite u_wz; [exact Ha | unfold hs_beg, hs_hi, two64 in *; lia]).
      rewrite Haw. exact (rdn_zeros m n f Hz).
    + clear. induction n as [|n IH]; cbn [repeat]; constructor; [|exact IH]. unfold xb_bv. cbn [xb_z]. reflexivity.
Qed.

End WithSegs.
