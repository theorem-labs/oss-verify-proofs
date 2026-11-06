(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.openssl.bndiv.lib.Common Require Import PropExec FastWord FastWordSem.
From OSSVerify.Proofs.openssl.bndiv.lib.Common.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import MState Mem Exec Frame.
From OSSVerify.Proofs.openssl.bndiv.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxMemSound HxStep HxStepSound HxRunSound HxHook HxHookSound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition regs_nf (Rg : bvmap 5 word) : Prop :=
  exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    Rg = mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.

Lemma reg_lit (r : reg) (k : Z) : bv_unsigned r = k -> r = Z_to_bv 5 k.
Proof. intros <-. apply bv_eq. rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma regs_nf_set (Rg : bvmap 5 word) (rd : reg) (v : word) : is_x0 rd = false -> regs_nf Rg -> regs_nf (bvmap_set rd v Rg).
Proof.
  intros H0 (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20 & x21 & x22
             & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & ->).
  unfold is_x0 in H0. apply Z.eqb_neq in H0. pose proof (bv_unsigned_in_range 5 rd) as Hr. change (bv_modulus 5) with 32 in Hr.
  assert (E : bv_unsigned rd = 1 \/ bv_unsigned rd = 2 \/ bv_unsigned rd = 3 \/ bv_unsigned rd = 4 \/ bv_unsigned rd = 5 \/ bv_unsigned rd = 6
              \/ bv_unsigned rd = 7 \/ bv_unsigned rd = 8 \/ bv_unsigned rd = 9 \/ bv_unsigned rd = 10 \/ bv_unsigned rd = 11 \/ bv_unsigned rd = 12
              \/ bv_unsigned rd = 13 \/ bv_unsigned rd = 14 \/ bv_unsigned rd = 15 \/ bv_unsigned rd = 16 \/ bv_unsigned rd = 17 \/ bv_unsigned rd = 18
              \/ bv_unsigned rd = 19 \/ bv_unsigned rd = 20 \/ bv_unsigned rd = 21 \/ bv_unsigned rd = 22 \/ bv_unsigned rd = 23 \/ bv_unsigned rd = 24
              \/ bv_unsigned rd = 25 \/ bv_unsigned rd = 26 \/ bv_unsigned rd = 27 \/ bv_unsigned rd = 28 \/ bv_unsigned rd = 29 \/ bv_unsigned rd = 30
              \/ bv_unsigned rd = 31) by lia.
  unfold regs_nf.
  repeat (destruct E as [E|E]; [apply reg_lit in E; subst rd; do 31 eexists; reflexivity|]).
  apply reg_lit in E. subst rd. do 31 eexists. reflexivity.
Qed.

Lemma regs_nf_step (Rg Rg' : bvmap 5 word) : regs_nf Rg -> regs_step Rg Rg' -> regs_nf Rg'.
Proof. intros H [->|(rd & v & H0 & ->)]; [exact H | apply regs_nf_set; assumption]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma reg_cases (r : reg) :
  r = Z_to_bv 5 0 \/ r = Z_to_bv 5 1 \/ r = Z_to_bv 5 2 \/ r = Z_to_bv 5 3 \/ r = Z_to_bv 5 4 \/ r = Z_to_bv 5 5 \/ r = Z_to_bv 5 6 \/ r = Z_to_bv 5 7
  \/ r = Z_to_bv 5 8 \/ r = Z_to_bv 5 9 \/ r = Z_to_bv 5 10 \/ r = Z_to_bv 5 11 \/ r = Z_to_bv 5 12 \/ r = Z_to_bv 5 13 \/ r = Z_to_bv 5 14
  \/ r = Z_to_bv 5 15 \/ r = Z_to_bv 5 16 \/ r = Z_to_bv 5 17 \/ r = Z_to_bv 5 18 \/ r = Z_to_bv 5 19 \/ r = Z_to_bv 5 20 \/ r = Z_to_bv 5 21
  \/ r = Z_to_bv 5 22 \/ r = Z_to_bv 5 23 \/ r = Z_to_bv 5 24 \/ r = Z_to_bv 5 25 \/ r = Z_to_bv 5 26 \/ r = Z_to_bv 5 27 \/ r = Z_to_bv 5 28
  \/ r = Z_to_bv 5 29 \/ r = Z_to_bv 5 30 \/ r = Z_to_bv 5 31.
Proof.
  pose proof (bv_unsigned_in_range 5 r) as Hr. change (bv_modulus 5) with 32 in Hr.
  assert (E : bv_unsigned r = 0 \/ bv_unsigned r = 1 \/ bv_unsigned r = 2 \/ bv_unsigned r = 3 \/ bv_unsigned r = 4 \/ bv_unsigned r = 5 \/ bv_unsigned r = 6
              \/ bv_unsigned r = 7 \/ bv_unsigned r = 8 \/ bv_unsigned r = 9 \/ bv_unsigned r = 10 \/ bv_unsigned r = 11 \/ bv_unsigned r = 12
              \/ bv_unsigned r = 13 \/ bv_unsigned r = 14 \/ bv_unsigned r = 15 \/ bv_unsigned r = 16 \/ bv_unsigned r = 17 \/ bv_unsigned r = 18
              \/ bv_unsigned r = 19 \/ bv_unsigned r = 20 \/ bv_unsigned r = 21 \/ bv_unsigned r = 22 \/ bv_unsigned r = 23 \/ bv_unsigned r = 24
              \/ bv_unsigned r = 25 \/ bv_unsigned r = 26 \/ bv_unsigned r = 27 \/ bv_unsigned r = 28 \/ bv_unsigned r = 29 \/ bv_unsigned r = 30
              \/ bv_unsigned r = 31) by lia.
  repeat (destruct E as [E|E]; [apply reg_lit in E; tauto|]). apply reg_lit in E. tauto.
Qed.

(* [comment removed for export] *)
Lemma Rregs_return (rho : valuation) (Rg : regfile hval) (res : hval)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
    (F F' : bvmap 5 word) (pc pc' : word) (fc fc' : bv 32) (rv rv' : option word) :
  Rregs rho Rg (Core (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F pc fc rv) ->
  den rho res a0' ->
  Rregs rho (rf_set (havoc_caller_saved Rg) X10 res)
        (Core (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' pc' fc' rv').
Proof.
  intros H Hd r.
  destruct (reg_cases r) as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
    subst r; try exact I; try exact Hd; try reflexivity;
    match goal with |- den _ _ (Sem.rget _ ?r) => exact (H r) end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section MemKit.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition bytes_kept (rho : valuation) (t : int) (rg : region) (m m' : word -> option byte) : Prop :=
  forall i, 0 <= i < to_Z (rg_size rg) ->
    mrd segs m' (wa (rbase rho t rg + i)) = mrd segs m (wa (rbase rho t rg + i))
    /\ (wview segs m (wa (rbase rho t rg + i)) <> None -> wview segs m' (wa (rbase rho t rg + i)) <> None).

Lemma region_ok_frame (rho : valuation) (t : int) (rg : region) (m m' : word -> option byte) :
  region_ok segs rho t rg m -> bytes_kept rho t rg m m' -> region_ok segs rho t rg m'.
Proof.
  intros (H0 & H1 & H2 & H3 & H4 & H5 & H6 & Hb) Hk. unfold region_ok. repeat (split; [assumption|]).
  intros i Hi. destruct (Hb i Hi) as (b & Eb & Kb & Wb). destruct (Hk i Hi) as [E W].
  exists b. split; [rewrite E; exact Eb|]. split; [exact Kb | intros Hw; apply W, Wb, Hw].
Qed.

(* [comment removed for export] *)
Lemma region_ok_upd (rho : valuation) (t : int) (rg rg' : region) (m m' : word -> option byte) :
  region_ok segs rho t rg m -> same_dir rg rg' ->
  (forall i, 0 <= i < to_Z (rg_size rg) ->
     exists b, mrd segs m' (wa (rbase rho t rg + i)) = Some b /\ kb_ok rho (rg_kb segs rg' i) b
               /\ (rg_wr rg = true -> wview segs m' (wa (rbase rho t rg + i)) <> None)) ->
  region_ok segs rho t rg' m'.
Proof.
  intros (H0 & H1 & H2 & H3 & H4 & H5 & H6 & _) (Ea & Es & El & Ew & Ed & Edd) Hb.
  assert (EB : rbase rho t rg' = rbase rho t rg) by (unfold rbase; rewrite Ea; reflexivity).
  unfold region_ok. rewrite EB, Es, El, Ew, Edd. repeat (split; [assumption|]). exact Hb.
Qed.

(* [comment removed for export] *)
Lemma regions_sep_mset_same (rho : valuation) (M : mem) (t : int) (rg rg' : region) :
  mget M t = Some rg -> same_dir rg rg' -> regions_sep rho M -> regions_sep rho (mset M t rg').
Proof.
  intros Eg (Ea & Es & _ & Ew & _) Hsep t1 t2 r1 r2 G1 G2 Hne Hw.
  assert (EB : forall tt, rbase rho tt rg' = rbase rho tt rg) by (intros tt; unfold rbase; rewrite Ea; reflexivity).
  rewrite (mget_mset M t t1 rg' (mget_lt M t rg Eg)) in G1. rewrite (mget_mset M t t2 rg' (mget_lt M t rg Eg)) in G2.
  destruct (Z.eqb_spec (to_Z t) (to_Z t1)) as [E1|E1]; destruct (Z.eqb_spec (to_Z t) (to_Z t2)) as [E2|E2].
  - exfalso. apply Hne. apply to_Z_inj. congruence.
  - injection G1 as <-. apply to_Z_inj in E1. subst t1. rewrite EB, Es. rewrite Ew in Hw. exact (Hsep t t2 rg r2 Eg G2 Hne Hw).
  - injection G2 as <-. apply to_Z_inj in E2. subst t2. rewrite EB, Es. rewrite Ew in Hw. exact (Hsep t1 t r1 rg G1 Eg Hne Hw).
  - exact (Hsep t1 t2 r1 r2 G1 G2 Hne Hw).
Qed.

Lemma mget_mset_cases (M : mem) (t t2 : int) (rg' rg2 : region) : to_Z t < to_Z TAGLIM ->
  mget (mset M t rg') t2 = Some rg2 -> (t2 = t /\ rg2 = rg') \/ (t2 <> t /\ mget M t2 = Some rg2).
Proof.
  intros Ht G. rewrite (mget_mset M t t2 rg' Ht) in G. destruct (Z.eqb_spec (to_Z t) (to_Z t2)) as [E|E].
  - left. split; [symmetry; apply to_Z_inj; exact E | congruence].
  - right. split; [intros ->; apply E; reflexivity | exact G].
Qed.

(* [comment removed for export] *)
Lemma Rmem_replace (rho : valuation) (M : mem) (t : int) (rg rg' : region) (m m' : word -> option byte) :
  Rmem segs rho M m -> mget M t = Some rg -> same_dir rg rg' ->
  (forall i, 0 <= i < to_Z (rg_size rg) ->
     exists b, mrd segs m' (wa (rbase rho t rg + i)) = Some b /\ kb_ok rho (rg_kb segs rg' i) b
               /\ (rg_wr rg = true -> wview segs m' (wa (rbase rho t rg + i)) <> None)) ->
  (forall t2 rg2, mget M t2 = Some rg2 -> t2 <> t -> bytes_kept rho t2 rg2 m m') ->
  Rmem segs rho (mset M t rg') m'.
Proof.
  intros [HR Hsep] Eg Hd Hb Hk. split.
  - intros t2 rg2 G. destruct (mget_mset_cases M t t2 rg' rg2 (mget_lt M t rg Eg) G) as [[-> ->]|[Hne G2]].
    + exact (region_ok_upd rho t rg rg' m m' (HR t rg Eg) Hd Hb).
    + exact (region_ok_frame rho t2 rg2 m m' (HR t2 rg2 G2) (Hk t2 rg2 G2 Hne)).
  - exact (regions_sep_mset_same rho M t rg rg' Eg Hd Hsep).
Qed.

(* [comment removed for export] *)
Lemma Rmem_frame (rho : valuation) (M : mem) (m m' : word -> option byte) :
  Rmem segs rho M m -> (forall t rg, mget M t = Some rg -> bytes_kept rho t rg m m') -> Rmem segs rho M m'.
Proof.
  intros [HR Hsep] Hk. split; [|exact Hsep]. intros t rg G. exact (region_ok_frame rho t rg m m' (HR t rg G) (Hk t rg G)).
Qed.

(* [comment removed for export] *)
Lemma Rmem_new_region (rho : valuation) (M : mem) (t n al : int) (m : word -> option byte) :
  Rmem segs rho M m -> mget M t = None -> to_Z t < to_Z TAGLIM ->
  0 < rho t -> rho t + to_Z n < two63 -> to_Z n < 2 ^ 62 -> to_Z al < 63 -> rho t mod 2 ^ to_Z al = 0 ->
  (forall i, 0 <= i < to_Z n -> (exists b, mrd segs m (wa (rho t + i)) = Some b) /\ wview segs m (wa (rho t + i)) <> None) ->
  (forall t2 rg2, mget M t2 = Some rg2 -> rho t + to_Z n <= rbase rho t2 rg2 \/ rbase rho t2 rg2 + to_Z (rg_size rg2) <= rho t) ->
  Rmem segs rho (new_region M t n al DUnk) m.
Proof.
  intros [HR Hsep] Hfresh Ht Hpos Hhi H62 Hal Hmod Hbytes Hdisj. unfold new_region.
  set (rg' := RG None n al true DUnk (depth_for 60 n 0) IEmpty). split.
  - intros t2 rg2 G. destruct (mget_mset_cases M t t2 rg' rg2 Ht G) as [[-> ->]|[Hne G2]]; [|exact (HR t2 rg2 G2)].
    unfold region_ok, rbase. cbn [rg' rg_abs rg_size rg_al rg_wr rg_d].
    assert (Hdep : to_Z n <= 8 * 2 ^ Z.of_nat (depth_for 60 n 0) /\ Z.of_nat (depth_for 60 n 0) <= 59).
    { assert (G60 : forall fuel d, (fuel + d = 60)%nat -> (forall d', (d' < d)%nat -> 8 * 2 ^ Z.of_nat d' < to_Z n) ->
                     to_Z n <= 8 * 2 ^ Z.of_nat (depth_for fuel n d) /\ Z.of_nat (depth_for fuel n d) <= 59).
      { induction fuel as [|fuel IH]; intros d Hfd Hlow.
        - exfalso. assert (d = 60%nat) by lia. subst d. specialize (Hlow 59%nat ltac:(lia)). change (8 * 2 ^ Z.of_nat 59) with (2 ^ 62) in Hlow. lia.
        - cbn [depth_for].
          assert (Ed : to_Z (of_Z (Z.of_nat d)) = Z.of_nat d) by (rewrite of_Z_spec; apply Z.mod_small; rewrite wB_eq; unfold two63; lia).
          assert (E8 : to_Z (8 << of_Z (Z.of_nat d))%uint63 = 8 * 2 ^ Z.of_nat d).
          { rewrite lsl_spec, Ed. change (to_Z 8%uint63) with 8. apply Z.mod_small. rewrite wB_eq. unfold two63.
            assert (2 ^ Z.of_nat d <= 2 ^ 59) by (apply Z.pow_le_mono_r; lia). assert (0 < 2 ^ Z.of_nat d) by (apply Z.pow_pos_nonneg; lia). lia. }
          destruct (n <=? 8 << of_Z (Z.of_nat d))%uint63 eqn:El.
          + apply leb_spec in El. rewrite E8 in El. split; [exact El | lia].
          + apply (IH (Datatypes.S d)); [lia|]. intros d' Hd'. destruct (Nat.eq_dec d' d) as [->|Hne2]; [|apply Hlow; lia].
            destruct (Z_lt_le_dec (8 * 2 ^ Z.of_nat d) (to_Z n)) as [L|L]; [exact L|]. exfalso.
            assert (Hc : (n <=? 8 << of_Z (Z.of_nat d))%uint63 = true) by (apply leb_spec; rewrite E8; exact L). congruence. }
      apply (G60 60%nat 0%nat); [reflexivity | intros d' Hd'; lia]. }
    destruct Hdep as [Hd1 Hd2]. split; [split; [lia | left; exact Hpos]|]. repeat (split; [assumption|]).
    intros i Hi. destruct (Hbytes i Hi) as [[b Eb] Wb]. exists b. split; [exact Eb|]. split; [|intros _; exact Wb].
    unfold rg_kb, rd_cell. cbn [rg' rg_d rg_cells rg_dflt]. rewrite iget_empty. cbn [dflt_cell cell_kb].
    change (to_Z 0%uint63) with 0. rewrite Z.bits_0. exact I.
  - intros t1 t2 r1 r2 G1 G2 Hne Hw.
    destruct (mget_mset_cases M t t1 rg' r1 Ht G1) as [[-> ->]|[N1 G1']]; destruct (mget_mset_cases M t t2 rg' r2 Ht G2) as [[-> ->]|[N2 G2']].
    + exfalso. apply Hne. reflexivity.
    + unfold rbase at 1 3. cbn [rg' rg_abs rg_size]. exact (Hdisj t2 r2 G2').
    + unfold rbase at 2 4. cbn [rg' rg_abs rg_size]. destruct (Hdisj t1 r1 G1') as [D|D]; [right | left]; exact D.
    + exact (Hsep t1 t2 r1 r2 G1' G2' Hne Hw).
Qed.

(* [comment removed for export] *)
Lemma Rmem_kill_region (rho : valuation) (M : mem) (t : int) (rg : region) (m : word -> option byte) :
  Rmem segs rho M m -> mget M t = Some rg -> Rmem segs rho (kill_region M t rg) m.
Proof.
  intros [HR Hsep] Eg. unfold kill_region. set (rg' := RG (Some 0%uint63) 0 0 false DUnk 0 IEmpty).
  assert (EB : forall tt, rbase rho tt rg' = 0) by reflexivity.
  split.
  - intros t2 rg2 G. destruct (mget_mset_cases M t t2 rg' rg2 (mget_lt M t rg Eg) G) as [[-> ->]|[Hne G2]]; [|exact (HR t2 rg2 G2)].
    unfold region_ok. rewrite EB. cbn [rg' rg_size rg_d rg_al]. change (to_Z 0%uint63) with 0.
    repeat (split; [first [lia | (unfold two63; lia) | (cbn; lia) | reflexivity]|]). intros i Hi. lia.
  - intros t1 t2 r1 r2 G1 G2 Hne Hw.
    destruct (mget_mset_cases M t t1 rg' r1 (mget_lt M t rg Eg) G1) as [[-> ->]|[N1 G1']];
      destruct (mget_mset_cases M t t2 rg' r2 (mget_lt M t rg Eg) G2) as [[-> ->]|[N2 G2']].
    + exfalso. apply Hne. reflexivity.
    + rewrite EB. cbn [rg' rg_size]. change (to_Z 0%uint63) with 0. destruct (HR t2 r2 G2') as ((H0 & _) & _). left. lia.
    + rewrite EB. cbn [rg' rg_size]. change (to_Z 0%uint63) with 0. destruct (HR t1 r1 G1') as ((H0 & _) & _). right. lia.
    + exact (Hsep t1 t2 r1 r2 G1' G2' Hne Hw).
Qed.

End MemKit.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section KbKit.
Variable segs : list Segment.

Lemma of_Z_small (z : Z) : 0 <= z < 2 ^ 62 -> to_Z (of_Z z) = z.
Proof. intros H. rewrite of_Z_spec. apply Z.mod_small. rewrite wB_eq. unfold two63. lia. Qed.

(* [comment removed for export] *)
Lemma rd_cell_drop_below (rg : region) (off k : int) : to_Z k < 2 ^ Z.of_nat (rg_d rg) -> rg_dflt rg = DUnk ->
  rd_cell segs (drop_below rg off) k = if (to_Z k <? to_Z off / 8) then CW w_zero 0 else rd_cell segs rg k.
Proof.
  intros Hk Hd. unfold rd_cell, drop_below. cbn [rg_d rg_cells rg_dflt]. rewrite iget_iremove.
  pose proof (to_Z_bounded k) as Bk. rewrite Z.add_0_l, Z.mul_1_l, Z.mod_small by lia. rewrite lsr_spec. change (2 ^ to_Z 3%uint63) with 8.
  rewrite Hd. destruct (iget (rg_d rg) (rg_cells rg) k) as [c|]; destruct (to_Z k <? to_Z off / 8); reflexivity.
Qed.

Lemma rg_kb_drop_below (rg : region) (off : int) (i : Z) : 0 <= i < to_Z (rg_size rg) ->
  to_Z (rg_size rg) <= 8 * 2 ^ Z.of_nat (rg_d rg) -> to_Z (rg_size rg) < 2 ^ 62 -> rg_dflt rg = DUnk -> to_Z off mod 8 = 0 ->
  rg_kb segs (drop_below rg off) i = if (i <? to_Z off) then KU else rg_kb segs rg i.
Proof.
  intros Hi Hd H62 Hdf Hal. unfold rg_kb.
  assert (Ei : to_Z (of_Z (i / 8)) = i / 8) by (apply of_Z_small; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite rd_cell_drop_below by (try exact Hdf; rewrite Ei; apply Z.div_lt_upper_bound; lia). rewrite Ei.
  pose proof (to_Z_bounded off) as Bo. pose proof (Z.div_mod (to_Z off) 8 ltac:(lia)) as Eo. rewrite Hal, Z.add_0_r in Eo.
  pose proof (Z.div_mod i 8 ltac:(lia)) as Ei8. pose proof (Z.mod_pos_bound i 8 ltac:(lia)) as Him.
  destruct (Z.ltb_spec (i / 8) (to_Z off / 8)) as [L|L]; destruct (Z.ltb_spec i (to_Z off)) as [L2|L2]; try reflexivity; try lia.
  cbn [cell_kb]. change (to_Z 0%uint63) with 0. rewrite Z.bits_0. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma iget_fill_cells (d : nat) (c64 : w64) : forall (cnt : nat) (cells : itrie cell) (k0 k : int),
  to_Z k0 + Z.of_nat cnt <= 2 ^ Z.of_nat d -> Z.of_nat d <= 59 -> to_Z k < 2 ^ Z.of_nat d ->
  iget d (fill_cells d cells k0 cnt c64) k =
  if (to_Z k0 <=? to_Z k) && (to_Z k <? to_Z k0 + Z.of_nat cnt) then Some (CW c64 255) else iget d cells k.
Proof.
  induction cnt as [|cnt IH]; intros cells k0 k Hc Hd Hk; cbn [fill_cells].
  - replace ((to_Z k0 <=? to_Z k) && (to_Z k <? to_Z k0 + Z.of_nat 0)) with false; [reflexivity|].
    symmetry. apply andb_false_iff. rewrite Z.leb_gt, Z.ltb_ge. lia.
  - pose proof (to_Z_bounded k0) as B0. pose proof (to_Z_bounded k) as Bk.
    assert (P : 2 ^ Z.of_nat d <= 2 ^ 59) by (apply Z.pow_le_mono_r; lia).
    assert (E1 : to_Z (k0 + 1)%uint63 = to_Z k0 + 1) by (rewrite add_spec; change (to_Z 1%uint63) with 1; apply Z.mod_small; rewrite wB_eq; unfold two63; lia).
    rewrite IH by (rewrite ?E1; lia). rewrite E1, iget_iset. rewrite !Z.mod_small by lia.
    destruct (Z.eqb_spec (to_Z k0) (to_Z k)) as [E|E].
    + replace ((to_Z k0 + 1 <=? to_Z k) && (to_Z k <? to_Z k0 + 1 + Z.of_nat cnt)) with false by (symmetry; apply andb_false_iff; rewrite Z.leb_gt; lia).
      replace ((to_Z k0 <=? to_Z k) && (to_Z k <? to_Z k0 + Z.of_nat (Datatypes.S cnt))) with true; [reflexivity|].
      symmetry. apply andb_true_intro. rewrite Z.leb_le, Z.ltb_lt. lia.
    + replace ((to_Z k0 <=? to_Z k) && (to_Z k <? to_Z k0 + Z.of_nat (Datatypes.S cnt)))
        with ((to_Z k0 + 1 <=? to_Z k) && (to_Z k <? to_Z k0 + 1 + Z.of_nat cnt)); [reflexivity|].
      destruct (Z.leb_spec (to_Z k0 + 1) (to_Z k)); destruct (Z.leb_spec (to_Z k0) (to_Z k)); destruct (Z.ltb_spec (to_Z k) (to_Z k0 + 1 + Z.of_nat cnt));
        destruct (Z.ltb_spec (to_Z k) (to_Z k0 + Z.of_nat (Datatypes.S cnt))); cbn [andb]; try reflexivity; lia.
Qed.

(* [comment removed for export] *)
Lemma iget_copy_rec (src : region) (d : nat) : forall (cnt : nat) (acc : itrie cell) (k0 k : int) (c : cell),
  to_Z k0 + Z.of_nat cnt <= 2 ^ Z.of_nat d -> Z.of_nat d <= 59 -> to_Z k < 2 ^ Z.of_nat d ->
  iget d (copy_cells_rec src d acc k0 cnt) k = Some c ->
  iget d acc k = Some c \/ (to_Z k0 <= to_Z k < to_Z k0 + Z.of_nat cnt /\ iget (rg_d src) (rg_cells src) k = Some c).
Proof.
  induction cnt as [|cnt IH]; intros acc k0 k c Hc Hd Hk H; cbn [copy_cells_rec] in H; [left; exact H|].
  pose proof (to_Z_bounded k0) as B0. pose proof (to_Z_bounded k) as Bk.
  assert (P : 2 ^ Z.of_nat d <= 2 ^ 59) by (apply Z.pow_le_mono_r; lia).
  assert (E1 : to_Z (k0 + 1)%uint63 = to_Z k0 + 1) by (rewrite add_spec; change (to_Z 1%uint63) with 1; apply Z.mod_small; rewrite wB_eq; unfold two63; lia).
  destruct (IH _ (k0 + 1)%uint63 k c ltac:(rewrite E1; lia) Hd Hk H) as [Ha|[Hr Hs]]; [|right; split; [rewrite E1 in Hr; lia | exact Hs]].
  destruct (iget (rg_d src) (rg_cells src) k0) as [c0|] eqn:E0; [|left; exact Ha].
  rewrite iget_iset in Ha. rewrite !Z.mod_small in Ha by lia. destruct (Z.eqb_spec (to_Z k0) (to_Z k)) as [E|E]; [|left; exact Ha].
  apply to_Z_inj in E. subst k0. injection Ha as <-. right. split; [lia | exact E0].
Qed.

(* [comment removed for export] *)
Lemma rg_kb_copy (src : region) (n : int) (ab : option int) (n2 al : int) (wr : bool) (d2 : nat) (i : Z) :
  0 <= i < to_Z n2 -> to_Z n2 <= 8 * 2 ^ Z.of_nat d2 -> Z.of_nat d2 <= 59 -> to_Z n <= to_Z n2 ->
  rg_kb segs (RG ab n2 al wr DUnk d2 (copy_cells src n d2)) i = KU
  \/ (i < 8 * (to_Z n / 8) /\ rg_kb segs (RG ab n2 al wr DUnk d2 (copy_cells src n d2)) i = rg_kb segs src i).
Proof.
  intros Hi Hd Hd59 Hn. unfold rg_kb at 1 2, rd_cell. cbn [rg_d rg_cells rg_dflt].
  assert (P : 2 ^ Z.of_nat d2 <= 2 ^ 59) by (apply Z.pow_le_mono_r; lia).
  assert (Ei : to_Z (of_Z (i / 8)) = i / 8) by (apply of_Z_small; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  destruct (iget d2 (copy_cells src n d2) (of_Z (i / 8))) as [c|] eqn:E.
  - right. unfold copy_cells in E. pose proof (to_Z_bounded n) as Bn. pose proof (to_Z_bounded (n >> 3)%uint63) as Bn3.
    assert (E3 : to_Z (n >> 3)%uint63 = to_Z n / 8) by (rewrite lsr_spec; reflexivity).
    destruct (iget_copy_rec src d2 (Z.to_nat (to_Z (n >> 3)%uint63)) IEmpty 0%uint63 (of_Z (i / 8)) c) as [Ha|[Hr Hs]]; try exact E; try exact Hd59.
    + change (to_Z 0%uint63) with 0. rewrite Z2Nat.id by lia. rewrite E3.
      apply (Z.le_trans _ (to_Z n2 / 8)); [apply Z.div_le_mono; lia | apply Z.div_le_upper_bound; lia].
    + rewrite Ei. apply Z.div_lt_upper_bound; lia.
    + rewrite iget_empty in Ha. discriminate.
    + change (to_Z 0%uint63) with 0 in Hr. rewrite Z2Nat.id, E3, Ei in Hr by lia.
      split; [pose proof (Z.div_mod i 8 ltac:(lia)); pose proof (Z.mod_pos_bound i 8 ltac:(lia)); lia|].
      unfold rg_kb, rd_cell. rewrite Hs. reflexivity.
  - left. cbn [dflt_cell cell_kb]. change (to_Z 0%uint63) with 0. rewrite Z.bits_0. reflexivity.
Qed.

(* [comment removed for export] *)
Definition rep8_check : bool :=
  forallb (fun b => forallb (fun jj => byteZ (wZ (rep8 (of_Z (Z.of_nat b)))) (Z.of_nat jj) =? Z.of_nat b) (seq 0 8)) (seq 0 256).

Lemma rep8_check_ok : rep8_check = true.
Proof. vm_compute. reflexivity. Qed.

Lemma rep8_land (c : int) : rep8 c = rep8 (c land 255)%uint63.
Proof.
  unfold rep8. assert (E : ((c land 255) land 255 = c land 255)%uint63).
  { apply to_Z_inj. rewrite !land_spec'. change (to_Z 255%uint63) with (Z.ones 8). rewrite !Z.land_ones by lia. apply Z.mod_mod. lia. }
  rewrite E. reflexivity.
Qed.

Lemma byteZ_rep8 (c : int) (j : Z) : 0 <= j < 8 -> byteZ (wZ (rep8 c)) j = to_Z (c land 255)%uint63.
Proof.
  intros Hj. rewrite rep8_land. set (b := (c land 255)%uint63).
  assert (Hb : 0 <= to_Z b < 256).
  { unfold b. rewrite land_spec'. change (to_Z 255%uint63) with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  pose proof rep8_check_ok as Hc. unfold rep8_check in Hc. rewrite forallb_forall in Hc.
  specialize (Hc (Z.to_nat (to_Z b)) ltac:(apply in_seq; lia)). rewrite forallb_forall in Hc.
  specialize (Hc (Z.to_nat j) ltac:(apply in_seq; lia)). rewrite !Z2Nat.id in Hc by lia. rewrite of_to_Z in Hc.
  apply Z.eqb_eq in Hc. exact Hc.
Qed.

(* [comment removed for export] *)
Lemma rg_kb_fill (rg : region) (k0 : int) (cnt : nat) (c : int) (i : Z) :
  0 <= i < to_Z (rg_size rg) -> to_Z (rg_size rg) <= 8 * 2 ^ Z.of_nat (rg_d rg) -> Z.of_nat (rg_d rg) <= 59 ->
  8 * (to_Z k0 + Z.of_nat cnt) <= to_Z (rg_size rg) ->
  rg_kb segs (RG (rg_abs rg) (rg_size rg) (rg_al rg) (rg_wr rg) (rg_dflt rg) (rg_d rg) (fill_cells (rg_d rg) (rg_cells rg) k0 cnt (rep8 c))) i
  = if (8 * to_Z k0 <=? i) && (i <? 8 * (to_Z k0 + Z.of_nat cnt)) then KB (to_Z (c land 255)%uint63) else rg_kb segs rg i.
Proof.
  intros Hi Hd Hd59 Hfit. unfold rg_kb, rd_cell. cbn [rg_d rg_cells rg_dflt].
  assert (P : 2 ^ Z.of_nat (rg_d rg) <= 2 ^ 59) by (apply Z.pow_le_mono_r; lia).
  assert (Ei : to_Z (of_Z (i / 8)) = i / 8) by (apply of_Z_small; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  pose proof (Z.div_mod i 8 ltac:(lia)) as Ei8. pose proof (Z.mod_pos_bound i 8 ltac:(lia)) as Him.
  rewrite iget_fill_cells by (try lia; rewrite Ei; apply Z.div_lt_upper_bound; lia). rewrite Ei.
  destruct ((to_Z k0 <=? i / 8) && (i / 8 <? to_Z k0 + Z.of_nat cnt)) eqn:E.
  - apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    replace ((8 * to_Z k0 <=? i) && (i <? 8 * (to_Z k0 + Z.of_nat cnt))) with true by (symmetry; apply andb_true_intro; rewrite Z.leb_le, Z.ltb_lt; lia).
    cbn [cell_kb]. change (to_Z 255%uint63) with 255. rewrite testbit_255 by lia. rewrite byteZ_rep8 by lia. reflexivity.
  - replace ((8 * to_Z k0 <=? i) && (i <? 8 * (to_Z k0 + Z.of_nat cnt))) with false; [reflexivity|].
    symmetry. apply andb_false_iff. apply andb_false_iff in E. rewrite Z.leb_gt, Z.ltb_ge in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma region_bytes (rho : valuation) (t : int) (rg : region) (m : word -> option byte) (off : Z) (bs : list byte) :
  region_ok segs rho t rg m -> 0 <= off -> off + Z.of_nat (length bs) <= to_Z (rg_size rg) ->
  (forall i b0, nth_error bs i = Some b0 -> forall b, kb_ok rho (rg_kb segs rg (off + Z.of_nat i)) b -> b = b0) ->
  bytes_at segs m (rbase rho t rg + off) bs
  /\ (rg_wr rg = true -> wr_at segs m (rbase rho t rg + off) (Z.of_nat (length bs))).
Proof.
  intros (H0 & H1 & H2 & H3 & H4 & H5 & H6 & Hb) Hoff Hfit Hf. unfold two63 in *. split.
  - split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Hb (off + Z.of_nat i) ltac:(lia)) as (b & Eb & Kb & _). rewrite <- Z.add_assoc, Eb.
    destruct (nth_error bs i) as [b0|] eqn:En; [|apply nth_error_None in En; lia]. f_equal. exact (Hf i b0 En b Kb).
  - intros Hw. split; [lia|]. split; [lia|]. intros i Hi. destruct (Hb (off + i) ltac:(lia)) as (b & _ & _ & Wb).
    rewrite <- Z.add_assoc. apply Wb. exact Hw.
Qed.

(* [comment removed for export] *)
Lemma cell_word_bytes (rho : valuation) (t : int) (rg : region) (m : word -> option byte) (k : int) (w : w64) :
  region_ok segs rho t rg m -> rd_cell segs rg k = CW w 255 -> 8 * to_Z k + 8 <= to_Z (rg_size rg) ->
  bytes_at segs m (rbase rho t rg + 8 * to_Z k) (le8 (wbv w))
  /\ (rg_wr rg = true -> wr_at segs m (rbase rho t rg + 8 * to_Z k) 8).
Proof.
  intros Hok Hc Hfit. pose proof (to_Z_bounded k) as Bk.
  pose proof (region_bytes rho t rg m (8 * to_Z k) (le8 (wbv w)) Hok ltac:(lia)) as H. rewrite length_le8 in H.
  apply H; [exact Hfit|]. intros i b0 En b Kb.
  assert (Hi : (i < 8)%nat) by (apply nth_error_Some_lt in En || (assert (X : nth_error (le8 (wbv w)) i <> None) by congruence; apply nth_error_Some in X; rewrite length_le8 in X; exact X); assumption).
  unfold le8, word_to_le_bytes in En. rewrite wbv_unsigned in En. pose proof (wZ_range w) as Hw.
  rewrite (nth_Z_to_le_bytes 8 (wZ w) i ltac:(lia) Hi) in En. injection En as <-.
  unfold rg_kb in Kb.
  assert (Ek : of_Z ((8 * to_Z k + Z.of_nat i) / 8) = k).
  { apply to_Z_inj. rewrite of_Z_small; [|split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; destruct Hok as (_ & _ & H62 & _); lia]].
    symmetry. apply Z.div_unique with (r := Z.of_nat i); lia. }
  assert (Em : (8 * to_Z k + Z.of_nat i) mod 8 = Z.of_nat i) by (symmetry; apply Z.mod_unique with (q := to_Z k); lia).
  rewrite Ek, Em, Hc in Kb. cbn [cell_kb] in Kb. change (to_Z 255%uint63) with 255 in Kb. rewrite testbit_255 in Kb by lia.
  cbn [kb_ok] in Kb. apply byte_of_eq. exact Kb.
Qed.

End KbKit.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section HookKit.
Variable segs : list Segment.

Lemma depth_for_ok (n : int) : to_Z n < 2 ^ 62 ->
  to_Z n <= 8 * 2 ^ Z.of_nat (depth_for 60 n 0) /\ Z.of_nat (depth_for 60 n 0) <= 59.
Proof.
  intros H62.
  assert (G60 : forall fuel d, (fuel + d = 60)%nat -> (forall d', (d' < d)%nat -> 8 * 2 ^ Z.of_nat d' < to_Z n) ->
                   to_Z n <= 8 * 2 ^ Z.of_nat (depth_for fuel n d) /\ Z.of_nat (depth_for fuel n d) <= 59).
  { induction fuel as [|fuel IH]; intros d Hfd Hlow.
    - exfalso. assert (d = 60%nat) by lia. subst d. specialize (Hlow 59%nat ltac:(lia)). change (8 * 2 ^ Z.of_nat 59) with (2 ^ 62) in Hlow. lia.
    - cbn [depth_for].
      assert (Ed : to_Z (of_Z (Z.of_nat d)) = Z.of_nat d) by (rewrite of_Z_spec; apply Z.mod_small; rewrite wB_eq; unfold two63; lia).
      assert (E8 : to_Z (8 << of_Z (Z.of_nat d))%uint63 = 8 * 2 ^ Z.of_nat d).
      { rewrite lsl_spec, Ed. change (to_Z 8%uint63) with 8. apply Z.mod_small. rewrite wB_eq. unfold two63.
        assert (2 ^ Z.of_nat d <= 2 ^ 59) by (apply Z.pow_le_mono_r; lia). assert (0 < 2 ^ Z.of_nat d) by (apply Z.pow_pos_nonneg; lia). lia. }
      destruct (n <=? 8 << of_Z (Z.of_nat d))%uint63 eqn:El.
      + apply leb_spec in El. rewrite E8 in El. split; [exact El | lia].
      + apply (IH (Datatypes.S d)); [lia|]. intros d' Hd'. destruct (Nat.eq_dec d' d) as [->|Hne2]; [|apply Hlow; lia].
        destruct (Z_lt_le_dec (8 * 2 ^ Z.of_nat d) (to_Z n)) as [L|L]; [exact L|]. exfalso.
        assert (Hc : (n <=? 8 << of_Z (Z.of_nat d))%uint63 = true) by (apply leb_spec; rewrite E8; exact L). congruence. }
  apply (G60 60%nat 0%nat); [reflexivity | intros d' Hd'; lia].
Qed.

(* [comment removed for export] *)
Lemma region_ok_fresh_gen (rho : valuation) (t : int) (ab : option int) (n al : int) (wr : bool) (d : nat) (m : word -> option byte) :
  let rg := RG ab n al wr DUnk d IEmpty in
  (0 <= rbase rho t rg /\ (0 < rbase rho t rg \/ to_Z al = 0)) ->
  rbase rho t rg + to_Z n < two63 -> to_Z n < 2 ^ 62 -> to_Z n <= 8 * 2 ^ Z.of_nat d -> Z.of_nat d <= 59 ->
  to_Z al < 63 -> rbase rho t rg mod 2 ^ to_Z al = 0 ->
  (forall i, 0 <= i < to_Z n -> (exists b, mrd segs m (wa (rbase rho t rg + i)) = Some b)
                                /\ (wr = true -> wview segs m (wa (rbase rho t rg + i)) <> None)) ->
  region_ok segs rho t rg m.
Proof.
  intros rg Hpos Hhi H62 Hd1 Hd2 Hal Hmod Hbytes. unfold region_ok. fold rg. cbn [rg rg_size rg_d rg_al rg_wr].
  repeat (split; [assumption|]).
  intros i Hi. destruct (Hbytes i Hi) as [[b Eb] Wb]. exists b. split; [exact Eb|]. split; [|exact Wb].
  unfold rg_kb, rd_cell. cbn [rg rg_d rg_cells rg_dflt]. rewrite iget_empty. cbn [dflt_cell cell_kb].
  change (to_Z 0%uint63) with 0. rewrite Z.bits_0. exact I.
Qed.

Lemma region_ok_fresh (rho : valuation) (t : int) (ab : option int) (n al : int) (wr : bool) (d : nat) (m : word -> option byte) :
  let rg := RG ab n al wr DUnk d IEmpty in
  0 < rbase rho t rg -> rbase rho t rg + to_Z n < two63 -> to_Z n < 2 ^ 62 -> to_Z n <= 8 * 2 ^ Z.of_nat d -> Z.of_nat d <= 59 ->
  to_Z al < 63 -> rbase rho t rg mod 2 ^ to_Z al = 0 ->
  (forall i, 0 <= i < to_Z n -> (exists b, mrd segs m (wa (rbase rho t rg + i)) = Some b)
                                /\ (wr = true -> wview segs m (wa (rbase rho t rg + i)) <> None)) ->
  region_ok segs rho t rg m.
Proof.
  intros rg Hpos Hhi H62 Hd1 Hd2 Hal Hmod Hbytes. apply (region_ok_fresh_gen rho t ab n al wr d m); try assumption.
  split; [apply Z.lt_le_incl; exact Hpos | left; exact Hpos].
Qed.

(* [comment removed for export] *)
Lemma region_ok_reset (rho : valuation) (t : int) (rg : region) (m m' : word -> option byte) :
  region_ok segs rho t rg m ->
  (forall i, 0 <= i < to_Z (rg_size rg) -> (exists b, mrd segs m' (wa (rbase rho t rg + i)) = Some b)
                                          /\ (rg_wr rg = true -> wview segs m' (wa (rbase rho t rg + i)) <> None)) ->
  region_ok segs rho t (RG (rg_abs rg) (rg_size rg) (rg_al rg) (rg_wr rg) DUnk (rg_d rg) IEmpty) m'.
Proof.
  intros (H0 & H1 & H2 & H3 & H4 & H5 & H6 & _) Hb.
  apply (region_ok_fresh_gen rho t (rg_abs rg) (rg_size rg) (rg_al rg) (rg_wr rg) (rg_d rg) m'); assumption.
Qed.

(* [comment removed for export] *)
Lemma region_ok_drop (rho : valuation) (t : int) (rg : region) (off : int) (m m' : word -> option byte) :
  region_ok segs rho t rg m -> rg_dflt rg = DUnk -> to_Z off mod 8 = 0 ->
  (forall i, 0 <= i < to_Z (rg_size rg) -> (exists b, mrd segs m' (wa (rbase rho t rg + i)) = Some b)
                                          /\ (rg_wr rg = true -> wview segs m' (wa (rbase rho t rg + i)) <> None)) ->
  (forall i, to_Z off <= i < to_Z (rg_size rg) -> mrd segs m' (wa (rbase rho t rg + i)) = mrd segs m (wa (rbase rho t rg + i))) ->
  region_ok segs rho t (drop_below rg off) m'.
Proof.
  intros Hok Hdf Hal Hb Hk. pose proof Hok as (H0 & H1 & H2 & H3 & H4 & H5 & H6 & Hby).
  apply (region_ok_upd segs rho t rg (drop_below rg off) m m' Hok); [repeat split|].
  intros i Hi. destruct (Hb i Hi) as [[b Eb] Wb]. exists b. split; [exact Eb|]. split; [|exact Wb].
  rewrite (rg_kb_drop_below segs rg off i Hi H3 H2 Hdf Hal). destruct (Z.ltb_spec i (to_Z off)) as [L|L]; [exact I|].
  destruct (Hby i Hi) as (b0 & Eb0 & Kb0 & _). rewrite (Hk i ltac:(lia)), Eb0 in Eb. injection Eb as <-. exact Kb0.
Qed.

(* [comment removed for export] *)
Lemma regions_sep_new_wr (rho : valuation) (M : mem) (t : int) (rg' : region) :
  regions_sep rho M -> mget M t = None -> to_Z t < to_Z TAGLIM ->
  (forall t2 rg2, mget M t2 = Some rg2 -> rg_wr rg' = true \/ rg_wr rg2 = true ->
     rbase rho t rg' + to_Z (rg_size rg') <= rbase rho t2 rg2 \/ rbase rho t2 rg2 + to_Z (rg_size rg2) <= rbase rho t rg') ->
  regions_sep rho (mset M t rg').
Proof.
  intros Hsep Hfresh Ht Hdisj t1 t2 r1 r2 G1 G2 Hne Hw.
  destruct (mget_mset_cases M t t1 rg' r1 Ht G1) as [[-> ->]|[N1 G1']]; destruct (mget_mset_cases M t t2 rg' r2 Ht G2) as [[-> ->]|[N2 G2']].
  - exfalso. apply Hne. reflexivity.
  - exact (Hdisj t2 r2 G2' Hw).
  - destruct (Hdisj t1 r1 G1' ltac:(tauto)) as [D|D]; [right | left]; exact D.
  - exact (Hsep t1 t2 r1 r2 G1' G2' Hne Hw).
Qed.

Lemma regions_sep_new (rho : valuation) (M : mem) (t : int) (rg' : region) :
  regions_sep rho M -> mget M t = None -> to_Z t < to_Z TAGLIM ->
  (forall t2 rg2, mget M t2 = Some rg2 ->
     rbase rho t rg' + to_Z (rg_size rg') <= rbase rho t2 rg2 \/ rbase rho t2 rg2 + to_Z (rg_size rg2) <= rbase rho t rg') ->
  regions_sep rho (mset M t rg').
Proof.
  intros Hsep Hfresh Ht Hdisj. apply (regions_sep_new_wr rho M t rg' Hsep Hfresh Ht). intros t2 rg2 G2 _. exact (Hdisj t2 rg2 G2).
Qed.

Lemma regions_sep_kill (rho : valuation) (M : mem) (t : int) (rg : region) (m : word -> option byte) :
  Rmem segs rho M m -> mget M t = Some rg -> regions_sep rho (kill_region M t rg).
Proof. intros HR Eg. exact (proj2 (Rmem_kill_region segs rho M t rg m HR Eg)). Qed.

(* [comment removed for export] *)
Lemma new_region_eq (M : mem) (t n al : int) (df : rdflt) :
  new_region M t n al df = mset M t (RG None n al true df (depth_for 60 n 0) IEmpty).
Proof. reflexivity. Qed.

Lemma kill_region_eq (M : mem) (t : int) (rg : region) : kill_region M t rg = mset M t (RG (Some 0%uint63) 0 0 false DUnk 0 IEmpty).
Proof. reflexivity. Qed.

Lemma same_dirs_mset (M : mem) (t : int) (rg rg' : region) : mget M t = Some rg -> same_dir rg rg' -> same_dirs M (mset M t rg').
Proof.
  intros Eg Hd t2. rewrite (mget_mset M t t2 rg' (mget_lt M t rg Eg)). destruct (Z.eqb_spec (to_Z t) (to_Z t2)) as [E|E].
  - apply to_Z_inj in E. subst t2. rewrite Eg. exact Hd.
  - destruct (mget M t2); [apply same_dir_refl | exact I].
Qed.

Lemma same_dir_drop_below (rg : region) (off : int) : same_dir rg (drop_below rg off).
Proof. repeat split. Qed.

(* [comment removed for export] *)
Lemma Rmem_clobber (rho : valuation) (M : mem) (ts : int) (rgs : region) (o : int) (m : word -> option byte) :
  Rmem segs rho M m -> mget M ts = Some rgs -> rg_dflt rgs = DUnk -> to_Z o mod 8 = 0 ->
  Rmem segs rho (mset M ts (drop_below rgs o)) m.
Proof.
  intros [HR Hsep] Eg Hdf Ho. split.
  - intros t2 rg2 G. destruct (mget_mset_cases M ts t2 _ rg2 (mget_lt M ts rgs Eg) G) as [[-> ->]|[Hne G2]]; [|exact (HR t2 rg2 G2)].
    apply (region_ok_drop rho ts rgs o m m (HR ts rgs Eg) Hdf Ho); [|intros; reflexivity].
    intros i Hi. destruct (HR ts rgs Eg) as (_ & _ & _ & _ & _ & _ & _ & Hb). destruct (Hb i Hi) as (b & Eb & _ & Wb).
    split; [exists b; exact Eb | exact Wb].
  - exact (regions_sep_mset_same rho M ts rgs _ Eg (same_dir_drop_below rgs o) Hsep).
Qed.

End HookKit.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mem_check (f : Z -> region -> bool) (M : mem) : bool :=
  iall (fun _ : region => false) (imapo (fun k v => if f k v then None else Some v) M 0 1).

Lemma mem_check_ok (f : Z -> region -> bool) (M : mem) : mem_check f M = true ->
  forall t rg, mget M t = Some rg -> f (to_Z t) rg = true.
Proof.
  intros Hc t rg G. unfold mget in G. destruct (t <? TAGLIM)%uint63 eqn:Et; [|discriminate]. apply ltb_spec in Et.
  destruct (f (to_Z t) rg) eqn:Ef; [reflexivity|]. exfalso.
  pose proof (iget_imapo (fun k v => if f k v then None else Some v) TAGD M 0 1 t) as E. rewrite G in E.
  pose proof (to_Z_bounded t) as Bt. rewrite Z.add_0_l, Z.mul_1_l in E. rewrite Z.mod_small in E by (rewrite <- TAGLIM_Z; lia).
  rewrite Ef in E. pose proof (iall_iget (fun _ : region => false) TAGD _ t rg Hc E). discriminate.
Qed.

Section Build.
Variable segs : list Segment.

Lemma Rmem_empty (rho : valuation) (m : word -> option byte) : Rmem segs rho IEmpty m.
Proof.
  split.
  - intros t rg G. unfold mget in G. destruct (_ <? _)%uint63; [rewrite iget_empty in G|]; discriminate.
  - intros t1 t2 r1 r2 G. unfold mget in G. destruct (_ <? _)%uint63; [rewrite iget_empty in G|]; discriminate.
Qed.

(* [comment removed for export] *)
Definition all_below (rho : valuation) (M : mem) (bound : Z) : Prop :=
  forall t rg, mget M t = Some rg -> rbase rho t rg + to_Z (rg_size rg) <= bound.

Lemma all_below_empty (rho : valuation) (bound : Z) : all_below rho IEmpty bound.
Proof. intros t rg G. unfold mget in G. destruct (_ <? _)%uint63; [rewrite iget_empty in G|]; discriminate. Qed.

Lemma Rmem_add (rho : valuation) (M : mem) (t : int) (rg : region) (m : word -> option byte) (bound bound' : Z) :
  Rmem segs rho M m -> all_below rho M bound -> mget M t = None -> to_Z t < to_Z TAGLIM ->
  region_ok segs rho t rg m -> bound <= rbase rho t rg -> rbase rho t rg + to_Z (rg_size rg) <= bound' ->
  Rmem segs rho (mset M t rg) m /\ all_below rho (mset M t rg) bound'.
Proof.
  intros [HR Hsep] Hb Hfresh Ht Hok Hlo Hhi. pose proof (to_Z_bounded (rg_size rg)) as Bs. split; [split|].
  - intros t2 rg2 G. destruct (mget_mset_cases M t t2 rg rg2 Ht G) as [[-> ->]|[_ G2]]; [exact Hok | exact (HR t2 rg2 G2)].
  - apply (regions_sep_new rho M t rg Hsep Hfresh Ht). intros t2 rg2 G2. right. specialize (Hb t2 rg2 G2). lia.
  - intros t2 rg2 G. destruct (mget_mset_cases M t t2 rg rg2 Ht G) as [[-> ->]|[_ G2]]; [exact Hhi|]. specialize (Hb t2 rg2 G2). lia.
Qed.

(* [comment removed for export] *)
Lemma region_ok_of_bytes (rho : valuation) (t : int) (rg : region) (m : word -> option byte) (bs : list byte) :
  0 < rbase rho t rg -> rbase rho t rg + to_Z (rg_size rg) < two63 -> to_Z (rg_size rg) < 2 ^ 62 ->
  to_Z (rg_size rg) <= 8 * 2 ^ Z.of_nat (rg_d rg) -> Z.of_nat (rg_d rg) <= 59 -> to_Z (rg_al rg) < 63 -> rbase rho t rg mod 2 ^ to_Z (rg_al rg) = 0 ->
  Z.of_nat (length bs) = to_Z (rg_size rg) ->
  (forall i, (i < length bs)%nat -> mrd segs m (wa (rbase rho t rg + Z.of_nat i)) = nth_error bs i) ->
  (rg_wr rg = true -> forall i, 0 <= i < to_Z (rg_size rg) -> wview segs m (wa (rbase rho t rg + i)) <> None) ->
  (forall i b, nth_error bs i = Some b -> kb_ok rho (rg_kb segs rg (Z.of_nat i)) b) ->
  region_ok segs rho t rg m.
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 Hl Hb Hw Hk. unfold region_ok. split; [split; [lia | left; exact H0]|]. repeat (split; [assumption|]).
  intros i Hi. specialize (Hb (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in Hb by lia.
  destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:E; [|apply nth_error_None in E; lia].
  exists b. split; [exact Hb|]. split; [|intros Hwr; exact (Hw Hwr i Hi)].
  specialize (Hk _ _ E). rewrite Z2Nat.id in Hk by lia. exact Hk.
Qed.

End Build.

(* [comment removed for export] *)
Lemma clobber_stack_inv (S : sstate) (M M' : mem) : clobber_stack S M = Some M' ->
  exists ts o rgs, rget S X2 = VP ts o /\ wh o = false /\ mget M ts = Some rgs /\ rg_abs rgs = None /\ rg_dflt rgs = DUnk
                   /\ to_Z (wl o) mod 16 = 0 /\ 16384 <= to_Z (wl o) <= to_Z (rg_size rgs) /\ rg_wr rgs = true
                   /\ M' = mset M ts (drop_below rgs (wl o)).
Proof.
  unfold clobber_stack. intros H. destruct (rget S X2) as [|ts o| |] eqn:E2; try discriminate. destruct (wh o) eqn:Eh; [discriminate|].
  destruct (mget M ts) as [rgs|] eqn:Eg; [|discriminate]. destruct (rg_abs rgs) eqn:Ea; [discriminate|].
  destruct (rg_dflt rgs) eqn:Ed; try discriminate.
  destruct ((wl o land 15 =? 0)%uint63 && (HK_STACK <=? wl o)%uint63 && (wl o <=? rg_size rgs)%uint63 && rg_wr rgs) eqn:Ec; [|discriminate].
  apply andb_prop in Ec as [Ec Ew]. apply andb_prop in Ec as [Ec E3]. apply andb_prop in Ec as [E1 E2'].
  apply Uint63.eqb_spec in E1. apply leb_spec in E2', E3. change (to_Z HK_STACK) with 16384 in E2'.
  injection H as <-. exists ts, o, rgs.
  assert (E16 : to_Z (wl o) mod 16 = 0).
  { pose proof (f_equal to_Z E1) as E. rewrite land_spec' in E. change (to_Z 15%uint63) with (Z.ones 4) in E.
    rewrite Z.land_ones in E by lia. exact E. }
  repeat split; first [reflexivity | assumption | lia].
Qed.

Lemma hk_return_inv (S S' : sstate) (res : hval) (M : mem) (nx : int) : hk_return S res M nx = Some S' ->
  exists ra M', rget S X1 = VC ra /\ clobber_stack S M = Some M' /\ s_resv S = RNone
                /\ S' = SS (w_and ra w_notone) (rf_set (havoc_caller_saved (s_regs S)) X10 res) RNone M' (s_abs S) nx.
Proof.
  unfold hk_return. intros H. destruct (rget S X1) as [ra| | |] eqn:E1; try discriminate.
  destruct (clobber_stack S M) as [M'|] eqn:Ec; [|discriminate]. destruct (s_resv S) eqn:Er; try discriminate.
  injection H as <-. exists ra, M'. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FinalRet.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma hx_ret_step (rho : valuation) (ic ic' : icache) (S : sstate) (ms : machine_state) :
  ic_ok segs ic -> R segs rho S ms -> hx_fetch segs ic (s_pc S) = Some (DJalr X0 X1 w_zero, ic') ->
  exists ms', mstep segs ms ms'
              /\ ms' = MS (ms_regs ms) (ms_fregs ms) (ret_pc (Sem.rget (core_of ms) (Z_to_bv 5 1))) (ms_fcsr ms) (ms_resv ms) (ms_mem ms) (ms_rom ms).
Proof.
  intros Hic HR Hf. destruct (hx_fetch_sound segs ic ic' (s_pc S) _ Hic Hf) as (_ & w & i & Hfw & Hec & Hdec & Hpre).
  pose proof HR as (Hsvc & Hpc & _). rewrite <- Hpc in Hfw.
  destruct i; cbn [predec] in Hpre; try discriminate.
  assert (Hrd : X0 = rix_of_reg rd) by (exact (f_equal (fun d => match d with DJalr a _ _ => a | _ => X0 end) Hpre)).
  assert (Hrs : X1 = rix_of_reg rs1) by (exact (f_equal (fun d => match d with DJalr _ a _ => a | _ => X0 end) Hpre)).
  assert (Himm : w_zero = w_of_bv (sext 64 imm)) by (exact (f_equal (fun d => match d with DJalr _ _ o => o | _ => w_zero end) Hpre)).
  clear Hpre.
  assert (Ex0 : is_x0 rd = true) by (apply rix_of_reg_X0; symmetry; exact Hrd).
  assert (Ers : rs1 = Z_to_bv 5 1) by (apply reg_lit; rewrite <- rix_of_reg_Z, <- Hrs; reflexivity).
  assert (Eimm : sext 64 imm = Z_to_bv 64 0).
  { rewrite <- (wbv_w_of_bv (sext 64 imm)), <- Himm. reflexivity. }
  eexists. split.
  - split; [exact Hsvc|]. rewrite (MS_eta ms Hsvc) at 1.
    rewrite (step_gen segs _ _ _ _ _ _ _ w _ 4 Hfw Hec Hdec). cbn [exec interp_eff lift_result]. reflexivity.
  - unfold Sem.rset. rewrite Ex0. unfold MS_of_core, Sem.with_pc, MS. cbn [c_regs c_fregs c_pc c_fcsr c_resv].
    subst rs1. rewrite Eimm. unfold ret_pc, core_of. f_equal.
    f_equal. apply bv_eq. rewrite bv_add_unsigned. change (bv_unsigned (Z_to_bv 64 0)) with 0. rewrite Z.add_0_r.
    apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

End FinalRet.
