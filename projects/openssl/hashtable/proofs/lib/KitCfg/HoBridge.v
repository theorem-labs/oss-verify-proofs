(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.FX Require Import W64 ITrie FxSpec FxInstr FxState FxRel FxKind FxHandoff.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ioz (z : Z) : int := Uint63.of_Z z.
Lemma to_Z_ioz : forall z, 0 <= z < 2 ^ 63 -> to_Z (ioz z) = z.
Proof. intros z Hz. unfold ioz. rewrite of_Z_spec. apply Z.mod_small. change wB with (2 ^ 63). exact Hz. Qed.

Lemma u64z : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. exact Hz. Qed.

Lemma bv_add_Z : forall x y, bv_add (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x + y).
Proof.
  intros x y. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite <- Zplus_mod. reflexivity.
Qed.

Lemma bv_add_word_Z : forall (w : word) y, bv_add w (Z_to_bv 64 y) = Z_to_bv 64 (bv_unsigned w + y).
Proof. intros w y. rewrite <- (bv_add_Z (bv_unsigned w) y). f_equal. symmetry. apply Z_to_bv_bv_unsigned. Qed.

(* [comment removed for export] *)
Definition hcell (t : int) (off : Z) (n : nat) (v : Z) : hfact := HCell t (ioz off) (ioz (Z.of_nat n)) (w_of_Z v).
Definition hval (t : int) (off : Z) (tv : int) (z : Z) : hfact := HVal t (ioz off) (FV tv (w_of_Z z)).
Definition hopq (t : int) (off : Z) (tv : int) : hfact := HVal t (ioz off) (FV tv w_zero).
Definition hbytesf (t : int) (off : Z) (n : nat) (tv : int) : hfact := HBytes t (ioz off) (ioz (Z.of_nat n)) (FV tv w_zero).
Definition hzero (t : int) (off len : Z) : hfact := HZero t (ioz off) (ioz len).
Definition hwr (t : int) (off len : Z) : hfact := HWr t (ioz off) (ioz len).
Definition hclear (lo hi : Z) : hfact := HClear (ioz lo) (ioz hi).
Definition hreg (r : Z) (tv : int) (z : Z) : hfact := HReg (ioz r) (FV tv (w_of_Z z)).
Definition hregion (t : int) (lo len al : Z) : hfact := HRegion t (ioz lo) (ioz len) (ioz al).
Definition hdisj (t1 : int) (lo1 len1 : Z) (t2 : int) (lo2 len2 : Z) : hfact := HDisj t1 (ioz lo1) (ioz len1) t2 (ioz lo2) (ioz len2).

Section Bridge.
  Variable segs : list Segment.
  Variable rho : int -> word.
  Variables (R : bvmap 5 word) (pc : word) (M : word -> option byte).
  Let ms : machine_state := mkst R pc M (seg_rom segs).

  (* [comment removed for export] *)
  Lemma rview_rdn : forall n a bs, rdn segs M a n = Some bs ->
    forall j, (j < n)%nat -> rview segs M (aoff a j) = nth_error bs j.
  Proof.
    induction n as [|n IH]; intros a bs H j Hj; [lia|].
    cbn [rdn] in H.
    destruct (match M a with Some b => Some b | None => seg_rom segs a end) as [b|] eqn:E; [|discriminate].
    destruct (rdn segs M (a + 1)%bv n) as [rest|] eqn:E2; [|discriminate]. injection H as <-.
    destruct j as [|j].
    - rewrite aoff_0. cbn [nth_error]. unfold rview. unfold seg_rom in E. exact E.
    - cbn [nth_error]. rewrite <- aoff_S. apply (IH _ _ E2). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma adr_abs : forall z, rho 0%uint63 = Z_to_bv 64 0 -> adr rho 0 z = Z_to_bv 64 z.
  Proof. intros z H0. unfold adr. rewrite H0, bv_add_Z. reflexivity. Qed.

  Lemma adr_tag : forall t base z, rho t = Z_to_bv 64 base -> adr rho t z = Z_to_bv 64 (base + z).
  Proof. intros t base z Ht. unfold adr. rewrite Ht, bv_add_Z. reflexivity. Qed.

  Lemma aoff_Z : forall a j, aoff (Z_to_bv 64 a) j = Z_to_bv 64 (a + Z.of_nat j).
  Proof. intros a j. unfold aoff. apply bv_add_Z. Qed.

  (* [comment removed for export] *)
  Lemma hcell_of_rdn : forall t base a off (n : nat) (v : Z) (w : w64),
    rho t = Z_to_bv 64 base -> a = base + to_Z off ->
    rdn segs M (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 v)) ->
    (n <= 8)%nat -> 0 <= v < 2 ^ 64 -> wZ w = v ->
    hholds segs rho ms (HCell t off (ioz (Z.of_nat n)) w).
  Proof.
    intros t base a off n v w Ht -> Hr Hn Hv Hw. cbn [hholds]. rewrite to_Z_ioz by lia. rewrite Nat2Z.id.
    intros j Hj. rewrite (adr_tag t base _ Ht). rewrite Z.add_assoc, <- aoff_Z.
    change (ms_mem ms) with M. rewrite (rview_rdn n _ _ Hr j Hj).
    unfold word_to_le_bytes, w_bytes. rewrite u64z by exact Hv. rewrite Hw.
    rewrite !Z_to_le_bytes_nth by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma hval_of_rdn : forall t base a off (z : Z) (fv : fval),
    rho t = Z_to_bv 64 base -> a = base + to_Z off ->
    rdn segs M (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 z)) ->
    dv rho fv = Z_to_bv 64 z ->
    hholds segs rho ms (HVal t off fv).
  Proof.
    intros t base a off z fv Ht -> Hr Hd. cbn [hholds]. intros j Hj.
    rewrite (adr_tag t base _ Ht). rewrite Z.add_assoc, <- aoff_Z.
    change (ms_mem ms) with M. rewrite (rview_rdn 8 _ _ Hr j Hj). rewrite Hd. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma hzero_of_overlay : forall t base a off len,
    rho t = Z_to_bv 64 base -> a = base + to_Z off ->
    (forall i, 0 <= i < to_Z len -> M (Z_to_bv 64 (a + i)) = Some (Z_to_bv 8 0)) ->
    hholds segs rho ms (HZero t off len).
  Proof.
    intros t base a off len Ht -> Hz. cbn [hholds]. intros j Hj.
    rewrite (adr_tag t base _ Ht). change (ms_mem ms) with M. unfold rview.
    rewrite Z.add_assoc. rewrite (Hz j Hj). reflexivity.
  Qed.

  Lemma hclear_of_overlay : forall lo hi,
    (forall i, to_Z lo <= i < to_Z hi -> M (Z_to_bv 64 i) = None) ->
    hholds segs rho ms (HClear lo hi).
  Proof. intros lo hi H. cbn [hholds]. exact H. Qed.

  (* [comment removed for export] *)
  Lemma hwr_of_defined : forall t base a off len,
    rho t = Z_to_bv 64 base -> a = base + to_Z off ->
    (forall i, 0 <= i < to_Z len -> M (Z_to_bv 64 (a + i)) <> None) ->
    hholds segs rho ms (HWr t off len).
  Proof.
    intros t base a off len Ht -> Hd. cbn [hholds]. intros j Hj.
    rewrite (adr_tag t base _ Ht). change (ms_mem ms) with M. rewrite Z.add_assoc.
    specialize (Hd j Hj). unfold RiscvSemantics.wview. destruct (M (Z_to_bv 64 (base + to_Z off + j))); [discriminate | contradiction].
  Qed.

  Lemma hwr_of_store_ok : forall t base a off len,
    rho t = Z_to_bv 64 base -> a = base + to_Z off ->
    (forall i, 0 <= i < to_Z len -> store_ok segs M (Z_to_bv 64 (a + i)) 1 = true) ->
    hholds segs rho ms (HWr t off len).
  Proof.
    intros t base a off len Ht -> Hs. cbn [hholds]. intros j Hj.
    rewrite (adr_tag t base _ Ht). change (ms_mem ms) with M. rewrite Z.add_assoc.
    specialize (Hs j Hj). cbn [store_ok] in Hs.
    destruct (RiscvSemantics.wview segs M (Z_to_bv 64 (base + to_Z off + j))); [discriminate | discriminate Hs].
  Qed.

  (* [comment removed for export] *)
  Lemma dv_plain : forall t w, to_Z t < 2 ^ 60 -> dv rho (FV t w) = bv_add (rho t) (wbv w).
  Proof. intros t w Ht. unfold dv. cbn [vtag vw]. rewrite (fk_vkind_plain t Ht), (fk_vbase_plain t Ht). reflexivity. Qed.

  Lemma dv_tag : forall t base z, to_Z t < 2 ^ 60 -> rho t = Z_to_bv 64 base -> dv rho (FV t (w_of_Z z)) = Z_to_bv 64 (base + z).
  Proof. intros t base z Hp Ht. rewrite dv_plain by exact Hp. rewrite Ht, wbv_w_of_Z, bv_add_Z. reflexivity. Qed.

  Lemma dv_opaque : forall t, to_Z t < 2 ^ 60 -> dv rho (FV t w_zero) = rho t.
  Proof.
    intros t Hp. rewrite dv_plain by exact Hp. change (wbv w_zero) with (Z_to_bv 64 0). rewrite bv_add_word_Z, Z.add_0_r.
    apply Z_to_bv_bv_unsigned.
  Qed.

  (* [comment removed for export] *)
  Lemma hcell_ok : forall t base a off n v,
    rho t = Z_to_bv 64 base -> a = base + off -> 0 <= off < 2 ^ 63 -> (n <= 8)%nat -> 0 <= v < 2 ^ 64 ->
    rdn segs M (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 v)) ->
    hholds segs rho ms (hcell t off n v).
  Proof.
    intros t base a off n v Ht Ha Hoff Hn Hv Hr. unfold hcell.
    apply (hcell_of_rdn t base a (ioz off) n v (w_of_Z v) Ht); [rewrite to_Z_ioz by exact Hoff; exact Ha | exact Hr | exact Hn | exact Hv |].
    rewrite wZ_w_of_Z. apply Z.mod_small. exact Hv.
  Qed.

  Lemma hval_ok : forall t base a off tv vbase z zz,
    rho t = Z_to_bv 64 base -> a = base + off -> 0 <= off < 2 ^ 63 ->
    rho tv = Z_to_bv 64 vbase -> to_Z tv < 2 ^ 60 -> zz = vbase + z ->
    rdn segs M (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 zz)) ->
    hholds segs rho ms (hval t off tv z).
  Proof.
    intros t base a off tv vbase z zz Ht Ha Hoff Htv Hp -> Hr. unfold hval.
    apply (hval_of_rdn t base a (ioz off) (vbase + z) _ Ht); [rewrite to_Z_ioz by exact Hoff; exact Ha | exact Hr |].
    apply dv_tag; [exact Hp | exact Htv].
  Qed.

  Lemma hopq_ok : forall t base a off tv zz,
    rho t = Z_to_bv 64 base -> a = base + off -> 0 <= off < 2 ^ 63 -> rho tv = Z_to_bv 64 zz -> to_Z tv < 2 ^ 60 ->
    rdn segs M (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 zz)) ->
    hholds segs rho ms (hopq t off tv).
  Proof.
    intros t base a off tv zz Ht Ha Hoff Htv Hp Hr. unfold hopq.
    apply (hval_of_rdn t base a (ioz off) zz _ Ht); [rewrite to_Z_ioz by exact Hoff; exact Ha | exact Hr |].
    rewrite dv_opaque by exact Hp. exact Htv.
  Qed.

  (* [comment removed for export] *)
  Lemma hbytesf_ok : forall t base a off (n : nat) tv z,
    rho t = Z_to_bv 64 base -> a = base + off -> 0 <= off < 2 ^ 63 -> (n <= 8)%nat -> 0 <= z < 2 ^ 64 ->
    rho tv = Z_to_bv 64 z -> to_Z tv < 2 ^ 60 ->
    rdn segs M (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 z)) ->
    hholds segs rho ms (hbytesf t off n tv).
  Proof.
    intros t base a off n tv z Ht -> Hoff Hn Hz Htv Hp Hr. unfold hbytesf. cbn [hholds].
    rewrite !to_Z_ioz by lia. rewrite Nat2Z.id. intros j Hj.
    rewrite (adr_tag t base _ Ht). rewrite Z.add_assoc, <- aoff_Z.
    change (ms_mem ms) with M. rewrite (rview_rdn n _ _ Hr j Hj). rewrite dv_opaque by exact Hp. rewrite Htv.
    unfold word_to_le_bytes, wbytes8. rewrite !Z_to_le_bytes_nth by lia. reflexivity.
  Qed.

  Lemma hzero_ok : forall t base a off len,
    rho t = Z_to_bv 64 base -> a = base + off -> 0 <= off < 2 ^ 63 -> 0 <= len < 2 ^ 63 ->
    (forall i, 0 <= i < len -> M (Z_to_bv 64 (a + i)) = Some (Z_to_bv 8 0)) ->
    hholds segs rho ms (hzero t off len).
  Proof.
    intros t base a off len Ht Ha Hoff Hlen Hz. unfold hzero.
    apply (hzero_of_overlay t base a (ioz off) (ioz len) Ht); [rewrite to_Z_ioz by exact Hoff; exact Ha |].
    rewrite to_Z_ioz by exact Hlen. exact Hz.
  Qed.

  Lemma hwr_ok_defined : forall t base a off len,
    rho t = Z_to_bv 64 base -> a = base + off -> 0 <= off < 2 ^ 63 -> 0 <= len < 2 ^ 63 ->
    (forall i, 0 <= i < len -> M (Z_to_bv 64 (a + i)) <> None) ->
    hholds segs rho ms (hwr t off len).
  Proof.
    intros t base a off len Ht Ha Hoff Hlen Hd. unfold hwr.
    apply (hwr_of_defined t base a (ioz off) (ioz len) Ht); [rewrite to_Z_ioz by exact Hoff; exact Ha |].
    rewrite to_Z_ioz by exact Hlen. exact Hd.
  Qed.

  Lemma hwr_ok_store : forall t base a off len,
    rho t = Z_to_bv 64 base -> a = base + off -> 0 <= off < 2 ^ 63 -> 0 <= len < 2 ^ 63 ->
    (forall i, 0 <= i < len -> store_ok segs M (Z_to_bv 64 (a + i)) 1 = true) ->
    hholds segs rho ms (hwr t off len).
  Proof.
    intros t base a off len Ht Ha Hoff Hlen Hs. unfold hwr.
    apply (hwr_of_store_ok t base a (ioz off) (ioz len) Ht); [rewrite to_Z_ioz by exact Hoff; exact Ha |].
    rewrite to_Z_ioz by exact Hlen. exact Hs.
  Qed.

  Lemma hclear_ok : forall lo hi, 0 <= lo < 2 ^ 63 -> 0 <= hi < 2 ^ 63 ->
    (forall i, lo <= i < hi -> M (Z_to_bv 64 i) = None) -> hholds segs rho ms (hclear lo hi).
  Proof. intros lo hi Hlo Hhi H. unfold hclear. apply hclear_of_overlay. rewrite !to_Z_ioz by assumption. exact H. Qed.

  (* [comment removed for export] *)
  Lemma hreg_of_getr : forall (r : reg) (fv : fval),
    getr R r = dv rho fv -> hholds segs rho ms (HReg (ireg r) fv).
  Proof.
    intros r fv H. cbn [hholds]. intros rr Hrr.
    assert (rr = r).
    { unfold ireg in Hrr. apply bv_eq.
      pose proof (bv_unsigned_in_range _ rr) as H1. pose proof (bv_unsigned_in_range _ r) as H2.
      change (bv_modulus 5) with 32 in H1, H2.
      apply (f_equal to_Z) in Hrr. rewrite !of_Z_spec in Hrr. change wB with (2 ^ 63) in Hrr.
      rewrite !Z.mod_small in Hrr by lia. exact Hrr. }
    subst rr. rewrite <- H. unfold Sem.rget, getr, is_x0, bv_eqb, core_of, ms, mkst. cbn [c_regs ms_regs].
    change (bv_unsigned (0%bv : bv 5)) with 0. destruct (bv_unsigned r =? 0); reflexivity.
  Qed.
  Lemma hreg_ok : forall (r : reg) tv vbase z zz,
    rho tv = Z_to_bv 64 vbase -> to_Z tv < 2 ^ 60 -> zz = vbase + z -> getr R r = Z_to_bv 64 zz ->
    hholds segs rho ms (hreg (bv_unsigned r) tv z).
  Proof.
    intros r tv vbase z zz Htv Hp -> Hg. unfold hreg. change (ioz (bv_unsigned r)) with (ireg r).
    apply hreg_of_getr. rewrite Hg. symmetry. apply dv_tag; [exact Hp | exact Htv].
  Qed.

  Lemma hreg_opaque_ok : forall (r : reg) tv, to_Z tv < 2 ^ 60 -> rho tv = getr R r -> hholds segs rho ms (HReg (ireg r) (FV tv w_zero)).
  Proof. intros r tv Hp H. apply hreg_of_getr. rewrite dv_opaque by exact Hp. symmetry. exact H. Qed.

  Lemma hregion_ok : forall t base lo len al,
    rho t = Z_to_bv 64 base -> to_Z t < 2 ^ 60 -> 0 <= base -> 0 <= lo < 2 ^ 62 -> 0 <= len <= 2 ^ 62 -> 0 <= al < 64 ->
    base + len < 2 ^ 63 -> 0 < base + lo -> base mod 2 ^ al = 0 ->
    hholds segs rho ms (hregion t lo len al).
  Proof.
    intros t base lo len al Ht Hp Hb Hlo Hlen Hal Hnw Hpos Hmod. unfold hregion. cbn [hholds]. unfold region_ok. cbn [rg_len rg_lo rg_align rg_clo rg_chi].
    rewrite !to_Z_ioz by lia. rewrite Ht, u64z by lia. change (to_Z clo_dflt) with 0. change (to_Z chi_dflt) with (2 ^ 63 - 1).
    repeat split; try lia; try exact Hmod.
  Qed.

  Lemma hdisj_ok : forall t1 b1 lo1 len1 t2 b2 lo2 len2,
    rho t1 = Z_to_bv 64 b1 -> rho t2 = Z_to_bv 64 b2 -> 0 <= b1 < 2 ^ 64 -> 0 <= b2 < 2 ^ 64 ->
    0 <= lo1 < 2 ^ 63 -> 0 <= len1 < 2 ^ 63 -> 0 <= lo2 < 2 ^ 63 -> 0 <= len2 < 2 ^ 63 ->
    (b1 + len1 <= b2 + lo2 \/ b2 + len2 <= b1 + lo1) ->
    hholds segs rho ms (hdisj t1 lo1 len1 t2 lo2 len2).
  Proof.
    intros t1 b1 lo1 len1 t2 b2 lo2 len2 H1 H2 Hb1 Hb2 A B C D H. unfold hdisj. cbn [hholds].
    rewrite !to_Z_ioz by lia. rewrite H1, H2, !u64z by lia. exact H.
  Qed.
End Bridge.
