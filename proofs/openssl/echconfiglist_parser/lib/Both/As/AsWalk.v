(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge Frame TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac nonneg_lit d := lazymatch (eval vm_compute in (andb (Z.leb 0 d) (Z.leb d 4096))) with true => d end.

Ltac addr_diff E A ::=
  lazymatch E with
  | Z.add ?X ?c1 =>
      lazymatch A with
      | Z.add X ?c2 => let c1 := zlit c1 in let c2 := zlit c2 in let d := eval vm_compute in (c1 - c2)%Z in nonneg_lit d
      | X => let c1 := zlit c1 in nonneg_lit c1
      | _ => let e := zlit E in let a := zlit A in let d := eval vm_compute in (e - a)%Z in nonneg_lit d
      end
  | _ =>
      lazymatch A with
      | Z.add E ?c2 => let c2 := zlit c2 in let d := eval vm_compute in (- c2)%Z in nonneg_lit d
      | E => constr:(0%Z)
      | _ => let e := zlit E in let a := zlit A in let d := eval vm_compute in (e - a)%Z in nonneg_lit d
      end
  end.

Lemma land_align32 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551584 = x - x mod 32.
Proof.
  intros x Hx. transitivity (Z.ldiff (Z.land x (Z.ones 64)) (Z.ones 5)).
  - rewrite Z.ldiff_land. rewrite <- Z.land_assoc. f_equal.
  - rewrite Z.land_ones, Z.mod_small by lia. rewrite Z.ldiff_ones_r by lia.
    rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2^5) with 32. Z.div_mod_to_equations. lia.
Qed.

Lemma land_m8 : forall y, 0 <= y < 2^64 -> Z.land y 18446744073709551608 = 8 * (y / 8).
Proof.
  intros y Hy. transitivity (Z.ldiff (Z.land y (Z.ones 64)) (Z.ones 3)).
  - rewrite Z.ldiff_land. rewrite <- Z.land_assoc. f_equal.
  - rewrite Z.land_ones, Z.mod_small by lia. rewrite Z.ldiff_ones_r by lia.
    rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2^3) with 8. lia.
Qed.

Lemma land_7 : forall y, Z.land y 7 = y mod 8.
Proof. intros. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma rw_cells_C8_CB8 : forall segs m a v cs,
  rw_cells segs m a (C8 v :: cs) -> rw_cells segs m a (CB 8 (le8 v) :: cs).
Proof.
  intros segs m a v cs [[WF B] W]. split; [split|].
  - cbn in WF |- *. split; [apply (length_le8 v)| destruct WF as [_ WF]; exact WF].
  - cbn [cells_bytes cbytes] in *. exact B.
  - cbn [cells_size csize] in *. exact W.
Qed.

(* [comment removed for export] *)
Lemma rw_cells_C1_mrd : forall segs m a b cs, rw_cells segs m a (C1 b :: cs) -> mrd segs m (wa a) = Some b.
Proof.
  intros segs m a b cs [[WF (B0 & B1 & BB)] _]. specialize (BB 0%nat ltac:(cbn; lia)). cbn in BB.
  rewrite Z.add_0_r in BB. exact BB.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition wins_hi (W : list (Z * Z)) : Prop :=
  Forall (fun iv : Z * Z => (AIMG_TOP <= fst iv /\ snd iv <= ALOWSH_LO) \/ AHI_LO <= fst iv) W.

Lemma wins_hi_outside : forall W x, wins_hi W -> 0 <= x < AAPP_HI -> outside W (sh x).
Proof.
  induction W as [|[lo hi] W IH]; intros x HW Hx; cbn; [exact I|].
  inversion HW; subst. cbn in *. pose proof (sh_below_app x Hx).
  assert (ALOWSH_LO < sh x) by (unfold sh, ALOWSH_LO; rewrite ASHADOW_BASE_val; lia).
  split; [lia| apply IH; assumption].
Qed.

(* [comment removed for export] *)
Lemma wins_hi_disjoint : forall W a n, wins_hi W -> ALOWSH_LO <= a /\ a + n <= AHI_LO -> disjoint_from W a n.
Proof.
  induction W as [|[lo hi] W IH]; intros a n HW [Ha Hn]; cbn; [exact I|].
  inversion HW; subst. cbn in *. split; [lia| apply IH; [assumption| split; assumption]].
Qed.

Lemma sh_ge_lowsh : forall a, 0 <= a -> ALOWSH_LO <= sh a.
Proof. intros a Ha. unfold sh, ALOWSH_LO. rewrite ASHADOW_BASE_val. lia. Qed.

Lemma accessible_transport_hi : forall W m m' a n,
  accessible m a n -> munch W m m' -> wins_hi W -> accessible m' a n.
Proof.
  intros W m m' a n AC MU HW. eapply accessible_transport; [exact AC| exact MU|].
  destruct AC as (A0 & A1 & _). intros x Hx. apply wins_hi_outside; [exact HW| lia].
Qed.

Lemma addressable_transport_hi : forall W m m' A n,
  addressable m A n -> munch W m m' -> wmono asegs m m' -> A + n <= AAPP_HI -> wins_hi W -> addressable m' A n.
Proof.
  intros W m m' A n AD MU WM Htop HW. eapply addressable_transport; [exact AD| exact MU| exact WM|].
  destruct AD as (Hn & A0 & A8 & _). apply wins_hi_disjoint; [exact HW|]. split; [apply sh_ge_lowsh; lia| apply sh_nsh_high; lia].
Qed.

Lemma SHAD_transport_hi : forall W m m' A sbs,
  SHAD m A sbs -> munch W m m' -> wmono asegs m m' -> A + 8 * Z.of_nat (length sbs) <= AAPP_HI -> wins_hi W -> SHAD m' A sbs.
Proof.
  intros W m m' A sbs SD MU WM Htop HW. eapply SHAD_transport; [exact SD| exact MU| exact WM|].
  destruct SD as (A0 & A8 & _). apply wins_hi_disjoint; [exact HW|]. split; [apply sh_ge_lowsh; lia|].
  pose proof (sh_nsh_high A (8 * Z.of_nat (length sbs)) ltac:(lia) ltac:(lia) Htop) as K.
  unfold nsh in K. replace ((8 * Z.of_nat (length sbs) + 7) / 8) with (Z.of_nat (length sbs)) in K by (Z.div_mod_to_equations; lia). lia.
Qed.

Lemma shvis_transport_hi : forall W m m' lo hi,
  shvis m lo hi -> munch W m m' -> wmono asegs m m' -> 0 <= lo <= hi -> hi <= AAPP_HI -> wins_hi W -> shvis m' lo hi.
Proof.
  intros W m m' lo hi SV MU WM H0 Htop HW. eapply shvis_transport; [exact SV| exact MU| exact WM|].
  pose proof (hull_lo_le lo ltac:(lia)) as (L1 & L2 & L3).
  apply wins_hi_disjoint; [exact HW|]. split; [apply sh_ge_lowsh; lia|]. pose proof (hull_hi_ge hi ltac:(lia)) as (G1 & G2 & G3).
  assert (LE : hull_hi hi <= AAPP_HI) by (unfold AAPP_HI in *; Z.div_mod_to_equations; nia).
  pose proof (sh_mono _ _ LE) as K. unfold sh, AAPP_HI, AHI_LO in *. rewrite ASHADOW_BASE_val in *.
  change (2147450880 + 2^47 / 8) with 17594333495296 in K. lia.
Qed.

(* [comment removed for export] *)
Lemma accessible_read0_sr : forall m a n g,
  accessible m a n -> a <= g -> g mod 8 = 0 -> g + 8 <= a + n ->
  ov_read_bytes asegs m (Z_to_bv 64 (Z.shiftr g 3 + 2147450880)) 1 = Some [b8 0].
Proof.
  intros m a n g AC Hag Hg Hn.
  destruct (accessible_read1 m (g + 7) (accessible_sub _ _ _ (g + 7) 1 AC ltac:(lia) ltac:(lia) ltac:(lia))) as (v & V1 & OK & RD).
  assert (v = 0) as -> by (destruct OK as [->|OK]; [reflexivity| exfalso; Z.div_mod_to_equations; lia]).
  rewrite (sh_granule g 7 Hg ltac:(lia)) in RD.
  destruct AC as (A0 & _). rewrite <- (sh_shiftr g) in RD by lia. rewrite ASHADOW_BASE_val in RD. exact RD.
Qed.

(* [comment removed for export] *)
Lemma addressable_rd : forall m A n a w,
  addressable m A n -> A <= a -> 1 <= w -> a + w <= A + 8 * (n / 8) ->
  ov_read_bytes asegs m (Z_to_bv 64 (Z.shiftr a 3 + 2147450880)) 1 = Some [b8 0].
Proof.
  intros m A n a w T Ha Hw Hhi. pose proof T as [Hn0 (P0 & _ & _)].
  apply (addressable_read0_w m A n a w); [exact T| lia| exact Hw| exact Hhi|].
  rewrite <- sh_shiftr by lia. rewrite ASHADOW_BASE_val. reflexivity.
Qed.
