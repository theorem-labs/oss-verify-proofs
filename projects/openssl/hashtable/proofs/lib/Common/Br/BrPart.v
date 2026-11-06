(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.FX Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxImage FxHandoff.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec AsanAcct AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Br Require Import BrEnv BrMem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section Part.
Variable segs : list Segment.
Variable IM : fimage.
Variable rho : int -> word.
Variable M : itrie region.
Variable mem : word -> option byte.
Hypothesis Hrho0 : rho 0%uint63 = Z_to_bv 64 0.
Hypothesis HMem : mem_ok segs IM rho M mem.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition slotsP (t : int) (o : Z) : option slots :=
  if (0 <=? o) && (o <? b62z) then
    match iget t M with
    | Some rg =>
        if (o / 8 * 8 + 8 <=? to_Z (rg_len rg)) then
          let oi := of_Z o in
          let pn := (oi >> 12)%uint63 in
          match page_at IM rg t pn with
          | Some p => Some (slots_at IM p pn ((oi land 4095) >> 3)%uint63)
          | None => None
          end
        else None
    | None => None
    end
  else None.

Lemma slotsP_sound t o sls :
  slotsP t o = Some sls ->
  exists rg, iget t M = Some rg /\ to_Z (rg_lo rg) <= o / 8 * 8 /\ o / 8 * 8 + 8 <= to_Z (rg_len rg) /\ 0 <= o
    /\ slots_val rho sls (fun j => rview segs mem (adr rho t (o / 8 * 8 + Z.of_nat j))).
Proof.
  unfold slotsP. intros Hc.
  destruct ((0 <=? o) && (o <? b62z)) eqn:Eo; [|discriminate].
  apply andb_prop in Eo as [E0 E62]. apply Z.leb_le in E0. apply Z.ltb_lt in E62. unfold b62z in E62.
  destruct (iget t M) as [rg|] eqn:Hg; [|discriminate].
  destruct (o / 8 * 8 + 8 <=? to_Z (rg_len rg)) eqn:Eend; [|discriminate]. apply Z.leb_le in Eend.
  set (oi := of_Z o) in *.
  assert (Hoi : to_Z oi = o) by (apply of_Z_small; lia).
  destruct (page_at IM rg t (oi >> 12)%uint63) as [p|] eqn:Hp; [|discriminate].
  injection Hc as <-.
  assert (Hpn : to_Z (oi >> 12)%uint63 = o / 4096) by (rewrite to_Z_lsr12, Hoi; reflexivity).
  assert (Hpn50 : to_Z (oi >> 12)%uint63 < 2 ^ 50).
  { rewrite Hpn. apply Z.div_lt_upper_bound; lia. }
  destruct (proj1 HMem t rg Hg) as [_ Hpages]. destruct (Hpages _ p Hpn50 Hp) as (Hpok & Hlo & _ & _).
  assert (Hci : to_Z ((oi land 4095) >> 3)%uint63 = (o mod 4096) / 8).
  { rewrite to_Z_lsr3, to_Z_land4095, Hoi. reflexivity. }
  pose proof (cell_index_range o E0) as Hcr.
  assert (Hcl : 0 <= to_Z ((oi land 4095) >> 3)%uint63 < clim rg (oi >> 12)%uint63).
  { rewrite Hci. apply clim_intro; [exact Hcr|]. rewrite Hpn. clear - Eend E0. Z.div_mod_to_equations. lia. }
  exists rg. split; [reflexivity|]. rewrite Hpn in Hlo.
  split; [clear - Hlo E0; Z.div_mod_to_equations; lia|]. split; [exact Eend|]. split; [exact E0|].
  pose proof (slots_at_sound segs IM rho Hrho0 mem t _ _ p _ Hpok Hcl) as Hs.
  eapply slots_val_ext; [|exact Hs]. intros j Hj. unfold cell_view. rewrite Hpn, Hci.
  f_equal. f_equal. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint pages_wrP (rg : region) (t pn : int) (k : nat) : bool :=
  match k with
  | O => true
  | S k' => match page_at IM rg t pn with Some p => pg_wr p | None => false end
            && pages_wrP rg t (pn + 1)%uint63 k'
  end.

Lemma pages_wrP_spec rg t : forall k pn,
  to_Z pn + Z.of_nat k <= 2 ^ 50 ->
  pages_wrP rg t pn k = true ->
  forall q, to_Z pn <= q < to_Z pn + Z.of_nat k -> exists p, page_at IM rg t (of_Z q) = Some p /\ pg_wr p = true.
Proof.
  induction k as [|k IH]; intros pn Hb Hw q Hq; [lia|].
  cbn [pages_wrP] in Hw. apply andb_prop in Hw as [Hp0 Hrest]. pose proof (i63_range pn) as Hpn.
  destruct (Z.eq_dec q (to_Z pn)) as [->|Hne].
  - rewrite of_to_Z. destruct (page_at IM rg t pn) as [p|]; [|discriminate]. exists p. split; [reflexivity | exact Hp0].
  - assert (E1 : to_Z (pn + 1)%uint63 = to_Z pn + 1).
    { rewrite add_spec. change (to_Z 1) with 1. apply Z.mod_small. rewrite i63_wB. lia. }
    apply (IH (pn + 1)%uint63 ltac:(lia) Hrest q). lia.
Qed.

Definition wr_rangeP (t : int) (o n : Z) : bool :=
  match iget t M with
  | Some rg =>
      (0 <=? o) && (0 <? n) && (to_Z (rg_lo rg) <=? o) && (o + n <=? to_Z (rg_len rg)) && (to_Z (rg_len rg) mod 8 =? 0)
      && (if ((o + n - 1) / 4096 - o / 4096 + 1 <=? 4194304)
          then pages_wrP rg t (of_Z (o / 4096)) (Z.to_nat ((o + n - 1) / 4096 - o / 4096 + 1)) else false)
  | None => false
  end.

Lemma wr_rangeP_sound t o n : wr_rangeP t o n = true ->
  exists rg, iget t M = Some rg /\ to_Z (rg_lo rg) <= o /\ o + n <= to_Z (rg_len rg)
    /\ forall x, o <= x < o + n -> wview segs mem (adr rho t x) <> None.
Proof.
  unfold wr_rangeP. destruct (iget t M) as [rg|] eqn:Hg; [|discriminate]. intros Hc.
  apply andb_prop in Hc as [Hc Hpg]. apply andb_prop in Hc as [Hc Hm8]. apply andb_prop in Hc as [Hc Hhi].
  apply andb_prop in Hc as [Hc Hlo]. apply andb_prop in Hc as [Ho0 Hn0].
  apply Z.leb_le in Ho0, Hlo, Hhi. apply Z.ltb_lt in Hn0. apply Z.eqb_eq in Hm8.
  destruct ((o + n - 1) / 4096 - o / 4096 + 1 <=? 4194304) eqn:Ecnt; [|discriminate]. apply Z.leb_le in Ecnt.
  exists rg. split; [reflexivity|]. split; [exact Hlo|]. split; [exact Hhi|].
  intros x Hx.
  destruct (proj1 HMem t rg Hg) as [Hrok Hpages]. destruct Hrok as (_ & Hl62 & _).
  assert (Ho4 : 0 <= o / 4096 < 2 ^ 50) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (Epn : to_Z (of_Z (o / 4096)) = o / 4096) by (apply of_Z_small; lia).
  set (q := x / 4096).
  assert (Hq : o / 4096 <= q <= (o + n - 1) / 4096) by (unfold q; split; apply Z.div_le_mono; lia).
  assert (Hk1 : to_Z (of_Z (o / 4096)) + Z.of_nat (Z.to_nat ((o + n - 1) / 4096 - o / 4096 + 1)) <= 2 ^ 50) by (rewrite Epn, Z2Nat.id by lia; lia).
  assert (Hk2 : to_Z (of_Z (o / 4096)) <= q < to_Z (of_Z (o / 4096)) + Z.of_nat (Z.to_nat ((o + n - 1) / 4096 - o / 4096 + 1))) by (rewrite Epn, Z2Nat.id by lia; lia).
  destruct (pages_wrP_spec rg t _ (of_Z (o / 4096)) Hk1 Hpg q Hk2) as (p & Hp & Hwr).
  assert (Eq : to_Z (of_Z q) = q) by (apply of_Z_small; unfold q in *; lia).
  destruct (Hpages (of_Z q) p ltac:(rewrite Eq; lia) Hp) as ((Hwv & _) & _ & _ & _).
  specialize (Hwv Hwr (x - q * 4096)). rewrite Eq in Hwv.
  replace (q * 4096 + (x - q * 4096)) with x in Hwv by lia. apply Hwv.
  unfold clim. rewrite Eq. unfold q in *. clear - Hx Hhi Hm8 Ho0. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis HIM : image_ok segs IM.
Hypothesis HWR : image_wr_ok IM.

Fixpoint pages_segwr (pn : int) (k : nat) : bool :=
  match k with
  | O => true
  | S k' => if seg_wr_page IM pn then pages_segwr (pn + 1)%uint63 k' else false
  end.

Lemma pages_segwr_spec : forall k pn,
  to_Z pn + Z.of_nat k <= 2 ^ 50 -> pages_segwr pn k = true ->
  forall q, to_Z pn <= q < to_Z pn + Z.of_nat k -> seg_wr_page IM (of_Z q) = true.
Proof.
  induction k as [|k IH]; intros pn Hb Hw q Hq; [lia|].
  cbn [pages_segwr] in Hw. destruct (seg_wr_page IM pn) eqn:Ep; [|discriminate]. pose proof (i63_range pn) as Hpn.
  destruct (Z.eq_dec q (to_Z pn)) as [->|Hne]; [rewrite of_to_Z; exact Ep|].
  assert (E1 : to_Z (pn + 1)%uint63 = to_Z pn + 1).
  { rewrite add_spec. change (to_Z 1) with 1. apply Z.mod_small. rewrite i63_wB. lia. }
  apply (IH (pn + 1)%uint63 ltac:(lia) Hw q). lia.
Qed.

Lemma seg_wr_page_wview pn : to_Z pn < 2 ^ 50 -> seg_wr_page IM pn = true ->
  forall j, 0 <= j < 4096 -> wview segs mem (Z_to_bv 64 (to_Z pn * 4096 + j)) <> None.
Proof.
  intros Hpn Hw j Hj. unfold seg_wr_page in Hw.
  destruct (find_seg IM (pn << 12)%uint63) as [sg|] eqn:Hf; [|discriminate].
  pose proof (page_ok_image_init segs IM (fun _ => Z_to_bv 64 0) (fun _ => None) pn sg HIM HWR eq_refl Hpn Hf (fun _ _ => eq_refl)) as (Hwv & _).
  cbn [pg_wr] in Hwv. specialize (Hwv Hw j ltac:(lia)).
  unfold adr in Hwv. rewrite bv_add_0_Z_to_bv in Hwv.
  unfold wview in *. destruct (mem (Z_to_bv 64 (to_Z pn * 4096 + j))); [discriminate | exact Hwv].
Qed.

Definition seg_wr_range (t : int) (o n : Z) : bool :=
  if (t =? 0)%uint63 then
    match iget t M with
    | Some rg =>
        (0 <=? o) && (0 <? n) && (to_Z (rg_lo rg) <=? o) && (o + n <=? to_Z (rg_len rg)) && (o + n <? b62z)
        && (if ((o + n - 1) / 4096 - o / 4096 + 1 <=? 4194304)
            then pages_segwr (of_Z (o / 4096)) (Z.to_nat ((o + n - 1) / 4096 - o / 4096 + 1)) else false)
    | None => false
    end
  else false.

Lemma seg_wr_range_sound t o n : seg_wr_range t o n = true ->
  exists rg, iget t M = Some rg /\ to_Z (rg_lo rg) <= o /\ o + n <= to_Z (rg_len rg)
    /\ forall x, o <= x < o + n -> wview segs mem (adr rho t x) <> None.
Proof.
  unfold seg_wr_range. destruct (t =? 0)%uint63 eqn:Et; [|discriminate]. apply Uint63.eqb_spec in Et. subst t.
  destruct (iget 0%uint63 M) as [rg|] eqn:Hg; [|discriminate]. intros Hc.
  apply andb_prop in Hc as [Hc Hpg]. apply andb_prop in Hc as [Hc H62]. apply andb_prop in Hc as [Hc Hhi].
  apply andb_prop in Hc as [Hc Hlo]. apply andb_prop in Hc as [Ho0 Hn0].
  apply Z.leb_le in Ho0, Hlo, Hhi. apply Z.ltb_lt in Hn0, H62. unfold b62z in H62.
  destruct ((o + n - 1) / 4096 - o / 4096 + 1 <=? 4194304) eqn:Ecnt; [|discriminate].
  exists rg. split; [reflexivity|]. split; [exact Hlo|]. split; [exact Hhi|].
  intros x Hx.
  assert (Ho4 : 0 <= o / 4096 < 2 ^ 50) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (Epn : to_Z (of_Z (o / 4096)) = o / 4096) by (apply of_Z_small; lia).
  set (q := x / 4096).
  assert (Hq : o / 4096 <= q <= (o + n - 1) / 4096) by (unfold q; split; apply Z.div_le_mono; lia).
  assert (Hq50 : 0 <= q < 2 ^ 50) by (unfold q; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (Hk1 : to_Z (of_Z (o / 4096)) + Z.of_nat (Z.to_nat ((o + n - 1) / 4096 - o / 4096 + 1)) <= 2 ^ 50).
  { rewrite Epn, Z2Nat.id by lia. assert ((o + n - 1) / 4096 < 2 ^ 50) by (apply Z.div_lt_upper_bound; lia). lia. }
  assert (Hk2 : to_Z (of_Z (o / 4096)) <= q < to_Z (of_Z (o / 4096)) + Z.of_nat (Z.to_nat ((o + n - 1) / 4096 - o / 4096 + 1))) by (rewrite Epn, Z2Nat.id by lia; lia).
  pose proof (pages_segwr_spec _ (of_Z (o / 4096)) Hk1 Hpg q Hk2) as Hsw.
  assert (Eq : to_Z (of_Z q) = q) by (apply of_Z_small; lia).
  pose proof (seg_wr_page_wview (of_Z q) ltac:(rewrite Eq; lia) Hsw (x - q * 4096)) as Hwv. rewrite Eq in Hwv.
  replace (q * 4096 + (x - q * 4096)) with x in Hwv by lia.
  unfold adr. rewrite Hrho0, bv_add_0_Z_to_bv. apply Hwv. unfold q. clear - Hx Ho0. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Definition xwr2 (t : int) (o n : Z) : bool := if wr_rangeP t o n then true else seg_wr_range t o n.
Lemma xwr2_sound t o n : xwr2 t o n = true ->
  exists rg, iget t M = Some rg /\ to_Z (rg_lo rg) <= o /\ o + n <= to_Z (rg_len rg)
    /\ forall x, o <= x < o + n -> wview segs mem (adr rho t x) <> None.
Proof.
  unfold xwr2. destruct (wr_rangeP t o n) eqn:E1; [intros _; exact (wr_rangeP_sound t o n E1) | exact (seg_wr_range_sound t o n)].
Qed.

End Part.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section PartZero.
Variable segs : list Segment.
Variable IM : fimage.
Variable rho : int -> word.
Variable xv : nat -> word.
Variable xb : nat -> list byte.
Variable VT : vtab.
Variable M : itrie region.
Variable TL : ttab.
Variable XT : list (int * AX2.lin).
Variable mem : word -> option byte.
Hypothesis Hrho0 : rho 0%uint63 = Z_to_bv 64 0.
Hypothesis HMem : mem_ok segs IM rho M mem.
Hypothesis HTL : tl_ok VT M TL = true.
Hypothesis HXT : xt_ok rho xv xb VT XT.
Local Notation E := (env_of rho xv xb VT).
Variable H : word -> bool.
Variable visb : int -> Z -> Z -> bool.
Hypothesis visb_sound : forall t o n, visb t o n = true ->
  forall j, 0 <= j < n -> H (adr rho t (o + j)) = false.
Variable nosegb : int -> Z -> Z -> bool.
Hypothesis nosegb_sound : forall t o n, nosegb t o n = true ->
  forall j, 0 <= j < n -> mem (adr rho t (o + j)) <> None
                          \/ find_segment segs (bv_unsigned (adr rho t (o + j))) 1 = None.
Variable xslots : int -> Z -> option slots.
Hypothesis xslots_sound : forall t o sls, xslots t o = Some sls ->
  exists rg, iget t M = Some rg /\ to_Z (rg_lo rg) <= o / 8 * 8 /\ o / 8 * 8 + 8 <= to_Z (rg_len rg) /\ 0 <= o
    /\ slots_val rho sls (fun j => rview segs mem (adr rho t (o / 8 * 8 + Z.of_nat j))).

(* [comment removed for export] *)
Definition kzero_okP (a : AX2.saddr) (n : AX2.expr) : bool :=
  match n, aview VT M TL XT a with
  | AX2.ELit len, Some (t, o) =>
      let P := (o + len) / 4096 * 4096 in
      if (0 <=? o) && (o <? P) && (P <? o + len) && (o + len <? b62z) then
        range_zero IM M t o (P - o)
        && zero_bytes_b IM M xslots t P (Z.to_nat (o + len - P))
        && visb t o len && nosegb t o len
      else false
  | _, _ => false
  end.

Theorem kzeroP_sound a n :
  kzero_okP a n = true -> AX2S.kentry_ok segs E (mrestrict H mem) (AX2.KZero a n).
Proof.
  unfold kzero_okP. intros Hk. destruct n as [len| | | | | | |]; try discriminate.
  destruct (aview VT M TL XT a) as [[t o]|] eqn:Hav; [|discriminate].
  set (P := (o + len) / 4096 * 4096) in *.
  destruct ((0 <=? o) && (o <? P) && (P <? o + len) && (o + len <? b62z)) eqn:Hg0; [|discriminate].
  apply andb_prop in Hg0 as [Hg0 H62]. apply andb_prop in Hg0 as [Hg0 HP2]. apply andb_prop in Hg0 as [Ho0 HP1].
  apply Z.leb_le in Ho0. apply Z.ltb_lt in HP1, HP2, H62. unfold b62z in H62.
  apply andb_prop in Hk as [Hk Hns]. apply andb_prop in Hk as [Hk Hvis]. apply andb_prop in Hk as [Hrz Hzb].
  (* [comment removed for export] *)
  pose proof (zero_bytes_spec segs IM rho M mem Hrho0 HMem xslots xslots_sound t _ P ltac:(lia) Hzb) as Hsp.
  rewrite Z2Nat.id in Hsp by lia.
  destruct (Hsp (o + len - P - 1) ltac:(lia)) as (_ & rg & Hg & Hlen).
  (* [comment removed for export] *)
  unfold range_zero in Hrz. apply andb_prop in Hrz as [Hrz Hzp]. apply andb_prop in Hrz as [Hrz Hn8].
  apply andb_prop in Hrz as [Hrz Ho8]. apply andb_prop in Hrz as [Hrz _]. apply andb_prop in Hrz as [_ Hn0].
  apply Z.eqb_eq in Ho8, Hn8. rewrite Hg in Hzp.
  destruct ((o + (P - o)) / 4096 - o / 4096 + 2 <=? 4194304); [|discriminate].
  pose proof (zero_pages_spec segs IM rho M mem Hrho0 HMem rg t Hg _ (o / 8) ((o + (P - o)) / 8) ltac:(apply Z.div_pos; lia)
                ltac:(apply Z.div_le_upper_bound; lia) Hzp) as Hcells.
  destruct (region_flat segs IM rho xv xb VT M TL XT mem Hrho0 HMem HTL HXT a t o len rg Hav Hg Ho0 ltac:(lia) ltac:(lia)) as (Hflat & Hadr & Hst).
  cbn [AX2S.kentry_ok]. rewrite (elen_lit rho xv xb VT len) by lia. split; [exact Hflat|].
  intros i Hi.
  pose proof (region_ok_nowrap' rho t rg (HM_regions segs IM rho M mem HMem t rg Hg)) as Hnw. pose proof (br_u64 (rho t)) as Hr.
  assert (Ea : Z_to_bv 64 (AX2S.estart E a + i) = adr rho t (o + i)).
  { rewrite Hst. unfold adr. apply bv_eq. rewrite !bv_add_unsigned, !Z_to_bv_unsigned.
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). Z.div_mod_to_equations. lia. }
  rewrite Ea. unfold mrestrict. rewrite (visb_sound t o len Hvis i Hi).
  apply (rview_ov segs mem); [|exact (nosegb_sound t o len Hns i Hi)].
  destruct (Z_lt_dec (o + i) P) as [Hlt|Hge].
  - destruct (Hcells ((o + i) / 8) ltac:(replace (o + (P - o)) with P by lia; unfold P in *; Z.div_mod_to_equations; lia)) as (_ & _ & Hb).
    specialize (Hb (Z.to_nat ((o + i) mod 8)) ltac:(Z.div_mod_to_equations; lia)).
    rewrite Z2Nat.id in Hb by (Z.div_mod_to_equations; lia).
    replace ((o + i) / 8 * 8 + (o + i) mod 8) with (o + i) in Hb by (Z.div_mod_to_equations; lia).
    exact Hb.
  - destruct (Hsp (o + i - P) ltac:(lia)) as (Hb & _).
    replace (P + (o + i - P)) with (o + i) in Hb by lia. exact Hb.
Qed.
End PartZero.
