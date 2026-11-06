(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.FX Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec AsanAcct AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Br Require Import BrEnv.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Br Require Import BrMem BrPart.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.


(* [comment removed for export] *)
(* [comment removed for export] *)
Section Fill.
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

Definition fill_word (c : Z) : Z := c * 72340172838076673.        (* [comment removed for export] *)

Definition fv_fill (c : Z) (v : fval) : bool := (vtag v =? 0)%uint63 && (wZ (vw v) =? fill_word c).

Fixpoint cells_fill (c : Z) (p : page) (pn ci : int) (k : nat) : bool :=
  match k with
  | O => true
  | S k' => match cell_at IM p pn ci with Some v => fv_fill c v | None => false end
            && cells_fill c p pn (ci + 1)%uint63 k'
  end.

Definition page_fill (c : Z) (rg : region) (t pn : int) (c0 : int) (k : nat) : bool :=
  match page_atw IM rg t pn with
  | Some p => cells_fill c p pn c0 k
  | None => false
  end.

Fixpoint fill_pages_b (c : Z) (rg : region) (t : int) (lo hi : Z) (fuel : nat) : bool :=
  match fuel with
  | O => lo >=? hi
  | S f =>
      if lo >=? hi then true
      else
        let pn := lo / 512 in
        let top := Z.min hi ((pn + 1) * 512) in
        page_fill c rg t (of_Z pn) (of_Z (lo - pn * 512)) (Z.to_nat (top - lo))
        && fill_pages_b c rg t top hi f
  end.

Definition range_fill (c : Z) (t : int) (o n : Z) : bool :=
  (0 <=? c) && (c <? 256)
  && (0 <=? o) && (0 <? n) && (o + n <? b62z) && (o mod 8 =? 0) && (n mod 8 =? 0)
  && match iget t M with
     | Some rg => if ((o + n) / 4096 - o / 4096 + 2 <=? 4194304)
                  then fill_pages_b c rg t (o / 8) ((o + n) / 8) (Z.to_nat ((o + n) / 4096 - o / 4096 + 2)) else false
     | None => false
     end.

Definition kfill_ok (a : AX2.saddr) (n : AX2.expr) (c : Z) : bool :=
  match n, aview VT M TL XT a with
  | AX2.ELit len, Some (t, o) => range_fill c t o len && visb t o len && nosegb t o len
  | _, _ => false
  end.

Lemma fv_fill_bytes c v j : 0 <= c < 256 -> fv_fill c v = true -> (j < 8)%nat ->
  nth_error (wbytes8 (dv rho v)) j = Some (Z_to_bv 8 c).
Proof.
  intros Hc Hz Hj. destruct v as [t w]. unfold fv_fill in Hz. cbn [vtag vw] in Hz.
  apply andb_prop in Hz as [Ht Hw]. apply Uint63.eqb_spec in Ht. apply Z.eqb_eq in Hw. subst t.
  rewrite (fk_dv_conc rho w Hrho0). rewrite fk_wbytes8_nth by exact Hj. rewrite wbv_unsigned, Hw. unfold fill_word.
  rewrite <- (Z_to_bv8_mod (c * 72340172838076673 / 2 ^ (8 * Z.of_nat j))). f_equal. apply (f_equal (Z_to_bv 8)).
  do 8 (destruct j as [|j];
        [match goal with |- context [2 ^ ?e] => let v := eval vm_compute in (2 ^ e) in change (2 ^ e) with v end;
         clear - Hc; Z.div_mod_to_equations; lia|]).
  lia.
Qed.

Lemma cells_fill_spec c p pn : forall k ci,
  to_Z ci + Z.of_nat k <= 512 ->
  cells_fill c p pn ci k = true ->
  forall cc, to_Z ci <= cc < to_Z ci + Z.of_nat k ->
    exists v, cell_at IM p pn (of_Z cc) = Some v /\ fv_fill c v = true.
Proof.
  induction k as [|k IH]; intros ci Hb Hz cc Hc; [lia|].
  cbn [cells_fill] in Hz. apply andb_prop in Hz as [Hh Hr]. pose proof (i63_range ci) as Hci.
  destruct (Z.eq_dec cc (to_Z ci)) as [->|Hne].
  - rewrite of_to_Z. destruct (cell_at IM p pn ci) as [v|]; [|discriminate]. exists v. split; [reflexivity | exact Hh].
  - assert (E1 : to_Z (ci + 1)%uint63 = to_Z ci + 1).
    { rewrite add_spec. change (to_Z 1) with 1. apply Z.mod_small. rewrite i63_wB. lia. }
    apply (IH (ci + 1)%uint63); [lia | exact Hr | lia].
Qed.

Lemma page_fill_spec c rg t pn c0 k : 0 <= c < 256 ->
  iget t M = Some rg -> 0 <= pn < 2 ^ 50 -> 0 <= c0 -> c0 + Z.of_nat k <= 512 ->
  page_fill c rg t (of_Z pn) (of_Z c0) k = true ->
  to_Z (rg_lo rg) <= pn * 4096 /\ pn * 4096 + 4096 <= to_Z (rg_len rg)
  /\ forall cc, c0 <= cc < c0 + Z.of_nat k -> forall j, (j < 8)%nat ->
       rview segs mem (adr rho t (pn * 4096 + cc * 8 + Z.of_nat j)) = Some (Z_to_bv 8 c).
Proof.
  intros Hcb Hg Hpn Hc0 Hck Hz. unfold page_fill in Hz.
  assert (Hpn' : to_Z (of_Z pn) = pn) by (apply of_Z_small; lia).
  assert (Hc0' : to_Z (of_Z c0) = c0) by (apply of_Z_small; lia).
  destruct (page_atw IM rg t (of_Z pn)) as [p|] eqn:Hp; [|discriminate].
  destruct (page_atw_ok segs IM rho M mem HMem rg t _ p Hg ltac:(rewrite Hpn'; lia) Hp) as (_ & (_ & Hcells & _) & Hlo & Hhi).
  rewrite Hpn' in *. split; [exact Hlo|]. split; [exact Hhi|].
  intros cc Hc j Hj.
  assert (Hc' : to_Z (of_Z cc) = cc) by (apply of_Z_small; lia).
  destruct (cells_fill_spec c p (of_Z pn) k (of_Z c0) ltac:(rewrite Hc0'; lia) Hz cc ltac:(rewrite Hc0'; lia)) as (v & Hv1 & Hv2).
  specialize (Hcells (of_Z cc) v ltac:(rewrite Hc'; lia) Hv1 j Hj). rewrite Hc' in Hcells.
  rewrite Hcells. apply fv_fill_bytes; assumption.
Qed.

Lemma fill_pages_spec c rg t : 0 <= c < 256 -> iget t M = Some rg -> forall fuel lo hi,
  0 <= lo -> hi <= 2 ^ 59 ->
  fill_pages_b c rg t lo hi fuel = true ->
  forall cc, lo <= cc < hi ->
    to_Z (rg_lo rg) <= cc * 8 /\ cc * 8 + 8 <= to_Z (rg_len rg)
    /\ forall j, (j < 8)%nat -> rview segs mem (adr rho t (cc * 8 + Z.of_nat j)) = Some (Z_to_bv 8 c).
Proof.
  intros Hcb Hg. induction fuel as [|f IH]; intros lo hi Hlo Hhi Hz cc Hc; cbn [fill_pages_b] in Hz.
  - apply Z.geb_le in Hz. lia.
  - destruct (lo >=? hi) eqn:Ege; [apply Z.geb_le in Ege; lia|].
    apply andb_prop in Hz as [Hpz Hrest].
    set (pn := lo / 512) in *. set (top := Z.min hi ((pn + 1) * 512)) in *.
    assert (Hpn : 0 <= pn < 2 ^ 50).
    { unfold pn. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
    assert (Hlop : pn * 512 <= lo < (pn + 1) * 512) by (unfold pn; Z.div_mod_to_equations; lia).
    destruct (Z_lt_le_dec cc top) as [Hct|Hct].
    + destruct (page_fill_spec c rg t pn (lo - pn * 512) (Z.to_nat (top - lo)) Hcb Hg Hpn ltac:(lia)
                  ltac:(unfold top; lia) Hpz) as (Hrlo & Hrhi & Hcells).
      specialize (Hcells (cc - pn * 512) ltac:(unfold top in *; lia)).
      split; [lia|]. split; [unfold top in *; lia|].
      intros j Hj. specialize (Hcells j Hj).
      replace (pn * 4096 + (cc - pn * 512) * 8 + Z.of_nat j) with (cc * 8 + Z.of_nat j) in Hcells by lia.
      exact Hcells.
    + apply (IH top hi); [unfold top; lia | exact Hhi | exact Hrest | lia].
Qed.

Theorem kfill_sound a n c :
  kfill_ok a n c = true -> AX2S.kentry_ok segs E (mrestrict H mem) (AX2.KFill a n c).
Proof.
  unfold kfill_ok. intros Hk. destruct n as [len| | | | | | |]; try discriminate.
  destruct (aview VT M TL XT a) as [[t o]|] eqn:Hav; [|discriminate].
  apply andb_prop in Hk as [Hk Hns]. apply andb_prop in Hk as [Hrz Hvis].
  unfold range_fill in Hrz. apply andb_prop in Hrz as [Hrz Hzp]. apply andb_prop in Hrz as [Hrz Hn8].
  apply andb_prop in Hrz as [Hrz Ho8]. apply andb_prop in Hrz as [Hrz H62]. apply andb_prop in Hrz as [Hrz Hn0].
  apply andb_prop in Hrz as [Hrz Ho0]. apply andb_prop in Hrz as [Hc0 Hc1].
  apply Z.leb_le in Ho0, Hc0. apply Z.ltb_lt in Hn0, H62, Hc1. apply Z.eqb_eq in Ho8, Hn8. unfold b62z in H62.
  destruct (iget t M) as [rg|] eqn:Hg; [|discriminate].
  destruct ((o + len) / 4096 - o / 4096 + 2 <=? 4194304); [|discriminate].
  pose proof (fill_pages_spec c rg t (conj Hc0 Hc1) Hg _ (o / 8) ((o + len) / 8) ltac:(apply Z.div_pos; lia)
                ltac:(apply Z.div_le_upper_bound; lia) Hzp) as Hcells.
  assert (Hlen : o + len <= to_Z (rg_len rg)).
  { destruct (Hcells ((o + len) / 8 - 1)) as (_ & Hhi & _); Z.div_mod_to_equations; lia. }
  destruct (region_flat segs IM rho xv xb VT M TL XT mem Hrho0 HMem HTL HXT a t o len rg Hav Hg Ho0 ltac:(lia) Hlen) as (Hflat & Hadr & Hst).
  cbn [AX2S.kentry_ok]. rewrite (elen_lit rho xv xb VT len) by lia. split; [exact Hflat|].
  intros i Hi.
  pose proof (region_ok_nowrap' rho t rg (proj1 (proj1 HMem t rg Hg))) as Hnw. pose proof (br_u64 (rho t)) as Hr.
  assert (Ea : Z_to_bv 64 (AX2S.estart E a + i) = adr rho t (o + i)).
  { rewrite Hst. unfold adr. apply bv_eq. rewrite !bv_add_unsigned, !Z_to_bv_unsigned.
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). Z.div_mod_to_equations. lia. }
  rewrite Ea. unfold mrestrict. rewrite (visb_sound t o len Hvis i Hi).
  apply (rview_ov segs mem); [|exact (nosegb_sound t o len Hns i Hi)].
  destruct (Hcells ((o + i) / 8) ltac:(Z.div_mod_to_equations; lia)) as (_ & _ & Hb).
  specialize (Hb (Z.to_nat ((o + i) mod 8)) ltac:(Z.div_mod_to_equations; lia)).
  rewrite Z2Nat.id in Hb by (Z.div_mod_to_equations; lia).
  replace ((o + i) / 8 * 8 + (o + i) mod 8) with (o + i) in Hb by (Z.div_mod_to_equations; lia).
  exact Hb.
Qed.

(* [comment removed for export] *)

End Fill.
