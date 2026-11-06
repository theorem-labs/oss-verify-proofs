(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import AllocCfg.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.FX Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxRn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition fx_sysret (F : fstate) (ret : fval) (M' : itrie region) : fstate :=
  FS (f_pc F + 4)%uint63 (iset 10%uint63 ret (f_regs F)) M' (f_resv F).

(* [comment removed for export] *)
Definition grant_clo : int := 4096.
Definition grant_chi (len : int) : int := (140737488355328 - len)%uint63.

(* [comment removed for export] *)
Definition fx_grant (F : fstate) (t len : int) : fstate :=
  fx_sysret F (FV t w_zero) (iset t (RG 0 len 12 (Some PKZero) iempty grant_clo (grant_chi len)) (f_mem F)).

(* [comment removed for export] *)
Definition fx_grant_na (F : fstate) (t len : int) : fstate :=
  fx_sysret F (FV t w_zero) (iset t (RG 0 len 12 None iempty grant_clo (grant_chi len)) (f_mem F)).

(* [comment removed for export] *)
Definition fx_unmap (F : fstate) (t : int) : fstate :=
  fx_sysret F (FV 0 w_zero) (iremove t (f_mem F)).

(* [comment removed for export] *)
Definition fx_ret (F : fstate) (v : fval) : fstate := fx_sysret F v (f_mem F).

(* [comment removed for export] *)
Fixpoint hole_pages (k : nat) (pn : int) (pages : itrie page) : itrie page :=
  match k with
  | O => pages
  | S k' => hole_pages k' (pn + 1)%uint63 (iset pn (PG false PKUnk iempty) pages)
  end.
(* [comment removed for export] *)
Fixpoint zero_pages (k : nat) (pn : int) (pages : itrie page) : itrie page :=
  match k with
  | O => pages
  | S k' => zero_pages k' (pn + 1)%uint63 (iset pn (PG true PKZero iempty) pages)
  end.

Definition upd_region (M : itrie region) (t : int) (f : region -> region) : itrie region :=
  match iget t M with Some rg => iset t (f rg) M | None => M end.

(* [comment removed for export] *)
Definition fx_guard (F : fstate) (t pn : int) (k : nat) : fstate :=
  fx_sysret F (FV t (W64 0 (pn << 12)%uint63))
    (upd_region (f_mem F) t (fun rg => RGK (rg_lo rg) (rg_len rg) (rg_align rg) (rg_dflt rg) (hole_pages k pn (rg_pages rg)) (rg_clo rg) (rg_chi rg) (rg_kind rg))).

(* [comment removed for export] *)
Definition fx_expose (F : fstate) (t pn : int) (k : nat) : fstate :=
  fx_sysret F (FV 0 w_zero)
    (upd_region (f_mem F) t (fun rg => RGK (rg_lo rg) (rg_len rg) (rg_align rg) (rg_dflt rg) (zero_pages k pn (rg_pages rg)) (rg_clo rg) (rg_chi rg) (rg_kind rg))).

(* [comment removed for export] *)
Definition fx_commit (F : fstate) (t pn : int) (k : nat) : fstate :=
  fx_sysret F (FV t (W64 0 (pn << 12)%uint63))
    (upd_region (f_mem F) t (fun rg => RGK (rg_lo rg) (rg_len rg) (rg_align rg) (rg_dflt rg) (zero_pages k pn (rg_pages rg)) (rg_clo rg) (rg_chi rg) (rg_kind rg))).

(* [comment removed for export] *)
Definition fx_brk_grow (F : fstate) (t : int) (k : nat) : fstate :=
  match iget t (f_mem F) with
  | Some rg =>
      let len' := (rg_len rg + (of_Z (Z.of_nat k) << 12))%uint63 in
      fx_sysret F (FV t (W64 0 len'))
        (iset t (RGK (rg_lo rg) len' (rg_align rg) (rg_dflt rg) (zero_pages k (rg_len rg >> 12)%uint63 (rg_pages rg))
                    (rg_clo rg) (rg_chi rg) (rg_kind rg)) (f_mem F))
  | None => F
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma fxs_wB : wB = 2 ^ 63. Proof. reflexivity. Qed.

Lemma fxs_to_Z_succ : forall n : int, to_Z n < 2 ^ 61 -> to_Z (n + 1)%uint63 = to_Z n + 1.
Proof.
  intros n H. pose proof (to_Z_bounded n) as Hb. rewrite Uint63.add_spec.
  change (to_Z 1) with 1. apply Z.mod_small. rewrite fxs_wB. lia.
Qed.

Lemma fxs_to_Z_lsl12' : forall pn : int, to_Z pn < 2 ^ 51 -> to_Z (pn << 12)%uint63 = to_Z pn * 4096.
Proof.
  intros pn H. pose proof (to_Z_bounded pn) as Hb. rewrite Uint63.lsl_spec.
  change (to_Z 12) with 12. change (2 ^ 12) with 4096. apply Z.mod_small. rewrite fxs_wB. lia.
Qed.

Lemma fxs_to_Z_lsl12 : forall pn : int, to_Z pn < 2 ^ 50 -> to_Z (pn << 12)%uint63 = to_Z pn * 4096.
Proof.
  intros pn H. pose proof (to_Z_bounded pn) as Hb. rewrite Uint63.lsl_spec.
  change (to_Z 12) with 12. change (2 ^ 12) with 4096. apply Z.mod_small. rewrite fxs_wB. lia.
Qed.

Lemma fxs_to_Z_lsr12 : forall x : int, to_Z (x >> 12)%uint63 = to_Z x / 4096.
Proof. intros x. rewrite Uint63.lsr_spec. reflexivity. Qed.

Lemma fxs_eqb_false : forall a b : int, to_Z a <> to_Z b -> (a =? b)%uint63 = false.
Proof.
  intros a b H. destruct (a =? b)%uint63 eqn:E; [| reflexivity].
  apply Uint63.eqb_spec in E. subst. contradiction.
Qed.

Lemma fxs_eqb_true : forall a b : int, (a =? b)%uint63 = true -> a = b.
Proof. intros a b H. apply Uint63.eqb_spec. exact H. Qed.

(* [comment removed for export] *)
Lemma fxs_ireg_to_Z : forall r : reg, to_Z (ireg r) = bv_unsigned r.
Proof.
  intros r. unfold ireg. rewrite Uint63.of_Z_spec.
  pose proof (bv_unsigned_in_range _ r) as H. unfold bv_modulus in H. change (2 ^ Z.of_N 5) with 32 in H.
  apply Z.mod_small. rewrite fxs_wB. lia.
Qed.

Lemma fxs_ireg_is0 : forall r : reg, (ireg r =? 0)%uint63 = is_x0 r.
Proof.
  intros r. unfold is_x0.
  destruct (Z.eqb_spec (bv_unsigned r) 0) as [E|E].
  - apply Uint63.eqb_spec. apply Uint63.to_Z_inj. rewrite fxs_ireg_to_Z. exact E.
  - apply fxs_eqb_false. rewrite fxs_ireg_to_Z. exact E.
Qed.

Lemma fxs_ireg_eq10 : forall r : reg, (ireg r =? 10)%uint63 = bv_eqb r (10%bv : bv 5).
Proof.
  intros r. unfold bv_eqb. change (bv_unsigned (10%bv : bv 5)) with 10.
  destruct (Z.eqb_spec (bv_unsigned r) 10) as [E|E].
  - apply Uint63.eqb_spec. apply Uint63.to_Z_inj. rewrite fxs_ireg_to_Z. exact E.
  - apply fxs_eqb_false. rewrite fxs_ireg_to_Z. exact E.
Qed.

(* [comment removed for export] *)
Lemma fxs_u64 : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof. intro w. exact (bv_unsigned_in_range _ w). Qed.

Lemma fxs_u64_lit : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. apply Z_to_bv_small. unfold bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). lia. Qed.

Lemma fxs_bv_add_unsigned_small : forall (a : word) z,
  0 <= z -> bv_unsigned a + z < 2 ^ 64 ->
  bv_unsigned (bv_add a (Z_to_bv 64 z)) = bv_unsigned a + z.
Proof.
  intros a z Hz Hs. pose proof (fxs_u64 a) as Ha.
  rewrite bv_add_unsigned, fxs_u64_lit by lia.
  apply bv_wrap_small. unfold bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). lia.
Qed.

Lemma fxs_bv_add_0 : forall a : word, bv_add a (Z_to_bv 64 0) = a.
Proof.
  intros a. apply bv_eq. rewrite fxs_bv_add_unsigned_small; pose proof (fxs_u64 a); lia.
Qed.

Lemma fxs_wbv_W64_0 : forall x : int, wbv (W64 0 x) = Z_to_bv 64 (to_Z x).
Proof. intros x. unfold wbv. rewrite wZ_W64. change (to_Z 0 mod 2) with 0. reflexivity. Qed.

Lemma fxs_zero_bytes : forall j, (j < 8)%nat -> nth_error (Z_to_le_bytes 8 0) j = Some (Z_to_bv 8 0).
Proof. intros j Hj. do 8 (destruct j as [|j]; [reflexivity|]). lia. Qed.

(* [comment removed for export] *)
Lemma fxs_pc_plus4 : forall pc : int,
  to_Z pc < pc_bound - 4 ->
  bv_add (Z_to_bv 64 (to_Z pc)) (Z_to_bv 64 4) = Z_to_bv 64 (to_Z (pc + 4)%uint63).
Proof.
  intros pc H. unfold pc_bound in H. pose proof (to_Z_bounded pc) as Hb.
  rewrite Uint63.add_spec. change (to_Z 4) with 4. rewrite Z.mod_small by (rewrite fxs_wB; lia).
  apply bv_eq. rewrite fxs_bv_add_unsigned_small by (rewrite ?fxs_u64_lit; lia).
  rewrite !fxs_u64_lit by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma agree_upd : forall n rho a rho'',
  to_Z n < 2 ^ 61 ->
  agree (n + 1)%uint63 (rho_upd rho n a) rho'' ->
  agree n rho rho'' /\ rho'' n = a.
Proof.
  intros n rho a rho'' Hn [H0 Hb]. pose proof (fxs_to_Z_succ n Hn) as Hs. split; [split |].
  - exact H0.
  - intros t Ht. rewrite Hb by lia. unfold rho_upd. rewrite fxs_eqb_false by lia. reflexivity.
  - rewrite Hb by lia. unfold rho_upd. rewrite Uint63.eqb_refl. reflexivity.
Qed.

Lemma agree_refl : forall n rho, rho 0%uint63 = Z_to_bv 64 0 -> agree n rho rho.
Proof. intros n rho H. split; [exact H | reflexivity]. Qed.

(* [comment removed for export] *)
Lemma iget_hole_pages : forall k pn pages q,
  to_Z pn + Z.of_nat k < 2 ^ 61 ->
  iget q (hole_pages k pn pages) =
  if (to_Z pn <=? to_Z q) && (to_Z q <? to_Z pn + Z.of_nat k) then Some (PG false PKUnk iempty)
  else iget q pages.
Proof.
  induction k as [|k IH]; intros pn pages q Hb.
  - cbn [hole_pages]. replace (to_Z q <? to_Z pn + Z.of_nat 0) with (to_Z q <? to_Z pn) by (f_equal; lia).
    destruct (Z.leb_spec (to_Z pn) (to_Z q)); destruct (Z.ltb_spec (to_Z q) (to_Z pn)); try reflexivity; lia.
  - cbn [hole_pages]. pose proof (to_Z_bounded pn) as Hpn.
    assert (Hs : to_Z (pn + 1)%uint63 = to_Z pn + 1) by (apply fxs_to_Z_succ; lia).
    rewrite IH by (rewrite Hs; lia). rewrite Hs, iget_iset.
    destruct (q =? pn)%uint63 eqn:E.
    + apply fxs_eqb_true in E. subst q.
      destruct (Z.leb_spec (to_Z pn + 1) (to_Z pn)); [lia |]. cbn [andb].
      destruct (Z.leb_spec (to_Z pn) (to_Z pn)); [| lia].
      destruct (Z.ltb_spec (to_Z pn) (to_Z pn + Z.of_nat (S k))); [reflexivity | lia].
    + assert (Hne : to_Z q <> to_Z pn).
      { intros Heq. apply Uint63.to_Z_inj in Heq. subst q. rewrite Uint63.eqb_refl in E. discriminate E. }
      destruct (Z.leb_spec (to_Z pn + 1) (to_Z q)); destruct (Z.leb_spec (to_Z pn) (to_Z q));
        destruct (Z.ltb_spec (to_Z q) (to_Z pn + 1 + Z.of_nat k));
        destruct (Z.ltb_spec (to_Z q) (to_Z pn + Z.of_nat (S k))); cbn [andb]; try reflexivity; lia.
Qed.

Lemma iget_zero_pages : forall k pn pages q,
  to_Z pn + Z.of_nat k < 2 ^ 61 ->
  iget q (zero_pages k pn pages) =
  if (to_Z pn <=? to_Z q) && (to_Z q <? to_Z pn + Z.of_nat k) then Some (PG true PKZero iempty)
  else iget q pages.
Proof.
  induction k as [|k IH]; intros pn pages q Hb.
  - cbn [zero_pages]. replace (to_Z q <? to_Z pn + Z.of_nat 0) with (to_Z q <? to_Z pn) by (f_equal; lia).
    destruct (Z.leb_spec (to_Z pn) (to_Z q)); destruct (Z.ltb_spec (to_Z q) (to_Z pn)); try reflexivity; lia.
  - cbn [zero_pages]. pose proof (to_Z_bounded pn) as Hpn.
    assert (Hs : to_Z (pn + 1)%uint63 = to_Z pn + 1) by (apply fxs_to_Z_succ; lia).
    rewrite IH by (rewrite Hs; lia). rewrite Hs, iget_iset.
    destruct (q =? pn)%uint63 eqn:E.
    + apply fxs_eqb_true in E. subst q.
      destruct (Z.leb_spec (to_Z pn + 1) (to_Z pn)); [lia |]. cbn [andb].
      destruct (Z.leb_spec (to_Z pn) (to_Z pn)); [| lia].
      destruct (Z.ltb_spec (to_Z pn) (to_Z pn + Z.of_nat (S k))); [reflexivity | lia].
    + assert (Hne : to_Z q <> to_Z pn).
      { intros Heq. apply Uint63.to_Z_inj in Heq. subst q. rewrite Uint63.eqb_refl in E. discriminate E. }
      destruct (Z.leb_spec (to_Z pn + 1) (to_Z q)); destruct (Z.leb_spec (to_Z pn) (to_Z q));
        destruct (Z.ltb_spec (to_Z q) (to_Z pn + 1 + Z.of_nat k));
        destruct (Z.ltb_spec (to_Z q) (to_Z pn + Z.of_nat (S k))); cbn [andb]; try reflexivity; lia.
Qed.

Section Sys.
Variable segs : list Segment.
Variable IM : fimage.

Local Abbreviation Rn := (FxRn.Rn segs IM).

(* [comment removed for export] *)
Definition rg_ival (rho : int -> word) (t : int) (rg : region) : Z * Z :=
  (bv_unsigned (rho t) + to_Z (rg_lo rg), bv_unsigned (rho t) + to_Z (rg_len rg)).

(* [comment removed for export] *)
Definition sep_from (rho : int -> word) (M : itrie region) (lo hi : Z) : Prop :=
  forall t rg, iget t M = Some rg ->
    hi <= fst (rg_ival rho t rg) \/ snd (rg_ival rho t rg) <= lo.

(* [comment removed for export] *)
Definition regions_lt (n : int) (M : itrie region) : Prop :=
  forall t rg, iget t M = Some rg -> to_Z t < to_Z n.
Definition regions_lt_b (n : int) (M : itrie region) : bool := iall (fun t _ => (t <? n)%uint63) M.

(* [comment removed for export] *)
Definition at_ecall (F : fstate) : Prop := to_Z (f_pc F) < pc_bound - 4.

Theorem regions_lt_b_sound : forall n M, regions_lt_b n M = true -> regions_lt n M.
Proof.
  intros n M H t rg Hget. unfold regions_lt_b in H.
  pose proof (proj1 (iall_spec (fun t _ => (t <? n)%uint63) M) H t rg Hget) as Hlt.
  cbv beta in Hlt. apply Uint63.ltb_spec in Hlt. exact Hlt.
Qed.

(* [comment removed for export] *)

Lemma fxs_adr_unsigned : forall rho t z,
  0 <= z -> bv_unsigned (rho t) + z < 2 ^ 64 ->
  bv_unsigned (adr rho t z) = bv_unsigned (rho t) + z.
Proof. intros rho t z Hz Hs. unfold adr. apply fxs_bv_add_unsigned_small; assumption. Qed.

(* [comment removed for export] *)
Lemma fxs_adr_ext : forall rho rho' t z, rho' t = rho t -> adr rho' t z = adr rho t z.
Proof. intros rho rho' t z H. unfold adr. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma fxs_page_ok_frame : forall rho m m' t pn L p,
  (forall j, 0 <= j < 8 * L ->
     m' (adr rho t (to_Z pn * 4096 + j)) = m (adr rho t (to_Z pn * 4096 + j))) ->
  page_ok segs IM rho m t pn L p -> page_ok segs IM rho m' t pn L p.
Proof.
  intros rho m m' t pn L p Hm (Hwr & Hcells & Hslots). split; [| split].
  - intros Hw j Hj. specialize (Hwr Hw j Hj). unfold wview in *. rewrite (Hm j Hj). exact Hwr.
  - intros ci v Hci Hcell j Hj. specialize (Hcells ci v Hci Hcell j Hj).
    unfold rview in *.
    replace (to_Z pn * 4096 + to_Z ci * 8 + Z.of_nat j)
      with (to_Z pn * 4096 + (to_Z ci * 8 + Z.of_nat j)) in * by lia.
    rewrite (Hm (to_Z ci * 8 + Z.of_nat j)) by lia. exact Hcells.
  - intros ci sl Hci Hget j Hj. specialize (Hslots ci sl Hci Hget j Hj).
    assert (E : rview segs m' (adr rho t (to_Z pn * 4096 + to_Z ci * 8 + to_Z j))
                = rview segs m (adr rho t (to_Z pn * 4096 + to_Z ci * 8 + to_Z j))).
    { unfold rview.
      replace (to_Z pn * 4096 + to_Z ci * 8 + to_Z j)
        with (to_Z pn * 4096 + (to_Z ci * 8 + to_Z j)) by lia.
      rewrite (Hm (to_Z ci * 8 + to_Z j)) by lia. reflexivity. }
    unfold slot_ok in *. destruct (sget j sl); [rewrite E; exact Hslots | rewrite E; exact Hslots | exact I].
Qed.

(* [comment removed for export] *)
Lemma fxs_page_ok_hole : forall rho m t pn L, page_ok segs IM rho m t pn L (PG false PKUnk iempty).
Proof.
  intros rho m t pn L. split; [| split].
  - cbn [pg_wr]. discriminate.
  - intros ci v _ Hcell. unfold cell_at in Hcell. cbn [pg_cells pg_kind] in Hcell.
    rewrite iget_iempty in Hcell. discriminate Hcell.
  - intros ci sl _ Hget. cbn [pg_cells] in Hget. rewrite iget_iempty in Hget. discriminate Hget.
Qed.

(* [comment removed for export] *)
Lemma fxs_page_ok_zero : forall rho m t pn L wr,
  rho 0%uint63 = Z_to_bv 64 0 ->
  (forall j, 0 <= j < 8 * L -> m (adr rho t (to_Z pn * 4096 + j)) = Some (Z_to_bv 8 0)) ->
  page_ok segs IM rho m t pn L (PG wr PKZero iempty).
Proof.
  intros rho m t pn L wr H0 Hm. split; [| split];
    [| | intros ci sl _ Hget; cbn [pg_cells] in Hget; rewrite iget_iempty in Hget; discriminate Hget].
  - intros _ j Hj. unfold wview. rewrite (Hm j Hj). discriminate.
  - intros ci v Hci Hcell j Hj. unfold cell_at in Hcell. cbn [pg_cells pg_kind] in Hcell.
    rewrite iget_iempty in Hcell. inversion Hcell; subst v.
    unfold rview.
    replace (to_Z pn * 4096 + to_Z ci * 8 + Z.of_nat j)
      with (to_Z pn * 4096 + (to_Z ci * 8 + Z.of_nat j)) by lia.
    rewrite (Hm (to_Z ci * 8 + Z.of_nat j)) by lia.
    unfold fv0. rewrite (fk_dv_conc rho w_zero H0), wbv_w_zero. unfold wbytes8, w0.
    change (bv_unsigned (Z_to_bv 64 0)) with 0.
    symmetry. apply fxs_zero_bytes. exact Hj.
Qed.

(* [comment removed for export] *)
Lemma fxs_page_addr : forall rho t rg pn j,
  region_ok rho t rg ->
  to_Z (rg_lo rg) <= to_Z pn * 4096 -> to_Z pn * 4096 + j < to_Z (rg_len rg) ->
  0 <= j < 4096 ->
  bv_unsigned (adr rho t (to_Z pn * 4096 + j)) = bv_unsigned (rho t) + to_Z pn * 4096 + j.
Proof.
  intros rho t rg pn j (_ & Hlen & Hhi & _ & _) Hlo Hup Hj.
  pose proof (to_Z_bounded pn) as Hpn. pose proof (fxs_u64 (rho t)) as Hr.
  rewrite fxs_adr_unsigned by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma fxs_clim_bytes : forall rg q j, 0 <= j < 8 * clim rg q -> to_Z q * 4096 + j < to_Z (rg_len rg) /\ j < 4096.
Proof. intros rg q j Hj. unfold clim in Hj. Z.div_mod_to_equations. lia. Qed.

Lemma fxs_clim_full : forall rg q, to_Z q * 4096 + 4096 <= to_Z (rg_len rg) -> clim rg q = 512.
Proof. intros rg q H. unfold clim. apply Z.min_l. Z.div_mod_to_equations. lia. Qed.

Lemma fxs_page_whole : forall len q, len mod 4096 = 0 -> q * 4096 < len -> q * 4096 + 4096 <= len.
Proof. intros len q Hm Hq. Z.div_mod_to_equations. lia. Qed.

Lemma fxs_page_in_region_spec : forall rg pn, to_Z pn < 2 ^ 50 -> page_in_region rg pn = true ->
  to_Z (rg_lo rg) <= to_Z pn * 4096 /\ to_Z pn * 4096 < to_Z (rg_len rg)
  /\ (to_Z pn * 4096 + 4096 <= to_Z (rg_len rg) \/ to_Z (rg_len rg) mod 8 = 0)
  /\ to_Z (rg_len rg) <= 2 ^ 62.
Proof.
  intros rg pn Hpn H. unfold page_in_region in H. rewrite !andb_true_iff in H.
  destruct H as [[[_ Hlo] Hup] Hlen].
  apply Uint63.leb_spec in Hlo, Hlen. change (to_Z 4611686018427387904) with (2 ^ 62) in Hlen.
  pose proof (to_Z_bounded pn) as Hpnb. rewrite (fxs_to_Z_lsl12 pn Hpn) in Hlo.
  split; [exact Hlo|]. apply orb_true_iff in Hup as [Hup|Hup].
  - apply Uint63.leb_spec in Hup. rewrite Uint63.add_spec, (fxs_to_Z_lsl12 pn Hpn) in Hup.
    change (to_Z 4096) with 4096 in Hup. rewrite Z.mod_small in Hup by (rewrite fxs_wB; lia).
    split; [lia|]. split; [left; exact Hup | exact Hlen].
  - apply andb_true_iff in Hup as [Hup Hal]. apply Uint63.ltb_spec in Hup. rewrite (fxs_to_Z_lsl12 pn Hpn) in Hup.
    apply Uint63.eqb_spec in Hal. apply (f_equal to_Z) in Hal.
    rewrite (i63_land_ones (rg_len rg) 7%uint63 3 eq_refl ltac:(lia)) in Hal. change (2 ^ 3) with 8 in Hal. change (to_Z 0) with 0 in Hal.
    split; [exact Hup|]. split; [right; exact Hal | exact Hlen].
Qed.

(* [comment removed for export] *)
Lemma fxs_region_frame : forall rho m m' t rg,
  region_ok rho t rg ->
  (forall x : word,
     bv_unsigned (rho t) + to_Z (rg_lo rg) <= bv_unsigned x < bv_unsigned (rho t) + to_Z (rg_len rg) ->
     m' x = m x) ->
  (forall pn p, to_Z pn < 2 ^ 50 -> page_at IM rg t pn = Some p ->
     page_ok segs IM rho m t pn (clim rg pn) p
     /\ to_Z (rg_lo rg) <= to_Z pn * 4096 /\ to_Z pn * 4096 < to_Z (rg_len rg)
     /\ (to_Z pn * 4096 + 4096 <= to_Z (rg_len rg) \/ to_Z (rg_len rg) mod 8 = 0)) ->
  forall pn p, to_Z pn < 2 ^ 50 -> page_at IM rg t pn = Some p ->
     page_ok segs IM rho m' t pn (clim rg pn) p
     /\ to_Z (rg_lo rg) <= to_Z pn * 4096 /\ to_Z pn * 4096 < to_Z (rg_len rg)
     /\ (to_Z pn * 4096 + 4096 <= to_Z (rg_len rg) \/ to_Z (rg_len rg) mod 8 = 0).
Proof.
  intros rho m m' t rg Hrg Hm Hpages pn p Hpn Hpa.
  destruct (Hpages pn p Hpn Hpa) as (Hok & Hlo & Hup & Hal). split; [| split; [|split]; assumption].
  eapply fxs_page_ok_frame; [| exact Hok].
  intros j Hj.
  assert (Hjl : to_Z pn * 4096 + j < to_Z (rg_len rg) /\ j < 4096).
  { clear - Hj Hup. unfold clim in Hj. Z.div_mod_to_equations. lia. }
  apply Hm. rewrite (fxs_page_addr rho t rg pn j Hrg Hlo (proj1 Hjl) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma fxs_R_sysret : forall rho F ms ret v M' mem',
  R segs IM rho F ms -> at_ecall F ->
  dv rho v = ret ->
  mem_ok segs IM rho M' mem' ->
  R segs IM rho (fx_sysret F v M') (sysret (ms_pend ms) ret mem').
Proof.
  intros rho F ms ret v M' mem' HR Hpc Hv Hmem. constructor.
  - cbn [sysret ms_pc_val fx_sysret f_pc]. unfold ms_pc. cbn [ms_pend ms_pc_val].
    rewrite (R_pc _ _ _ _ _ HR). apply fxs_pc_plus4. exact Hpc.
  - intros r. pose proof (R_regs _ _ _ _ _ HR r) as Hr.
    unfold Sem.rget in *. cbn [core_of c_regs sysret ms_regs ms_pend] in *.
    unfold FxState.rget in *. cbn [fx_sysret f_regs]. rewrite fxs_ireg_is0 in *.
    destruct (is_x0 r) eqn:Ex0; [exact Hr |].
    rewrite iget_iset, fxs_ireg_eq10.
    unfold reg_get. destruct (bv_eqb r (10%bv : bv 5)) eqn:E10.
    + unfold bv_eqb in E10. apply Z.eqb_eq in E10. apply bv_eq in E10. subst r.
      rewrite bvmap_get_set_same. symmetry. exact Hv.
    + rewrite bvmap_get_set_other; [exact Hr |].
      intros Heq. subst r. unfold bv_eqb in E10. rewrite Z.eqb_refl in E10. discriminate E10.
  - reflexivity.
  - cbn [sysret ms_resv ms_pend fx_sysret f_resv]. exact (R_resv _ _ _ _ _ HR).
  - cbn [sysret ms_mem fx_sysret f_mem]. exact Hmem.
Qed.

(* [comment removed for export] *)
Lemma fxs_zeros_in : forall m a n x,
  bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n ->
  apply_zeros m [(a, n)] x = Some (Z_to_bv 8 0).
Proof.
  intros m a n x H. rewrite apply_zeros_one.
  rewrite (proj2 (Z.leb_le _ _)), (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.

Lemma fxs_zeros_out : forall m a n x,
  (bv_unsigned x < bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x) ->
  apply_zeros m [(a, n)] x = m x.
Proof.
  intros m a n x H. rewrite apply_zeros_one.
  destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned x));
    destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned a + bv_unsigned n)); cbn [andb]; try reflexivity; lia.
Qed.

Lemma fxs_unmaps_out : forall m a n x,
  (bv_unsigned x < bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x) ->
  apply_unmaps m [(a, n)] x = m x.
Proof.
  intros m a n x H. rewrite apply_unmaps_one.
  destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned x));
    destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned a + bv_unsigned n)); cbn [andb]; try reflexivity; lia.
Qed.

(* [comment removed for export] *)
Lemma fxs_mem_ok_fresh : forall rho'' M m m' n a len dflt clo chi,
  to_Z clo <= bv_unsigned a <= to_Z chi ->
  mem_ok segs IM rho'' M m ->
  rho'' n = a -> n <> 0%uint63 -> to_Z n < 2 ^ 60 ->
  iget n M = None ->
  to_Z len <= 2 ^ 62 -> bv_unsigned a mod 4096 = 0 -> 0 < bv_unsigned a ->
  bv_unsigned a + to_Z len < 2 ^ 63 ->
  sep_from rho'' M (bv_unsigned a) (bv_unsigned a + to_Z len) ->
  (forall x : word, (bv_unsigned x < bv_unsigned a \/ bv_unsigned a + to_Z len <= bv_unsigned x) ->
                    m' x = m x) ->
  (forall pn p, to_Z pn < 2 ^ 50 -> page_at IM (RG 0 len 12 dflt iempty clo chi) n pn = Some p ->
     page_ok segs IM rho'' m' n pn 512 p
     /\ 0 <= to_Z pn * 4096 /\ to_Z pn * 4096 + 4096 <= to_Z len) ->
  mem_ok segs IM rho'' (iset n (RG 0 len 12 dflt iempty clo chi) M) m'.
Proof.
  intros rho'' M m m' n a len dflt clo chi Hbnd [Hregs Hsep] Hn Hn0 Hnpl Hfresh Hlen Hal Ha0 Hhi Hsepf Hout Hnew.
  split.
  - intros t rg Hget. rewrite iget_iset in Hget.
    destruct (t =? n)%uint63 eqn:E.
    + apply fxs_eqb_true in E. subst t. inversion Hget; subst rg. clear Hget. split.
      * unfold region_ok. cbn [rg_len rg_lo rg_align rg_clo rg_chi]. rewrite Hn. change (to_Z 0) with 0.
        change (to_Z 12) with 12. change (2 ^ 12) with 4096.
        repeat split; try assumption; lia.
      * intros pn p Hpn Hpa. destruct (Hnew pn p Hpn Hpa) as (Hok & Hplo & Hphi).
        rewrite fxs_clim_full by (cbn [rg_len]; exact Hphi).
        cbn [rg_lo rg_len]. change (to_Z 0) with 0.
        split; [exact Hok|]. split; [exact Hplo|]. split; [lia | left; exact Hphi].
    + destruct (Hregs t rg Hget) as [Hrg Hpages]. split; [exact Hrg |].
      apply (fxs_region_frame rho'' m m' t rg Hrg); [| exact Hpages].
      intros x Hx. apply Hout.
      destruct (Hsepf t rg Hget) as [Hs | Hs]; unfold rg_ival in Hs; cbn [fst snd] in Hs; lia.
  - intros t t' rg rg' Hne Hg Hg'. rewrite iget_iset in Hg, Hg'.
    destruct (t =? n)%uint63 eqn:E; destruct (t' =? n)%uint63 eqn:E'.
    + apply fxs_eqb_true in E, E'. congruence.
    + apply fxs_eqb_true in E. subst t. inversion Hg; subst rg. cbn [rg_len rg_lo]. rewrite Hn.
      change (to_Z 0) with 0.
      destruct (Hsepf t' rg' Hg') as [Hs | Hs]; unfold rg_ival in Hs; cbn [fst snd] in Hs; lia.
    + apply fxs_eqb_true in E'. subst t'. inversion Hg'; subst rg'. cbn [rg_len rg_lo]. rewrite Hn.
      change (to_Z 0) with 0.
      destruct (Hsepf t rg Hg) as [Hs | Hs]; unfold rg_ival in Hs; cbn [fst snd] in Hs; lia.
    + exact (Hsep t t' rg rg' Hne Hg Hg').
Qed.

(* [comment removed for export] *)
Lemma fxs_sep_from_agree : forall n rho rho'' M lo hi,
  agree n rho rho'' -> regions_lt n M ->
  sep_from rho M lo hi -> sep_from rho'' M lo hi.
Proof.
  intros n rho rho'' M lo hi [_ Hag] Hlt Hs t rg Hget.
  specialize (Hs t rg Hget). unfold rg_ival in *. rewrite (Hag t (Hlt t rg Hget)). exact Hs.
Qed.

Lemma fxs_fresh_none : forall n (M : itrie region), regions_lt n M -> iget n M = None.
Proof.
  intros n M Hlt. destruct (iget n M) as [rg |] eqn:E; [| reflexivity].
  pose proof (Hlt n rg E). lia.
Qed.

Lemma fxs_n_neq0 : forall n : int, 0 < to_Z n -> n <> 0%uint63.
Proof. intros n H ->. change (to_Z 0) with 0 in H. lia. Qed.

(* [comment removed for export] *)
Lemma fxs_grant_bounds : forall (a : word) (len : int),
  bv_unsigned a mod 4096 = 0 -> 0 < bv_unsigned a -> bv_unsigned a + to_Z len <= 2 ^ 47 ->
  to_Z grant_clo <= bv_unsigned a <= to_Z (grant_chi len).
Proof.
  intros a len Hal Ha0 Htop. pose proof (i63_range len) as Hl.
  unfold grant_clo, grant_chi. rewrite sub_spec. change (to_Z 140737488355328) with (2 ^ 47).
  change (to_Z 4096) with 4096.
  assert (Hl47 : to_Z len <= 2 ^ 47) by lia.
  rewrite Z.mod_small by (change wB with (2 ^ 63); lia).
  split; [| lia].
  assert (E : bv_unsigned a = 4096 * (bv_unsigned a / 4096)) by (apply Z.div_exact; [lia | exact Hal]).
  assert (0 < bv_unsigned a / 4096) by lia. lia.
Qed.

(* [comment removed for export] *)
Theorem fx_grant_sound : forall n rho F ms a len,
  Rn n rho F ms -> at_ecall F ->
  0 < to_Z n -> to_Z n < 2 ^ 60 ->
  regions_lt n (f_mem F) ->
  0 < to_Z len <= 2 ^ 62 -> to_Z len mod 4096 = 0 ->
  bv_unsigned a mod 4096 = 0 -> 0 < bv_unsigned a -> bv_unsigned a + to_Z len < 2 ^ 63 ->
  bv_unsigned a + to_Z len <= 2 ^ 47 ->                     (* [comment removed for export] *)
  sep_from rho (f_mem F) (bv_unsigned a) (bv_unsigned a + to_Z len) ->
  Rn (n + 1)%uint63 (rho_upd rho n a) (fx_grant F n len)
     (sysret (ms_pend ms) a (apply_zeros (ms_mem ms) [(a, Z_to_bv 64 (to_Z len))])).
Proof.
  intros n rho F ms a len HRn Hpc Hn0 Hnb Hlt Hlen Hlenal Hal Ha0 Hhi H47 Hsep rho'' Hag''.
  destruct (agree_upd n rho a rho'' ltac:(lia) Hag'') as [Hag Hna].
  pose proof (HRn rho'' Hag) as HR. pose proof (proj1 Hag'') as Hrho0.
  assert (Hulen : bv_unsigned (Z_to_bv 64 (to_Z len)) = to_Z len) by (apply fxs_u64_lit; lia).
  unfold fx_grant. apply fxs_R_sysret; [exact HR | exact Hpc | |].
  - rewrite (fk_dv_plain rho'' (FV n w_zero)) by (cbn [vtag]; lia).
    cbn [vtag vw]. rewrite Hna, wbv_w_zero. unfold w0. apply fxs_bv_add_0.
  - apply (fxs_mem_ok_fresh rho'' (f_mem F) (ms_mem ms) _ n a len (Some PKZero) grant_clo (grant_chi len));
      try assumption; try lia.
    + exact (fxs_grant_bounds a len Hal Ha0 H47).
    + exact (R_mem _ _ _ _ _ HR).
    + apply fxs_n_neq0. exact Hn0.
    + apply fxs_fresh_none. exact Hlt.
    + eapply fxs_sep_from_agree; eassumption.
    + intros x Hx. apply fxs_zeros_out. rewrite Hulen. exact Hx.
    + intros pn p Hpn Hpa. unfold page_at in Hpa. cbn [rg_pages rg_dflt] in Hpa.
      rewrite iget_iempty in Hpa.
      rewrite (fxs_eqb_false n 0%uint63) in Hpa by (change (to_Z 0) with 0; lia).
      destruct (page_in_region (RG 0 len 12 (Some PKZero) iempty grant_clo (grant_chi len)) pn) eqn:Epr; [| discriminate Hpa].
      inversion Hpa; subst p. clear Hpa.
      destruct (fxs_page_in_region_spec _ pn Hpn Epr) as (_ & Hup0 & _ & _). cbn [rg_len] in Hup0.
      pose proof (fxs_page_whole _ _ Hlenal Hup0) as Hup. pose proof (to_Z_bounded pn) as Hpnb.
      split; [| lia].
      apply fxs_page_ok_zero; [exact Hrho0 |].
      intros j Hj. apply fxs_zeros_in. rewrite Hulen.
      rewrite fxs_adr_unsigned by (rewrite ?Hna; lia). rewrite Hna. lia.
Qed.

(* [comment removed for export] *)
Theorem fx_grant_na_sound : forall n rho F ms a len,
  Rn n rho F ms -> at_ecall F ->
  0 < to_Z n -> to_Z n < 2 ^ 60 ->
  regions_lt n (f_mem F) ->
  0 < to_Z len <= 2 ^ 62 -> to_Z len mod 4096 = 0 ->
  bv_unsigned a mod 4096 = 0 -> 0 < bv_unsigned a -> bv_unsigned a + to_Z len < 2 ^ 63 ->
  bv_unsigned a + to_Z len <= 2 ^ 47 ->                     (* [comment removed for export] *)
  sep_from rho (f_mem F) (bv_unsigned a) (bv_unsigned a + to_Z len) ->
  Rn (n + 1)%uint63 (rho_upd rho n a) (fx_grant_na F n len)
     (sysret (ms_pend ms) a (apply_unmaps (ms_mem ms) [(a, Z_to_bv 64 (to_Z len))])).
Proof.
  intros n rho F ms a len HRn Hpc Hn0 Hnb Hlt Hlen Hlenal Hal Ha0 Hhi H47 Hsep rho'' Hag''.
  destruct (agree_upd n rho a rho'' ltac:(lia) Hag'') as [Hag Hna].
  pose proof (HRn rho'' Hag) as HR.
  assert (Hulen : bv_unsigned (Z_to_bv 64 (to_Z len)) = to_Z len) by (apply fxs_u64_lit; lia).
  unfold fx_grant_na. apply fxs_R_sysret; [exact HR | exact Hpc | |].
  - rewrite (fk_dv_plain rho'' (FV n w_zero)) by (cbn [vtag]; lia).
    cbn [vtag vw]. rewrite Hna, wbv_w_zero. unfold w0. apply fxs_bv_add_0.
  - apply (fxs_mem_ok_fresh rho'' (f_mem F) (ms_mem ms) _ n a len None grant_clo (grant_chi len));
      try assumption; try lia.
    + exact (fxs_grant_bounds a len Hal Ha0 H47).
    + exact (R_mem _ _ _ _ _ HR).
    + apply fxs_n_neq0. exact Hn0.
    + apply fxs_fresh_none. exact Hlt.
    + eapply fxs_sep_from_agree; eassumption.
    + intros x Hx. apply fxs_unmaps_out. rewrite Hulen. exact Hx.
    + intros pn p Hpn Hpa. unfold page_at in Hpa. cbn [rg_pages rg_dflt] in Hpa.
      rewrite iget_iempty in Hpa.
      rewrite (fxs_eqb_false n 0%uint63) in Hpa by (change (to_Z 0) with 0; lia).
      discriminate Hpa.
Qed.

(* [comment removed for export] *)
Theorem fx_unmap_sound : forall n rho F ms t rg,
  Rn n rho F ms -> at_ecall F ->
  iget t (f_mem F) = Some rg -> t <> 0%uint63 -> to_Z t < to_Z n -> to_Z (rg_lo rg) = 0 ->
  Rn n rho (fx_unmap F t)
     (sysret (ms_pend ms) (Z_to_bv 64 0) (apply_unmaps (ms_mem ms) [(rho t, Z_to_bv 64 (to_Z (rg_len rg)))])).
Proof.
  intros n rho F ms t rg HRn Hpc Hget Ht0 Htn Hlo0 rho' Hag.
  pose proof (HRn rho' Hag) as HR. destruct Hag as [Hrho0 Hag].
  pose proof (Hag t Htn) as Hrt.
  destruct (R_mem _ _ _ _ _ HR) as [Hregs Hsep].
  destruct (Hregs t rg Hget) as [(Htpl & Hlen & Hhi & _ & _) _].
  pose proof (to_Z_bounded (rg_len rg)) as Hlb.
  assert (Hulen : bv_unsigned (Z_to_bv 64 (to_Z (rg_len rg))) = to_Z (rg_len rg))
    by (apply fxs_u64_lit; lia).
  unfold fx_unmap. apply fxs_R_sysret; [exact HR | exact Hpc | |].
  - rewrite (fk_dv_conc rho' w_zero Hrho0). apply wbv_w_zero.
  - split.
    + intros t' rg' Hget'. rewrite iget_iremove in Hget'.
      destruct (t' =? t)%uint63 eqn:E; [discriminate Hget' |].
      assert (Hne : t <> t') by (intros ->; rewrite Uint63.eqb_refl in E; discriminate E).
      destruct (Hregs t' rg' Hget') as [Hrg' Hpages]. split; [exact Hrg' |].
      apply (fxs_region_frame rho' (ms_mem ms) _ t' rg' Hrg'); [| exact Hpages].
      intros x Hx. apply fxs_unmaps_out. rewrite Hulen, <- Hrt.
      destruct (Hsep t t' rg rg' Hne Hget Hget') as [Hs | Hs]; lia.
    + intros t1 t2 rg1 rg2 Hne H1 H2. rewrite iget_iremove in H1, H2.
      destruct (t1 =? t)%uint63; [discriminate H1 |]. destruct (t2 =? t)%uint63; [discriminate H2 |].
      exact (Hsep t1 t2 rg1 rg2 Hne H1 H2).
Qed.

(* [comment removed for export] *)
Theorem fx_ret_sound : forall n rho F ms v w,
  Rn n rho F ms -> at_ecall F ->
  (forall rho', agree n rho rho' -> dv rho' v = w) ->
  Rn n rho (fx_ret F v) (sysret (ms_pend ms) w (ms_mem ms)).
Proof.
  intros n rho F ms v w HRn Hpc Hv rho' Hag.
  pose proof (HRn rho' Hag) as HR. unfold fx_ret.
  apply fxs_R_sysret; [exact HR | exact Hpc | exact (Hv rho' Hag) | exact (R_mem _ _ _ _ _ HR)].
Qed.

(* [comment removed for export] *)
Lemma fxs_mem_ok_repage : forall rho M m m' t rg pages' P pn k,
  mem_ok segs IM rho M m ->
  iget t M = Some rg ->
  to_Z pn + Z.of_nat k < 2 ^ 50 ->
  to_Z (rg_lo rg) <= to_Z pn * 4096 -> (to_Z pn + Z.of_nat k) * 4096 <= to_Z (rg_len rg) ->
  (forall q, iget q pages' =
             if (to_Z pn <=? to_Z q) && (to_Z q <? to_Z pn + Z.of_nat k) then Some P
             else iget q (rg_pages rg)) ->
  (forall x : word,
     (bv_unsigned x < bv_unsigned (rho t) + to_Z pn * 4096
      \/ bv_unsigned (rho t) + (to_Z pn + Z.of_nat k) * 4096 <= bv_unsigned x) -> m' x = m x) ->
  (forall q, to_Z pn <= to_Z q < to_Z pn + Z.of_nat k -> page_ok segs IM rho m' t q 512 P) ->
  mem_ok segs IM rho
    (iset t (RGK (rg_lo rg) (rg_len rg) (rg_align rg) (rg_dflt rg) pages' (rg_clo rg) (rg_chi rg) (rg_kind rg)) M) m'.
Proof.
  intros rho M m m' t rg pages' P pn k [Hregs Hsep] Hget Hpk Hlo Hup Hpages' Hout HP.
  destruct (Hregs t rg Hget) as [Hrg Hpgs].
  pose proof (to_Z_bounded pn) as Hpnb.
  split.
  - intros t' rg' Hget'. rewrite iget_iset in Hget'.
    destruct (t' =? t)%uint63 eqn:E.
    + apply fxs_eqb_true in E. subst t'. inversion Hget'; subst rg'. clear Hget'. split; [exact Hrg |].
      intros q p Hq Hpa. cbn [rg_lo rg_len].
      unfold page_at in Hpa. cbn [rg_pages rg_dflt] in Hpa. rewrite Hpages' in Hpa.
      destruct ((to_Z pn <=? to_Z q) && (to_Z q <? to_Z pn + Z.of_nat k)) eqn:Ein.
      * inversion Hpa; subst p. apply andb_true_iff in Ein as [E1 E2].
        apply Z.leb_le in E1. apply Z.ltb_lt in E2.
        assert (Hwhole : to_Z q * 4096 + 4096 <= to_Z (rg_len rg)) by lia.
        unfold clim. cbn [rg_len]. fold (clim rg q). rewrite (fxs_clim_full rg q Hwhole).
        split; [apply HP; lia | split; [lia | split; [lia | left; exact Hwhole]]].
      * (* [comment removed for export] *)
        assert (Hpa0 : page_at IM rg t q = Some p).
        { unfold page_at. unfold page_in_region in *. cbn [rg_lo rg_len] in Hpa. exact Hpa. }
        destruct (Hpgs q p Hq Hpa0) as (Hok & Hqlo & Hqup & Hqal).
        unfold clim. cbn [rg_len]. fold (clim rg q).
        split; [| split; [|split]; assumption].
        eapply fxs_page_ok_frame; [| exact Hok].
        intros j Hj. destruct (fxs_clim_bytes rg q j Hj) as [Hjl Hj4].
        apply Hout. rewrite (fxs_page_addr rho t rg q j Hrg Hqlo Hjl ltac:(lia)).
        apply andb_false_iff in Ein as [E1 | E2]; [apply Z.leb_gt in E1 | apply Z.ltb_ge in E2]; lia.
    + assert (Hne : t <> t') by (intros ->; rewrite Uint63.eqb_refl in E; discriminate E).
      destruct (Hregs t' rg' Hget') as [Hrg' Hpgs']. split; [exact Hrg' |].
      apply (fxs_region_frame rho m m' t' rg' Hrg'); [| exact Hpgs'].
      intros x Hx. apply Hout.
      destruct (Hsep t t' rg rg' Hne Hget Hget') as [Hs | Hs]; lia.
  - intros t1 t2 rg1 rg2 Hne H1 H2. rewrite iget_iset in H1, H2.
    destruct (t1 =? t)%uint63 eqn:E1; destruct (t2 =? t)%uint63 eqn:E2.
    + apply fxs_eqb_true in E1, E2. congruence.
    + apply fxs_eqb_true in E1. subst t1. inversion H1; subst rg1. cbn [rg_lo rg_len].
      exact (Hsep t t2 rg rg2 Hne Hget H2).
    + apply fxs_eqb_true in E2. subst t2. inversion H2; subst rg2. cbn [rg_lo rg_len].
      exact (Hsep t1 t rg1 rg Hne H1 Hget).
    + exact (Hsep t1 t2 rg1 rg2 Hne H1 H2).
Qed.

(* [comment removed for export] *)
Theorem fx_guard_sound : forall n rho F ms t rg pn k,
  Rn n rho F ms -> at_ecall F ->
  iget t (f_mem F) = Some rg -> to_Z t < to_Z n ->
  (0 < k)%nat -> to_Z pn + Z.of_nat k < 2 ^ 50 ->
  to_Z (rg_lo rg) <= to_Z pn * 4096 -> (to_Z pn + Z.of_nat k) * 4096 <= to_Z (rg_len rg) ->
  Rn n rho (fx_guard F t pn k)
     (sysret (ms_pend ms) (adr rho t (to_Z pn * 4096))
             (apply_unmaps (ms_mem ms) [(adr rho t (to_Z pn * 4096), Z_to_bv 64 (Z.of_nat k * 4096))])).
Proof.
  intros n rho F ms t rg pn k HRn Hpc Hget Htn Hk Hpk Hlo Hup rho' Hag.
  pose proof (HRn rho' Hag) as HR. destruct Hag as [Hrho0 Hag].
  pose proof (Hag t Htn) as Hrt.
  destruct (R_mem _ _ _ _ _ HR) as [Hregs Hsep].
  destruct (Hregs t rg Hget) as [(Htpl & Hlen & Hhi & _ & _) _].
  pose proof (to_Z_bounded pn) as Hpnb. pose proof (fxs_u64 (rho' t)) as Hrb.
  assert (Huk : bv_unsigned (Z_to_bv 64 (Z.of_nat k * 4096)) = Z.of_nat k * 4096)
    by (apply fxs_u64_lit; lia).
  assert (Hua : bv_unsigned (adr rho t (to_Z pn * 4096)) = bv_unsigned (rho' t) + to_Z pn * 4096).
  { rewrite <- (fxs_adr_ext rho rho' t _ Hrt). apply fxs_adr_unsigned; lia. }
  unfold fx_guard, upd_region. rewrite Hget.
  apply fxs_R_sysret; [exact HR | exact Hpc | |].
  - rewrite (fk_dv_plain rho' (FV t (W64 0 (pn << 12)%uint63))) by exact Htpl.
    cbn [vtag vw]. rewrite fxs_wbv_W64_0, (fxs_to_Z_lsl12 pn) by lia.
    unfold adr. rewrite Hrt. reflexivity.
  - apply (fxs_mem_ok_repage rho' (f_mem F) (ms_mem ms) _ t rg _ (PG false PKUnk iempty) pn k
             (R_mem _ _ _ _ _ HR) Hget Hpk Hlo Hup).
    + intros q. apply iget_hole_pages. lia.
    + intros x Hx. apply fxs_unmaps_out. rewrite Hua, Huk. lia.
    + intros q _. apply fxs_page_ok_hole.
Qed.

(* [comment removed for export] *)
Theorem fx_expose_sound : forall n rho F ms t rg pn k,
  Rn n rho F ms -> at_ecall F ->
  iget t (f_mem F) = Some rg -> to_Z t < to_Z n ->
  (0 < k)%nat -> to_Z pn + Z.of_nat k < 2 ^ 50 ->
  to_Z (rg_lo rg) <= to_Z pn * 4096 -> (to_Z pn + Z.of_nat k) * 4096 <= to_Z (rg_len rg) ->
  Rn n rho (fx_expose F t pn k)
     (sysret (ms_pend ms) (Z_to_bv 64 0)
             (apply_zeros (ms_mem ms) [(adr rho t (to_Z pn * 4096), Z_to_bv 64 (Z.of_nat k * 4096))])).
Proof.
  intros n rho F ms t rg pn k HRn Hpc Hget Htn Hk Hpk Hlo Hup rho' Hag.
  pose proof (HRn rho' Hag) as HR. destruct Hag as [Hrho0 Hag].
  pose proof (Hag t Htn) as Hrt.
  destruct (R_mem _ _ _ _ _ HR) as [Hregs Hsep].
  destruct (Hregs t rg Hget) as [Hrg _]. pose proof Hrg as (Htpl & Hlen & Hhi & _ & _).
  pose proof (to_Z_bounded pn) as Hpnb. pose proof (fxs_u64 (rho' t)) as Hrb.
  assert (Huk : bv_unsigned (Z_to_bv 64 (Z.of_nat k * 4096)) = Z.of_nat k * 4096)
    by (apply fxs_u64_lit; lia).
  assert (Hua : bv_unsigned (adr rho t (to_Z pn * 4096)) = bv_unsigned (rho' t) + to_Z pn * 4096).
  { rewrite <- (fxs_adr_ext rho rho' t _ Hrt). apply fxs_adr_unsigned; lia. }
  unfold fx_expose, upd_region. rewrite Hget.
  apply fxs_R_sysret; [exact HR | exact Hpc | |].
  - rewrite (fk_dv_conc rho' w_zero Hrho0). apply wbv_w_zero.
  - apply (fxs_mem_ok_repage rho' (f_mem F) (ms_mem ms) _ t rg _ (PG true PKZero iempty) pn k
             (R_mem _ _ _ _ _ HR) Hget Hpk Hlo Hup).
    + intros q. apply iget_zero_pages. lia.
    + intros x Hx. apply fxs_zeros_out. rewrite Hua, Huk. lia.
    + intros q Hq. apply fxs_page_ok_zero; [exact Hrho0 |].
      intros j Hj. apply fxs_zeros_in. rewrite Hua, Huk.
      rewrite (fxs_page_addr rho' t rg q j Hrg) by lia. lia.
Qed.

(* [comment removed for export] *)
Theorem fx_commit_sound : forall n rho F ms t rg pn k,
  Rn n rho F ms -> at_ecall F ->
  iget t (f_mem F) = Some rg -> to_Z t < to_Z n ->
  (0 < k)%nat -> to_Z pn + Z.of_nat k < 2 ^ 50 ->
  to_Z (rg_lo rg) <= to_Z pn * 4096 -> (to_Z pn + Z.of_nat k) * 4096 <= to_Z (rg_len rg) ->
  Rn n rho (fx_commit F t pn k)
     (sysret (ms_pend ms) (adr rho t (to_Z pn * 4096))
             (apply_zeros (ms_mem ms) [(adr rho t (to_Z pn * 4096), Z_to_bv 64 (Z.of_nat k * 4096))])).
Proof.
  intros n rho F ms t rg pn k HRn Hpc Hget Htn Hk Hpk Hlo Hup rho' Hag.
  pose proof (HRn rho' Hag) as HR. destruct Hag as [Hrho0 Hag].
  pose proof (Hag t Htn) as Hrt.
  destruct (R_mem _ _ _ _ _ HR) as [Hregs Hsep].
  destruct (Hregs t rg Hget) as [Hrg _]. pose proof Hrg as (Htpl & Hlen & Hhi & _ & _).
  pose proof (to_Z_bounded pn) as Hpnb. pose proof (fxs_u64 (rho' t)) as Hrb.
  assert (Huk : bv_unsigned (Z_to_bv 64 (Z.of_nat k * 4096)) = Z.of_nat k * 4096)
    by (apply fxs_u64_lit; lia).
  assert (Hua : bv_unsigned (adr rho t (to_Z pn * 4096)) = bv_unsigned (rho' t) + to_Z pn * 4096).
  { rewrite <- (fxs_adr_ext rho rho' t _ Hrt). apply fxs_adr_unsigned; lia. }
  unfold fx_commit, upd_region. rewrite Hget.
  apply fxs_R_sysret; [exact HR | exact Hpc | |].
  - rewrite (fk_dv_plain rho' (FV t (W64 0 (pn << 12)%uint63))) by exact Htpl.
    cbn [vtag vw]. rewrite fxs_wbv_W64_0, (fxs_to_Z_lsl12 pn) by lia.
    unfold adr. rewrite Hrt. reflexivity.
  - apply (fxs_mem_ok_repage rho' (f_mem F) (ms_mem ms) _ t rg _ (PG true PKZero iempty) pn k
             (R_mem _ _ _ _ _ HR) Hget Hpk Hlo Hup).
    + intros q. apply iget_zero_pages. lia.
    + intros x Hx. apply fxs_zeros_out. rewrite Hua, Huk. lia.
    + intros q Hq. apply fxs_page_ok_zero; [exact Hrho0 |].
      intros j Hj. apply fxs_zeros_in. rewrite Hua, Huk.
      rewrite (fxs_page_addr rho' t rg q j Hrg) by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma fxs_Rn_tag_lt : forall n rho F ms rho' t rg,
  Rn n rho F ms -> agree n rho rho' -> 0 < to_Z n ->
  iget t (f_mem F) = Some rg -> to_Z t < to_Z n.
Proof.
  intros n rho F ms rho' t rg HRn [H0 Hag] Hn Hget.
  destruct (Z_lt_le_dec (to_Z t) (to_Z n)) as [Hlt | Hge]; [exact Hlt | exfalso].
  set (rho2 := fun x : int => if (x =? t)%uint63 then Z_to_bv 64 (2 ^ 63) else rho' x).
  assert (Hag2 : agree n rho rho2).
  { split.
    - unfold rho2. rewrite (fxs_eqb_false 0%uint63 t) by (change (to_Z 0) with 0; lia). exact H0.
    - intros x Hx. unfold rho2. rewrite (fxs_eqb_false x t) by lia. apply Hag. exact Hx. }
  destruct (proj1 (R_mem _ _ _ _ _ (HRn rho2 Hag2)) t rg Hget) as [(_ & _ & Hhi & _) _].
  unfold rho2 in Hhi. rewrite Uint63.eqb_refl in Hhi.
  rewrite fxs_u64_lit in Hhi by lia. pose proof (to_Z_bounded (rg_len rg)). lia.
Qed.

(* [comment removed for export] *)
Lemma fxs_page_in_region_grow : forall rg len' q k p0,
  p0 * 4096 = to_Z (rg_len rg) ->
  to_Z (rg_len rg) <= 2 ^ 62 ->
  to_Z len' = to_Z (rg_len rg) + Z.of_nat k * 4096 ->
  ~ (p0 <= to_Z q < p0 + Z.of_nat k) ->
  page_in_region (RGK (rg_lo rg) len' (rg_align rg) (rg_dflt rg) (rg_pages rg) (rg_clo rg) (rg_chi rg) (rg_kind rg)) q = true ->
  page_in_region rg q = true.
Proof.
  intros rg len' q k p0 Hp0 Hlen Hlen' Hout H.
  assert (Hq : to_Z q < 2 ^ 50).
  { unfold page_in_region in H. rewrite !andb_true_iff in H. destruct H as [[[Hq _] _] _].
    apply Uint63.ltb_spec in Hq. exact Hq. }
  destruct (fxs_page_in_region_spec _ q Hq H) as (Hlo & Hup0 & _ & _). cbn [rg_lo rg_len] in Hlo, Hup0.
  pose proof (to_Z_bounded q) as Hqb.
  assert (Hup : to_Z q * 4096 + 4096 <= to_Z (rg_len rg)) by (clear - Hp0 Hlen' Hout Hup0; lia).
  unfold page_in_region. rewrite !andb_true_iff. split; [split; [split|]|].
  - apply Uint63.ltb_spec. change (to_Z 1125899906842624) with (2 ^ 50). exact Hq.
  - apply Uint63.leb_spec. rewrite (fxs_to_Z_lsl12 q Hq). exact Hlo.
  - apply orb_true_iff. left. apply Uint63.leb_spec. rewrite Uint63.add_spec, (fxs_to_Z_lsl12 q Hq).
    change (to_Z 4096) with 4096. rewrite Z.mod_small by (rewrite fxs_wB; lia). exact Hup.
  - apply Uint63.leb_spec. change (to_Z 4611686018427387904) with (2 ^ 62). exact Hlen.
Qed.

(* [comment removed for export] *)
Theorem fx_brk_grow_sound : forall n rho F ms t rg k,
  Rn n rho F ms -> at_ecall F ->
  iget t (f_mem F) = Some rg -> to_Z t < to_Z n ->
  (0 < k)%nat -> to_Z (rg_len rg) mod 4096 = 0 ->
  to_Z (rg_lo rg) <= to_Z (rg_len rg) ->
  to_Z (rg_len rg) + Z.of_nat k * 4096 <= 2 ^ 62 ->
  bv_unsigned (rho t) + to_Z (rg_len rg) + Z.of_nat k * 4096 < 2 ^ 63 ->
  (forall t' rg', t' <> t -> iget t' (f_mem F) = Some rg' ->
      bv_unsigned (rho t) + to_Z (rg_len rg) + Z.of_nat k * 4096 <= fst (rg_ival rho t' rg')
      \/ snd (rg_ival rho t' rg') <= bv_unsigned (rho t) + to_Z (rg_lo rg)) ->
  Rn n rho (fx_brk_grow F t k)
     (sysret (ms_pend ms) (adr rho t (to_Z (rg_len rg) + Z.of_nat k * 4096))
             (apply_zeros (ms_mem ms) [(adr rho t (to_Z (rg_len rg)), Z_to_bv 64 (Z.of_nat k * 4096))])).
Proof.
  intros n rho F ms t rg k HRn Hpc Hget Htn Hk Hal Hlole Hlen2 Hhi2 Hsepn rho' Hag.
  (* [comment removed for export] *)
  set (pn0 := (rg_len rg >> 12)%uint63).
  assert (Hpn0 : to_Z pn0 = to_Z (rg_len rg) / 4096) by (unfold pn0; apply fxs_to_Z_lsr12).
  assert (Hpn0m : to_Z pn0 * 4096 = to_Z (rg_len rg)).
  { rewrite Hpn0. pose proof (Z.div_mod (to_Z (rg_len rg)) 4096 ltac:(lia)) as Hdm.
    clear - Hdm Hal. lia. }
  pose proof (fun len' q => fxs_page_in_region_grow rg len' q k (to_Z pn0) Hpn0m) as Hgrow.
  clear Hal Hpn0.
  pose proof (HRn rho' Hag) as HR.
  assert (Hn0 : 0 < to_Z n) by (pose proof (to_Z_bounded t); lia).
  assert (Htags : forall t' rg', iget t' (f_mem F) = Some rg' -> rho' t' = rho t').
  { intros t' rg' Hg'. apply (proj2 Hag). exact (fxs_Rn_tag_lt n rho F ms rho' t' rg' HRn Hag Hn0 Hg'). }
  destruct Hag as [Hrho0 Hag]. pose proof (Hag t Htn) as Hrt.
  destruct (R_mem _ _ _ _ _ HR) as [Hregs Hsep].
  destruct (Hregs t rg Hget) as [Hrg Hpgs]. pose proof Hrg as (Htpl & Hlen & Hhi & Hpos & _).
  pose proof (to_Z_bounded (rg_len rg)) as Hlb. pose proof (to_Z_bounded (rg_lo rg)) as Hlob.
  pose proof (fxs_u64 (rho' t)) as Hrb.
  (* [comment removed for export] *)
  set (kk := of_Z (Z.of_nat k)).
  assert (Hkk : to_Z kk = Z.of_nat k).
  { unfold kk. rewrite Uint63.of_Z_spec. apply Z.mod_small. rewrite fxs_wB. lia. }
  assert (Hkk12 : to_Z (kk << 12)%uint63 = Z.of_nat k * 4096).
  { rewrite fxs_to_Z_lsl12' by (rewrite Hkk; lia). rewrite Hkk. reflexivity. }
  set (len' := (rg_len rg + (kk << 12))%uint63).
  assert (Hlen' : to_Z len' = to_Z (rg_len rg) + Z.of_nat k * 4096).
  { unfold len'. rewrite Uint63.add_spec, Hkk12. apply Z.mod_small. rewrite fxs_wB. lia. }
  assert (Huk : bv_unsigned (Z_to_bv 64 (Z.of_nat k * 4096)) = Z.of_nat k * 4096)
    by (apply fxs_u64_lit; lia).
  assert (Hua : bv_unsigned (adr rho t (to_Z (rg_len rg))) = bv_unsigned (rho' t) + to_Z (rg_len rg)).
  { rewrite <- (fxs_adr_ext rho rho' t _ Hrt). apply fxs_adr_unsigned; lia. }
  unfold fx_brk_grow. rewrite Hget. cbv zeta. fold kk. fold len'. fold pn0.
  set (rg' := RGK (rg_lo rg) len' (rg_align rg) (rg_dflt rg) (zero_pages k pn0 (rg_pages rg)) (rg_clo rg) (rg_chi rg) (rg_kind rg)).
  assert (Hrg' : region_ok rho' t rg').
  { unfold region_ok, rg'. cbn [rg_len rg_lo rg_align]. rewrite Hlen'.
    split; [exact Htpl |]. split; [lia |]. split; [rewrite Hrt; lia |]. split; [exact Hpos |].
    exact (proj2 (proj2 (proj2 (proj2 Hrg)))). }
  apply fxs_R_sysret; [exact HR | exact Hpc | |].
  - rewrite (fk_dv_plain rho' (FV t (W64 0 len'))) by exact Htpl.
    cbn [vtag vw]. rewrite fxs_wbv_W64_0, Hlen'. unfold adr. rewrite Hrt. reflexivity.
  - split.
    + intros t' rg1 Hget'. rewrite iget_iset in Hget'.
      destruct (t' =? t)%uint63 eqn:E.
      * apply fxs_eqb_true in E. subst t'. inversion Hget'; subst rg1. clear Hget'.
        split; [exact Hrg' |].
        intros q p Hq Hpa.
        assert (Hlo' : rg_lo rg' = rg_lo rg) by reflexivity.
        assert (Hln' : rg_len rg' = len') by reflexivity.
        match goal with |- page_ok _ _ _ ?mem _ _ _ _ /\ _ =>
          cut (page_ok segs IM rho' mem t q 512 p
               /\ to_Z (rg_lo rg) <= to_Z q * 4096 /\ to_Z q * 4096 + 4096 <= to_Z (rg_len rg) + Z.of_nat k * 4096) end.
        { intros (Hok & Hqlo & Hqup).
          rewrite (fxs_clim_full rg' q) by (rewrite Hln', Hlen'; exact Hqup).
          rewrite Hlo', Hln', Hlen'. split; [exact Hok|]. split; [exact Hqlo|]. split; [lia | left; exact Hqup]. }
        unfold page_at in Hpa. unfold rg' in Hpa. cbn [rg_pages rg_dflt] in Hpa.
        rewrite iget_zero_pages in Hpa by lia.
        destruct ((to_Z pn0 <=? to_Z q) && (to_Z q <? to_Z pn0 + Z.of_nat k)) eqn:Ein.
        -- (* [comment removed for export] *)
           inversion Hpa; subst p. apply andb_true_iff in Ein as [E1 E2].
           apply Z.leb_le in E1. apply Z.ltb_lt in E2. split; [| lia].
           apply fxs_page_ok_zero; [exact Hrho0 |].
           intros j Hj. apply fxs_zeros_in. rewrite Hua, Huk.
           pose proof (to_Z_bounded q) as Hqb.
           rewrite fxs_adr_unsigned by lia. lia.
        -- (* [comment removed for export] *)
           assert (Hout : ~ (to_Z pn0 <= to_Z q < to_Z pn0 + Z.of_nat k)).
           { intros [H1 H2].
             rewrite (proj2 (Z.leb_le _ _) H1), (proj2 (Z.ltb_lt _ _) H2) in Ein. discriminate Ein. }
           assert (Hpa0 : page_at IM rg t q = Some p).
           { unfold page_at. destruct (iget q (rg_pages rg)) as [p0 |]; [exact Hpa |].
             destruct (if (t =? 0)%uint63 then find_seg IM (q << 12) else None) as [sg |]; [exact Hpa |].
             destruct (rg_dflt rg) as [kd |]; [| exact Hpa].
             destruct (page_in_region (RGK (rg_lo rg) len' (rg_align rg) (Some kd)
                                          (zero_pages k pn0 (rg_pages rg)) (rg_clo rg) (rg_chi rg) (rg_kind rg)) q) eqn:Epr;
               [| discriminate Hpa].
             assert (Epr0 : page_in_region rg q = true).
             { apply (Hgrow len' q Hlen Hlen' Hout).
               unfold page_in_region in *. cbn [rg_lo rg_len] in *. exact Epr. }
             rewrite Epr0. exact Hpa. }
           destruct (Hpgs q p Hq Hpa0) as (Hok & Hqlo & Hqup0 & _).
           assert (Hqup : to_Z q * 4096 + 4096 <= to_Z (rg_len rg)).
           { pose proof (to_Z_bounded pn0). pose proof (to_Z_bounded q). clear - Hqup0 Hpn0m. nia. }
           rewrite (fxs_clim_full rg q Hqup) in Hok. split; [| lia].
           eapply fxs_page_ok_frame; [| exact Hok].
           intros j Hj. apply fxs_zeros_out. rewrite Hua, Huk.
           rewrite (fxs_page_addr rho' t rg q j Hrg Hqlo ltac:(lia) ltac:(lia)). lia.
      * assert (Hne : t' <> t) by (intros ->; rewrite Uint63.eqb_refl in E; discriminate E).
        destruct (Hregs t' rg1 Hget') as [Hrg1 Hpgs1]. split; [exact Hrg1 |].
        apply (fxs_region_frame rho' (ms_mem ms) _ t' rg1 Hrg1); [| exact Hpgs1].
        intros x Hx. apply fxs_zeros_out. rewrite Hua, Huk.
        destruct (Hsepn t' rg1 Hne Hget') as [Hs | Hs]; unfold rg_ival in Hs; cbn [fst snd] in Hs;
          rewrite <- (Htags t' rg1 Hget'), <- Hrt in Hs; lia.
    + intros t1 t2 rg1 rg2 Hne H1 H2. rewrite iget_iset in H1, H2.
      destruct (t1 =? t)%uint63 eqn:E1; destruct (t2 =? t)%uint63 eqn:E2.
      * apply fxs_eqb_true in E1, E2. congruence.
      * apply fxs_eqb_true in E1. subst t1. inversion H1; subst rg1. unfold rg'. cbn [rg_lo rg_len].
        rewrite Hlen'.
        destruct (Hsepn t2 rg2 ltac:(congruence) H2) as [Hs | Hs]; unfold rg_ival in Hs;
          cbn [fst snd] in Hs; rewrite <- (Htags t2 rg2 H2), <- Hrt in Hs; lia.
      * apply fxs_eqb_true in E2. subst t2. inversion H2; subst rg2. unfold rg'. cbn [rg_lo rg_len].
        rewrite Hlen'.
        destruct (Hsepn t1 rg1 ltac:(congruence) H1) as [Hs | Hs]; unfold rg_ival in Hs;
          cbn [fst snd] in Hs; rewrite <- (Htags t1 rg1 H1), <- Hrt in Hs; lia.
      * exact (Hsep t1 t2 rg1 rg2 Hne H1 H2).
Qed.
End Sys.
