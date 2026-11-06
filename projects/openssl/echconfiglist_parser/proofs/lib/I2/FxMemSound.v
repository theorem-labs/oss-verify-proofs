(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition load_result (sz : msize) (sgn : bool) (bs : list byte) : word :=
  match sz with
  | SZ1 => let v : bv 8 := bv_extract 0 8 (le_bytes_to_word bs) in if sgn then sext 64 v else zext 64 v
  | SZ2 => let v : bv 16 := bv_extract 0 16 (le_bytes_to_word bs) in if sgn then sext 64 v else zext 64 v
  | SZ4 => let v : bv 32 := bv_extract 0 32 (le_bytes_to_word bs) in if sgn then sext 64 v else zext 64 v
  | SZ8 => bv_extract 0 64 (le_bytes_to_word bs)
  end.

(* [comment removed for export] *)
Definition store_bytes_of (sz : msize) (v : word) : list byte :=
  match sz with
  | SZ1 => Z_to_le_bytes 1 (bv_unsigned (bv_extract 0 8 v))
  | SZ2 => Z_to_le_bytes 2 (bv_unsigned (bv_extract 0 16 v))
  | SZ4 => Z_to_le_bytes 4 (bv_unsigned (low32 v))
  | SZ8 => Z_to_le_bytes 8 (bv_unsigned v)
  end.

Definition msz_nat (sz : msize) : nat := match sz with SZ1 => 1 | SZ2 => 2 | SZ4 => 4 | SZ8 => 8 end.


Section MemSound.
Variable segs : list Segment.
Variable IM : fimage.
Variable rho : int -> word.
Hypothesis Hrho0 : rho 0%uint63 = Z_to_bv 64 0.

(* [comment removed for export] *)
Lemma to_Z_land7 x : to_Z (x land 7)%uint63 = to_Z x mod 8.
Proof. apply (i63_land_ones x 7%uint63 3); [reflexivity | lia]. Qed.
Lemma to_Z_land4095 x : to_Z (x land 4095)%uint63 = to_Z x mod 4096.
Proof. apply (i63_land_ones x 4095%uint63 12); [reflexivity | lia]. Qed.
Lemma to_Z_lsr12 x : to_Z (x >> 12)%uint63 = to_Z x / 4096.
Proof. rewrite lsr_spec. reflexivity. Qed.
Lemma to_Z_lsr3 x : to_Z (x >> 3)%uint63 = to_Z x / 8.
Proof. rewrite lsr_spec. reflexivity. Qed.
Lemma to_Z_msz sz : to_Z (msz_int sz) = Z.of_nat (msz_nat sz).
Proof. destruct sz; reflexivity. Qed.
Lemma msz_nat_pos sz : (1 <= msz_nat sz <= 8)%nat.
Proof. destruct sz; cbn; lia. Qed.

Lemma off_decomp o :
  0 <= o -> (o / 4096) * 4096 + ((o mod 4096) / 8) * 8 + o mod 8 = o.
Proof. intros Ho. Z.div_mod_to_equations. lia. Qed.

Lemma cell_index_range o : 0 <= o -> 0 <= (o mod 4096) / 8 < 512.
Proof. intros Ho. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Lemma blim_le rg pn : blim rg pn <= 4096.
Proof. unfold blim. lia. Qed.

Lemma clim_le rg pn : clim rg pn <= 512.
Proof. unfold clim, blim. Z.div_mod_to_equations. lia. Qed.

Lemma clim_full rg pn : to_Z pn * 4096 + 4096 <= to_Z (rg_len rg) -> clim rg pn = 512.
Proof. intros H. unfold clim, blim. rewrite Z.min_l by lia. reflexivity. Qed.

Lemma blim_full rg pn : to_Z pn * 4096 + 4096 <= to_Z (rg_len rg) -> blim rg pn = 4096.
Proof. intros H. unfold blim. lia. Qed.

(* [comment removed for export] *)
Lemma blim_bytes rg pn j : 0 <= j < blim rg pn -> to_Z pn * 4096 + j < to_Z (rg_len rg) /\ j < 4096.
Proof. unfold blim. intros Hj. lia. Qed.

Lemma blim_intro rg pn j : 0 <= j < 4096 -> to_Z pn * 4096 + j < to_Z (rg_len rg) -> 0 <= j < blim rg pn.
Proof. unfold blim. intros Hj Hb. lia. Qed.

(* [comment removed for export] *)
Lemma clim_bytes rg pn ci j :
  0 <= ci < clim rg pn -> 0 <= j < 8 -> to_Z pn * 4096 + ci * 8 + j < to_Z (rg_len rg).
Proof. unfold clim, blim. intros Hci Hj. Z.div_mod_to_equations. lia. Qed.

Lemma clim_blim rg pn ci j :
  0 <= ci < clim rg pn -> 0 <= j < 8 -> ci * 8 + j < blim rg pn.
Proof. unfold clim. intros Hci Hj. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Lemma clim_intro rg pn ci :
  0 <= ci < 512 -> to_Z pn * 4096 + ci * 8 + 8 <= to_Z (rg_len rg) -> 0 <= ci < clim rg pn.
Proof. unfold clim, blim. intros Hci Hb. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Lemma page_ok_of_whole m t pn B p :
  B mod 8 = 0 ->
  (pg_wr p = true -> forall j, 0 <= j < B -> wview segs m (adr rho t (to_Z pn * 4096 + j)) <> None) ->
  (forall ci v, 0 <= to_Z ci < B / 8 -> cell_at IM p pn ci = Some v ->
     forall j, (j < 8)%nat ->
       rview segs m (adr rho t (to_Z pn * 4096 + to_Z ci * 8 + Z.of_nat j)) = nth_error (wbytes8 (dv rho v)) j) ->
  (forall ci sl, 0 <= to_Z ci < B / 8 -> iget ci (pg_cells p) = Some (CB sl) ->
     forall j : int, 0 <= to_Z j < 8 -> slot_ok segs rho m (adr rho t (to_Z pn * 4096 + to_Z ci * 8 + to_Z j)) (sget j sl)) ->
  page_ok segs IM rho m t pn B p.
Proof.
  intros HB Hw Hc Hs. split; [exact Hw|]. split; [exact Hc|]. split.
  - intros ci sl Hci Hcb Hi j Hj. split.
    + intros _. apply Hs; [Z.div_mod_to_equations; lia | exact Hi | exact Hj].
    + intros Hout. exfalso. Z.div_mod_to_equations. lia.
  - intros ci Hci Hcut. exfalso. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma page_ok_slots_whole m t pn B p ci sl (j : int) :
  page_ok segs IM rho m t pn B p -> 0 <= to_Z ci < B / 8 -> iget ci (pg_cells p) = Some (CB sl) -> 0 <= to_Z j < 8 ->
  slot_ok segs rho m (adr rho t (to_Z pn * 4096 + to_Z ci * 8 + to_Z j)) (sget j sl).
Proof.
  intros (_ & _ & Hs & _) Hci Hi Hj.
  apply (proj1 (Hs ci sl ltac:(lia) ltac:(Z.div_mod_to_equations; lia) Hi j Hj)). Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Lemma bytes_lt_blim rg (pn : int) o n j :
  0 <= o -> o + n <= to_Z (rg_len rg) -> to_Z pn = o / 4096 -> o mod 4096 + n <= 4096 -> 0 <= j < n ->
  0 <= o mod 4096 + j < blim rg pn.
Proof. intros Ho Hin Epn Hpg Hj. unfold blim. rewrite Epn. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Lemma ci_cases rg (pn : int) o n :
  0 <= o -> 0 < n -> o mod 8 + n <= 8 -> o + n <= to_Z (rg_len rg) -> to_Z pn = o / 4096 ->
  (0 <= (o mod 4096) / 8 < clim rg pn)
  \/ ((o mod 4096) / 8 * 8 < blim rg pn < (o mod 4096) / 8 * 8 + 8).
Proof.
  intros Ho Hn Hcell Hin Epn. unfold clim, blim. rewrite Epn in *.
  Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma ci_lt_clim rg (pn : int) o n :
  0 <= o -> 0 < n -> o mod 8 + n <= 8 -> o + n <= to_Z (rg_len rg) -> to_Z pn = o / 4096 ->
  (to_Z pn * 4096 + 4096 <= to_Z (rg_len rg) \/ to_Z (rg_len rg) mod 8 = 0) ->
  0 <= (o mod 4096) / 8 < clim rg pn.
Proof.
  intros Ho Hn Hcell Hin Epn Hal. unfold clim, blim. rewrite Epn in *.
  destruct Hal as [Hal|Hal]; Z.div_mod_to_equations; lia.
Qed.


(* [comment removed for export] *)
Lemma aoff_adr t z j : aoff (adr rho t z) j = adr rho t (z + Z.of_nat j).
Proof.
  unfold aoff, adr. apply bv_eq. rewrite !bv_add_unsigned, !Z_to_bv_unsigned.
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma dv_adr t top off :
  to_Z t < 2 ^ 60 -> to_Z top mod 2 = 0 -> dv rho (FV t (W64 top off)) = adr rho t (to_Z off).
Proof.
  intros Hpl Htop. rewrite fk_dv_plain by exact Hpl. unfold adr. cbn [vtag vw]. f_equal.
  unfold wbv. rewrite (wZ_even_top top off Htop). reflexivity.
Qed.

Lemma adr_inj t z1 z2 :
  0 <= z1 < 2 ^ 64 -> 0 <= z2 < 2 ^ 64 -> adr rho t z1 = adr rho t z2 -> z1 = z2.
Proof.
  intros H1 H2 E. unfold adr in E. apply (f_equal bv_unsigned) in E.
  rewrite !bv_add_unsigned, !Z_to_bv_unsigned in E. unfold bv_wrap in E.
  change (bv_modulus 64) with (2 ^ 64) in E.
  rewrite !Zplus_mod_idemp_r in E.
  pose proof (bv_unsigned_in_range _ (rho t)) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
  assert (E' : (z1 - z2) mod 2 ^ 64 = 0).
  { replace (z1 - z2) with ((bv_unsigned (rho t) + z1) - (bv_unsigned (rho t) + z2)) by lia.
    rewrite Zminus_mod, E, Z.sub_diag. reflexivity. }
  apply Z.mod_divide in E'; [|lia]. destruct E' as [k Hk].
  assert (k = 0) by lia. lia.
Qed.

Lemma adr_unsigned t z :
  0 <= z -> bv_unsigned (rho t) + z < 2 ^ 64 ->
  bv_unsigned (adr rho t z) = bv_unsigned (rho t) + z.
Proof.
  intros Hz Hlt. unfold adr. rewrite bv_add_unsigned, Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64).
  pose proof (bv_unsigned_in_range _ (rho t)) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
  rewrite Zplus_mod_idemp_r. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma checks_inv top off sz rg :
  negb ((top land 1) =? 0)%uint63 = false ->
  negb ((off land 7) + msz_int sz <=? 8)%uint63 = false ->
  negb (in_region rg off (msz_int sz)) = false ->
  to_Z top mod 2 = 0
  /\ to_Z off mod 8 + Z.of_nat (msz_nat sz) <= 8
  /\ to_Z off < 2 ^ 62
  /\ to_Z (rg_len rg) <= 2 ^ 62
  /\ to_Z (rg_lo rg) <= to_Z off
  /\ to_Z off + Z.of_nat (msz_nat sz) <= to_Z (rg_len rg).
Proof.
  intros H1 H2 H3. apply negb_false_iff in H1, H2, H3.
  pose proof (msz_nat_pos sz) as Hn.
  pose proof (i63_range off) as Hoff.
  apply Uint63.eqb_spec in H1. apply (f_equal to_Z) in H1. rewrite i63_land1, to_Z_0 in H1.
  apply leb_spec in H2. rewrite add_spec, to_Z_land7, to_Z_msz, i63_wB in H2.
  change (to_Z 8) with 8 in H2.
  pose proof (Z.mod_pos_bound (to_Z off) 8 ltac:(lia)) as Hb.
  rewrite Z.mod_small in H2 by lia.
  unfold in_region in H3. apply andb_true_iff in H3. destruct H3 as [H3 H6].
  apply andb_true_iff in H3. destruct H3 as [H3 H5].
  apply andb_true_iff in H3. destruct H3 as [H3 H4].
  apply ltb_spec in H3. apply leb_spec in H4. apply leb_spec in H5. apply leb_spec in H6.
  change (to_Z off_bound) with (2 ^ 62) in H3, H4.
  rewrite add_spec, to_Z_msz, i63_wB in H6. rewrite Z.mod_small in H6 by lia.
  repeat split; assumption.
Qed.

(* [comment removed for export] *)
Lemma access_addr t top off (j : nat) :
  to_Z t < 2 ^ 60 -> to_Z top mod 2 = 0 ->
  adr rho t (to_Z (off >> 12)%uint63 * 4096 + to_Z ((off land 4095) >> 3)%uint63 * 8
             + Z.of_nat (Z.to_nat (to_Z off mod 8) + j))
  = aoff (dv rho (FV t (W64 top off))) j.
Proof.
  intros Hpl Htop. rewrite (dv_adr t top off Hpl Htop), aoff_adr. f_equal.
  rewrite to_Z_lsr12, to_Z_lsr3, to_Z_land4095.
  pose proof (i63_range off) as Hoff.
  pose proof (Z.mod_pos_bound (to_Z off) 8 ltac:(lia)) as Hb.
  rewrite Nat2Z.inj_add, Z2Nat.id by lia.
  pose proof (off_decomp (to_Z off) ltac:(lia)). lia.
Qed.

Lemma dv_tag0 w : dv rho (FV 0 w) = wbv w.
Proof. apply fk_dv_conc. exact Hrho0. Qed.

Lemma dv_tag0' (c : fval) : (vtag c =? 0)%uint63 = true -> dv rho c = wbv (vw c).
Proof.
  intros H. apply Uint63.eqb_spec in H. destruct c as [t w]. cbn [vtag vw] in *. subst t.
  apply dv_tag0.
Qed.

Lemma wbytes8_wbv w : wbytes8 (wbv w) = w_bytes w.
Proof. unfold wbytes8, w_bytes. rewrite wbv_unsigned. reflexivity. Qed.

Lemma length_wbytes8 w : length (wbytes8 w) = 8%nat.
Proof. apply length_Z_to_le_bytes. Qed.

(* [comment removed for export] *)
Lemma load_result_sub sz sgn (w : w64) (bi : int) :
  sz <> SZ8 ->
  to_Z bi + Z.of_nat (msz_nat sz) <= 8 ->
  load_result sz sgn
    (firstn (msz_nat sz) (skipn (Z.to_nat (to_Z bi)) (w_bytes w)))
  = wbv (ext_load sz sgn (w_extract bi (msz_int sz) w)).
Proof.
  intros Hsz Hb.
  assert (Hs : 1 <= to_Z (msz_int sz)) by (destruct sz; cbn; lia).
  assert (His : to_Z bi + to_Z (msz_int sz) <= 8) by (rewrite to_Z_msz; exact Hb).
  pose proof (w_load_bytes bi (msz_int sz) w Hs His) as HL.
  pose proof (wZ_w_extract_lt bi (msz_int sz) w Hs His) as Hlt.
  replace (Z.to_nat (to_Z (msz_int sz))) with (msz_nat sz) in HL
    by (rewrite to_Z_msz; lia).
  unfold load_result. rewrite HL.
  destruct sz; try congruence; destruct sgn; cbn [ext_load msz_int] in *.
  - symmetry. apply wbv_w_sext8.
  - rewrite <- wbv_w_zext8. apply wbv_w_zext8_small. exact (proj2 Hlt).
  - symmetry. apply wbv_w_sext16.
  - rewrite <- wbv_w_zext16. apply wbv_w_zext16_small. exact (proj2 Hlt).
  - symmetry. apply wbv_w_sext32.
  - rewrite <- wbv_w_zext32. apply wbv_w_zext32_small. exact (proj2 Hlt).
Qed.

Lemma load_result_8 (w : word) : load_result SZ8 false (wbytes8 w) = w.
Proof.
  unfold load_result, wbytes8.
  pose proof (bv_unsigned_in_range _ w) as Hr.
  rewrite (load_value_of_bytes 64 8) by (try reflexivity; lia).
  apply Z_to_bv_bv_unsigned.
Qed.


Lemma region_plain M m t rg : mem_ok segs IM rho M m -> iget t M = Some rg -> to_Z t < 2 ^ 60.
Proof. intros [Hmem _] Hg. exact (proj1 (proj1 (Hmem t rg Hg))). Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition slot_val (s : slot) (ob : option byte) : Prop :=
  match s with
  | SK b => ob = Some (Z_to_bv 8 (to_Z b))
  | SV v j => ob = nth_error (wbytes8 (dv rho v)) (Z.to_nat (to_Z j))
  | SU => True
  end.

Lemma slot_ok_val m a s : slot_ok segs rho m a s <-> slot_val s (rview segs m a).
Proof. destruct s; reflexivity. Qed.

(* [comment removed for export] *)
Definition slots_val (s : slots) (g : nat -> option byte) : Prop :=
  slot_val (sl0 s) (g 0%nat) /\ slot_val (sl1 s) (g 1%nat) /\ slot_val (sl2 s) (g 2%nat)
  /\ slot_val (sl3 s) (g 3%nat) /\ slot_val (sl4 s) (g 4%nat) /\ slot_val (sl5 s) (g 5%nat)
  /\ slot_val (sl6 s) (g 6%nat) /\ slot_val (sl7 s) (g 7%nat).

Lemma int_cases8 (j : int) :
  0 <= to_Z j < 8 ->
  j = 0%uint63 \/ j = 1%uint63 \/ j = 2%uint63 \/ j = 3%uint63 \/ j = 4%uint63 \/ j = 5%uint63
  \/ j = 6%uint63 \/ j = 7%uint63.
Proof.
  intros H.
  assert (to_Z j = 0 \/ to_Z j = 1 \/ to_Z j = 2 \/ to_Z j = 3 \/ to_Z j = 4 \/ to_Z j = 5
          \/ to_Z j = 6 \/ to_Z j = 7) as Hc by lia.
  repeat destruct Hc as [Hc|Hc]; [left | right; left | do 2 right; left | do 3 right; left
    | do 4 right; left | do 5 right; left | do 6 right; left | do 7 right]; apply to_Z_inj; exact Hc.
Qed.

Lemma slots_val_sget s g (j : int) :
  slots_val s g -> 0 <= to_Z j < 8 -> slot_val (sget j s) (g (Z.to_nat (to_Z j))).
Proof.
  intros (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7) Hj.
  destruct (int_cases8 j Hj) as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; assumption.
Qed.

Lemma slots_val_intro s g :
  (forall j : int, 0 <= to_Z j < 8 -> slot_val (sget j s) (g (Z.to_nat (to_Z j)))) -> slots_val s g.
Proof.
  intros H. unfold slots_val.
  pose proof (H 0%uint63 ltac:(cbn; lia)). pose proof (H 1%uint63 ltac:(cbn; lia)).
  pose proof (H 2%uint63 ltac:(cbn; lia)). pose proof (H 3%uint63 ltac:(cbn; lia)).
  pose proof (H 4%uint63 ltac:(cbn; lia)). pose proof (H 5%uint63 ltac:(cbn; lia)).
  pose proof (H 6%uint63 ltac:(cbn; lia)). pose proof (H 7%uint63 ltac:(cbn; lia)).
  repeat split; assumption.
Qed.

Lemma slots_val_ext s g g' :
  (forall j, (j < 8)%nat -> g' j = g j) -> slots_val s g -> slots_val s g'.
Proof.
  intros E (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7). unfold slots_val.
  rewrite !E by lia. repeat split; assumption.
Qed.

(* [comment removed for export] *)
Lemma fv_eqb_dv a b : fv_eqb a b = true -> dv rho a = dv rho b.
Proof.
  unfold fv_eqb. intros H. apply andb_true_iff in H as [Ht Hw].
  apply Uint63.eqb_spec in Ht. apply w_eqb_true_bv in Hw. unfold dv. rewrite Ht, Hw. reflexivity.
Qed.

Lemma byte_land255 (b : int) : Z_to_bv 8 (to_Z (b land 255)%uint63) = Z_to_bv 8 (to_Z b).
Proof.
  rewrite (i63_land_ones b 255%uint63 8) by (try reflexivity; lia).
  change (2 ^ 8) with 256. apply Z_to_bv8_mod.
Qed.

Lemma land255_lt (b : int) : to_Z (b land 255)%uint63 < 256.
Proof.
  rewrite (i63_land_ones b 255%uint63 8) by (try reflexivity; lia).
  change (2 ^ 8) with 256. apply Z.mod_pos_bound. lia.
Qed.

(* [comment removed for export] *)
Lemma slots_of_val_sound c g :
  (forall j, (j < 8)%nat -> g j = nth_error (wbytes8 (dv rho c)) j) -> slots_val (slots_of_val c) g.
Proof.
  intros Hg. destruct c as [t w]. unfold slots_of_val.
  destruct (t =? 0)%uint63 eqn:Et.
  - apply Uint63.eqb_spec in Et. subst t. unfold slots_val. cbn [sl0 sl1 sl2 sl3 sl4 sl5 sl6 sl7 slot_val].
    rewrite !Hg by lia. rewrite dv_tag0, wbytes8_wbv, w_bytes_eq. cbn [nth_error].
    repeat split; reflexivity.
  - unfold slots_val. cbn [sl0 sl1 sl2 sl3 sl4 sl5 sl6 sl7 slot_val].
    rewrite !Hg by lia. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
Definition cell_view (m : word -> option byte) (t pn ci : int) : nat -> option byte :=
  fun j => rview segs m (adr rho t (to_Z pn * 4096 + to_Z ci * 8 + Z.of_nat j)).

(* [comment removed for export] *)
Lemma slots_at_sound m t pn B p ci :
  page_ok segs IM rho m t pn B p -> 0 <= to_Z ci < B / 8 ->
  slots_val (slots_at IM p pn ci) (cell_view m t pn ci).
Proof.
  intros (_ & Hcells & Hslots & _) Hci. unfold slots_at.
  assert (Hdef : slots_val (match cell_at IM p pn ci with Some c => slots_of_val c | None => slots_unk end)
                   (cell_view m t pn ci)).
  { destruct (cell_at IM p pn ci) as [c|] eqn:Hc.
    - apply slots_of_val_sound. intros j Hj. exact (Hcells ci c Hci Hc j Hj).
    - unfold slots_val, slots_unk. cbn. tauto. }
  destruct (iget ci (pg_cells p)) as [[v| |sl]|] eqn:Hi; try exact Hdef.
  apply slots_val_intro. intros j Hj. apply slot_ok_val. unfold cell_view.
  rewrite Z2Nat.id by lia.
  assert (Hb : to_Z ci * 8 + to_Z j < B) by (Z.div_mod_to_equations; lia).
  exact (proj1 (Hslots ci sl ltac:(lia) ltac:(lia) Hi j Hj) Hb).
Qed.

(* [comment removed for export] *)
Lemma slots_at_sound_cut m t pn B p ci :
  page_ok segs IM rho m t pn B p -> 0 <= to_Z ci -> to_Z ci * 8 < B < to_Z ci * 8 + 8 ->
  slots_val (slots_at IM p pn ci) (cell_view m t pn ci).
Proof.
  intros (_ & Hcells & Hslots & Hcut) Hci Hb. unfold slots_at.
  rewrite (Hcut ci Hci Hb).
  destruct (iget ci (pg_cells p)) as [[v| |sl]|] eqn:Hi; try (unfold slots_val, slots_unk; cbn; tauto).
  apply slots_val_intro. intros j Hj.
  destruct (Hslots ci sl Hci ltac:(lia) Hi j Hj) as [Hin Hout].
  destruct (Z_lt_le_dec (to_Z ci * 8 + to_Z j) B) as [Hlt|Hge].
  - apply slot_ok_val. unfold cell_view. rewrite Z2Nat.id by lia. exact (Hin Hlt).
  - rewrite (Hout Hge). exact I.
Qed.

(* [comment removed for export] *)
Lemma slots_at_sound_any m t pn B p ci :
  page_ok segs IM rho m t pn B p -> 0 <= to_Z ci ->
  (to_Z ci < B / 8 \/ to_Z ci * 8 < B < to_Z ci * 8 + 8) ->
  slots_val (slots_at IM p pn ci) (cell_view m t pn ci).
Proof.
  intros Hp Hci [H|H]; [apply (slots_at_sound m t pn B p ci Hp); lia | exact (slots_at_sound_cut m t pn B p ci Hp Hci H)].
Qed.

(* [comment removed for export] *)
Lemma store_slot_field (bi n : int) v (jl : int) old ob ob' :
  to_Z jl < 8 -> to_Z bi + to_Z n <= 8 ->
  slot_val old ob ->
  (to_Z bi <= to_Z jl < to_Z bi + to_Z n ->
     ob' = nth_error (wbytes8 (dv rho v)) (Z.to_nat (to_Z jl - to_Z bi))) ->
  (~ (to_Z bi <= to_Z jl < to_Z bi + to_Z n) -> ob' = ob) ->
  slot_val (if ((bi <=? jl) && (jl <? bi + n))%uint63 then vslot v (jl - bi)%uint63 else old) ob'.
Proof.
  intros Hjl Hbn Hold Hin Hout.
  pose proof (i63_range bi) as Hb0. pose proof (i63_range n) as Hn0. pose proof (i63_range jl) as Hj0.
  assert (Hadd : to_Z (bi + n)%uint63 = to_Z bi + to_Z n).
  { rewrite add_spec, i63_wB. apply Z.mod_small. lia. }
  destruct (lebP bi jl) as [H1|H1]; cbn [andb].
  - destruct (ltbP jl (bi + n)%uint63) as [H2|H2]; rewrite Hadd in H2.
    + assert (Hsub : to_Z (jl - bi)%uint63 = to_Z jl - to_Z bi) by (apply i63_sub_small; lia).
      specialize (Hin (conj H1 H2)). destruct v as [tv wv]. unfold vslot.
      destruct (tv =? 0)%uint63 eqn:Et.
      * apply Uint63.eqb_spec in Et. subst tv. cbn [slot_val].
        rewrite Hin, dv_tag0, wbytes8_wbv, <- Hsub.
        apply w_bytes_nth_byte. lia.
      * cbn [slot_val]. rewrite Hsub. exact Hin.
    + rewrite (Hout ltac:(lia)). exact Hold.
  - rewrite (Hout ltac:(lia)). exact Hold.
Qed.

Lemma store_slots_sound (bi n : int) v s g g' :
  to_Z bi + to_Z n <= 8 ->
  slots_val s g ->
  (forall j : nat, (j < 8)%nat -> to_Z bi <= Z.of_nat j < to_Z bi + to_Z n ->
     g' j = nth_error (wbytes8 (dv rho v)) (Z.to_nat (Z.of_nat j - to_Z bi))) ->
  (forall j : nat, (j < 8)%nat -> ~ (to_Z bi <= Z.of_nat j < to_Z bi + to_Z n) -> g' j = g j) ->
  slots_val (store_slots bi n v s) g'.
Proof.
  intros Hbn (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7) Hin Hout.
  unfold store_slots, slots_val. cbn [sl0 sl1 sl2 sl3 sl4 sl5 sl6 sl7].
  repeat split.
  - apply (store_slot_field bi n v 0%uint63 _ (g 0%nat)); [cbn; lia | exact Hbn | exact H0 | apply (Hin 0%nat); lia | apply (Hout 0%nat); lia].
  - apply (store_slot_field bi n v 1%uint63 _ (g 1%nat)); [cbn; lia | exact Hbn | exact H1 | apply (Hin 1%nat); lia | apply (Hout 1%nat); lia].
  - apply (store_slot_field bi n v 2%uint63 _ (g 2%nat)); [cbn; lia | exact Hbn | exact H2 | apply (Hin 2%nat); lia | apply (Hout 2%nat); lia].
  - apply (store_slot_field bi n v 3%uint63 _ (g 3%nat)); [cbn; lia | exact Hbn | exact H3 | apply (Hin 3%nat); lia | apply (Hout 3%nat); lia].
  - apply (store_slot_field bi n v 4%uint63 _ (g 4%nat)); [cbn; lia | exact Hbn | exact H4 | apply (Hin 4%nat); lia | apply (Hout 4%nat); lia].
  - apply (store_slot_field bi n v 5%uint63 _ (g 5%nat)); [cbn; lia | exact Hbn | exact H5 | apply (Hin 5%nat); lia | apply (Hout 5%nat); lia].
  - apply (store_slot_field bi n v 6%uint63 _ (g 6%nat)); [cbn; lia | exact Hbn | exact H6 | apply (Hin 6%nat); lia | apply (Hout 6%nat); lia].
  - apply (store_slot_field bi n v 7%uint63 _ (g 7%nat)); [cbn; lia | exact Hbn | exact H7 | apply (Hin 7%nat); lia | apply (Hout 7%nat); lia].
Qed.


(* [comment removed for export] *)
Definition cell_val (c : cell) (g : nat -> option byte) : Prop :=
  match c with
  | CV u => forall j, (j < 8)%nat -> g j = nth_error (wbytes8 (dv rho u)) j
  | CB s => slots_val s g
  | CU => True
  end.

Lemma norm_slots_shape s :
  norm_slots s = CB s
  \/ (exists b0 b1 b2 b3 b4 b5 b6 b7,
        s = SL (SK b0) (SK b1) (SK b2) (SK b3) (SK b4) (SK b5) (SK b6) (SK b7))
  \/ (exists v0 j0 v1 j1 v2 j2 v3 j3 v4 j4 v5 j5 v6 j6 v7 j7,
        s = SL (SV v0 j0) (SV v1 j1) (SV v2 j2) (SV v3 j3) (SV v4 j4) (SV v5 j5) (SV v6 j6) (SV v7 j7)).
Proof.
  destruct s as [s0 s1 s2 s3 s4 s5 s6 s7].
  destruct s0 as [b0|v0 j0|]; [| |left; reflexivity].
  - destruct s1 as [b1| |]; [|left; reflexivity ..].
    destruct s2 as [b2| |]; [|left; reflexivity ..].
    destruct s3 as [b3| |]; [|left; reflexivity ..].
    destruct s4 as [b4| |]; [|left; reflexivity ..].
    destruct s5 as [b5| |]; [|left; reflexivity ..].
    destruct s6 as [b6| |]; [|left; reflexivity ..].
    destruct s7 as [b7| |]; [|left; reflexivity ..].
    right. left. exists b0, b1, b2, b3, b4, b5, b6, b7. reflexivity.
  - destruct s1 as [|v1 j1|]; [left; reflexivity| |left; reflexivity].
    destruct s2 as [|v2 j2|]; [left; reflexivity| |left; reflexivity].
    destruct s3 as [|v3 j3|]; [left; reflexivity| |left; reflexivity].
    destruct s4 as [|v4 j4|]; [left; reflexivity| |left; reflexivity].
    destruct s5 as [|v5 j5|]; [left; reflexivity| |left; reflexivity].
    destruct s6 as [|v6 j6|]; [left; reflexivity| |left; reflexivity].
    destruct s7 as [|v7 j7|]; [left; reflexivity| |left; reflexivity].
    right. right. exists v0, j0, v1, j1, v2, j2, v3, j3, v4, j4, v5, j5, v6, j6, v7, j7. reflexivity.
Qed.

Lemma eqb_lit_nat (j c : int) : (j =? c)%uint63 = true -> Z.to_nat (to_Z j) = Z.to_nat (to_Z c).
Proof. intros H. apply Uint63.eqb_spec in H. subst. reflexivity. Qed.

Lemma norm_slots_sound s g : slots_val s g -> cell_val (norm_slots s) g.
Proof.
  intros Hs. destruct (norm_slots_shape s) as [E | [(b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & ->) |
    (v0 & j0 & v1 & j1 & v2 & j2 & v3 & j3 & v4 & j4 & v5 & j5 & v6 & j6 & v7 & j7 & ->)]].
  - rewrite E. exact Hs.
  - (* [comment removed for export] *)
    destruct Hs as (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7). cbn [sl0 sl1 sl2 sl3 sl4 sl5 sl6 sl7 slot_val] in *.
    cbn [norm_slots cell_val]. intros j Hj. rewrite dv_tag0, wbytes8_wbv.
    rewrite w_bytes_w_of_bytes8 by apply land255_lt. rewrite !byte_land255.
    destruct j as [|[|[|[|[|[|[|[|j]]]]]]]]; cbn [nth_error]; try assumption. lia.
  - pose proof Hs as Hs0.
    destruct Hs as (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7). cbn [sl0 sl1 sl2 sl3 sl4 sl5 sl6 sl7 slot_val] in H0, H1, H2, H3, H4, H5, H6, H7.
    cbn [norm_slots].
    match goal with |- cell_val (if ?c then _ else _) _ => destruct c eqn:C1 end;
      [|exact Hs0].
    repeat match type of C1 with (_ && _ = true) =>
      let H := fresh "Hc" in apply andb_true_iff in C1 as [C1 H] end.
    apply eqb_lit_nat in C1, Hc7, Hc6, Hc5. rewrite C1 in H0. rewrite Hc7 in H1. rewrite Hc6 in H2. rewrite Hc5 in H3.
    apply fv_eqb_dv in Hc4, Hc3, Hc2, Hc1, Hc0, Hc.
    rewrite <- Hc4 in H1. rewrite <- Hc3 in H2. rewrite <- Hc2 in H3.
    rewrite <- Hc1 in H5. rewrite <- Hc0 in H6. rewrite <- Hc in H7.
    match goal with |- cell_val (if ?c then _ else _) _ => destruct c eqn:C2 end.
    + (* [comment removed for export] *)
      repeat match type of C2 with (_ && _ = true) =>
        let H := fresh "Hd" in apply andb_true_iff in C2 as [C2 H] end.
      apply eqb_lit_nat in C2, Hd2, Hd1, Hd0. apply fv_eqb_dv in Hd.
      rewrite C2 in H4. rewrite Hd2 in H5. rewrite Hd1 in H6. rewrite Hd0 in H7.
      rewrite <- Hd in H4, H5, H6, H7.
      cbn [cell_val]. intros j Hj.
      destruct j as [|[|[|[|[|[|[|[|j]]]]]]]]; try assumption. lia.
    + match goal with |- cell_val (if ?c then _ else _) _ => destruct c eqn:C3 end;
        [|exact Hs0].
      (* [comment removed for export] *)
      repeat match type of C3 with (_ && _ = true) =>
        let H := fresh "He" in apply andb_true_iff in C3 as [C3 H] end.
      apply eqb_lit_nat in C3, He5, He4, He3.
      rewrite C3 in H4. rewrite He5 in H5. rewrite He4 in H6. rewrite He3 in H7.
      apply Uint63.eqb_spec in He2, He1, He0. apply w_eqb_true_bv in He.
      destruct v0 as [ta wa], v4 as [tb wb]. cbn [vtag vw] in *.
      destruct (fk_vkind_cases ta) as [[_ K]|[[_ K]|[[Ba _]|[[_ K]|[[_ K]|[[_ K]|[[_ K]|[_ K]]]]]]]];
        try (rewrite K in He2; discriminate).
      destruct (fk_vkind_cases tb) as [[_ K]|[[_ K]|[[_ K]|[[Bb _]|[[_ K]|[[_ K]|[[_ K]|[_ K]]]]]]]];
        try (rewrite K in He1; discriminate).
      pose proof (fk_vbase_lt ta ltac:(lia)) as Hbl.
      set (x := bv_add (rho (vbase ta)) (wbv wa)).
      assert (Ea : dv rho (FV ta wa) = sx32 x).
      { unfold dv. cbn [vtag vw]. rewrite He2. reflexivity. }
      assert (Eb : dv rho (FV tb wb) = hi32 x).
      { unfold dv. cbn [vtag vw]. rewrite He1, <- He0, <- He. reflexivity. }
      assert (Eu : dv rho (FV (vbase ta) wa) = x).
      { rewrite fk_dv_plain by exact Hbl. reflexivity. }
      rewrite Ea in H0, H1, H2, H3. rewrite Eb in H4, H5, H6, H7.
      cbn [cell_val]. intros j Hj. rewrite Eu.
      destruct j as [|[|[|[|[|[|[|[|j]]]]]]]]; try lia.
      * rewrite H0. apply (fk_bytes_sx32 x 0). lia.
      * rewrite H1. apply (fk_bytes_sx32 x 1). lia.
      * rewrite H2. apply (fk_bytes_sx32 x 2). lia.
      * rewrite H3. apply (fk_bytes_sx32 x 3). lia.
      * rewrite H4. apply (fk_bytes_hi32 x 0). lia.
      * rewrite H5. apply (fk_bytes_hi32 x 1). lia.
      * rewrite H6. apply (fk_bytes_hi32 x 2). lia.
      * rewrite H7. apply (fk_bytes_hi32 x 3). lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bv_extract_0_64 (x : word) : bv_extract 0 64 x = x.
Proof.
  apply bv_eq. rewrite bv_extract_unsigned, Z.shiftr_0_r. apply bv_wrap_small.
  apply bv_unsigned_in_range.
Qed.

(* [comment removed for export] *)
Lemma load_result_any sz sgn (w : w64) (bi : int) :
  to_Z bi + Z.of_nat (msz_nat sz) <= 8 ->
  load_result sz sgn (firstn (msz_nat sz) (skipn (Z.to_nat (to_Z bi)) (w_bytes w)))
  = wbv (ext_load sz sgn (w_extract bi (msz_int sz) w)).
Proof.
  intros Hb. destruct (msize_eq_dec sz SZ8) as [->|Hne]; [|apply load_result_sub; assumption].
  cbn [msz_nat msz_int ext_load] in *.
  pose proof (w_load_bytes bi 8%uint63 w ltac:(cbn; lia) ltac:(change (to_Z 8) with 8; lia)) as HL.
  change (Z.to_nat (to_Z 8)) with 8%nat in HL.
  unfold load_result. rewrite HL. apply bv_extract_0_64.
Qed.

Lemma skb_lt x : to_Z (skb x) < 256.
Proof. destruct x; cbn [skb]; try (cbn; lia). apply land255_lt. Qed.

(* [comment removed for export] *)
Lemma all_sk_field (bi n jl : int) (x : slot) ob :
  to_Z bi + to_Z n <= 8 -> to_Z jl < 8 ->
  ((jl <? bi) || (bi + n <=? jl) || is_sk x)%uint63 = true ->
  slot_val x ob ->
  to_Z bi <= to_Z jl < to_Z bi + to_Z n ->
  ob = Some (Z_to_bv 8 (to_Z (skb x))).
Proof.
  intros Hbn Hjl H Hx Hin.
  pose proof (i63_range bi) as Hb0. pose proof (i63_range n) as Hn0.
  assert (Hadd : to_Z (bi + n)%uint63 = to_Z bi + to_Z n).
  { rewrite add_spec, i63_wB. apply Z.mod_small. lia. }
  apply orb_true_iff in H as [H|H]; [apply orb_true_iff in H as [H|H]|].
  - apply ltb_spec in H. lia.
  - apply leb_spec in H. rewrite Hadd in H. lia.
  - destruct x; try discriminate. cbn [slot_val skb] in *. rewrite byte_land255. exact Hx.
Qed.

Lemma all_sk_sound (bi n : int) s g :
  to_Z bi + to_Z n <= 8 -> slots_val s g -> all_sk bi n s = true ->
  forall j : nat, (j < 8)%nat -> to_Z bi <= Z.of_nat j < to_Z bi + to_Z n ->
    g j = nth_error (w_bytes (w_of_sk s)) j.
Proof.
  intros Hbn (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7) Hall j Hj Hin.
  unfold all_sk in Hall. cbv zeta in Hall.
  repeat match type of Hall with (_ && _ = true) =>
    let H := fresh "Ha" in apply andb_true_iff in Hall as [Hall H] end.
  unfold w_of_sk. rewrite w_bytes_w_of_bytes8 by apply skb_lt.
  destruct j as [|[|[|[|[|[|[|[|j]]]]]]]]; cbn [nth_error]; try lia.
  - apply (all_sk_field bi n 0%uint63 _ _ Hbn ltac:(cbn; lia) Hall H0). exact Hin.
  - apply (all_sk_field bi n 1%uint63 _ _ Hbn ltac:(cbn; lia) Ha5 H1). exact Hin.
  - apply (all_sk_field bi n 2%uint63 _ _ Hbn ltac:(cbn; lia) Ha4 H2). exact Hin.
  - apply (all_sk_field bi n 3%uint63 _ _ Hbn ltac:(cbn; lia) Ha3 H3). exact Hin.
  - apply (all_sk_field bi n 4%uint63 _ _ Hbn ltac:(cbn; lia) Ha2 H4). exact Hin.
  - apply (all_sk_field bi n 5%uint63 _ _ Hbn ltac:(cbn; lia) Ha1 H5). exact Hin.
  - apply (all_sk_field bi n 6%uint63 _ _ Hbn ltac:(cbn; lia) Ha0 H6). exact Hin.
  - apply (all_sk_field bi n 7%uint63 _ _ Hbn ltac:(cbn; lia) Ha H7). exact Hin.
Qed.

Lemma vkind0_plain t : (vkind t =? 0)%uint63 = true -> to_Z t < 2 ^ 60.
Proof.
  intros H. apply Uint63.eqb_spec in H.
  destruct (fk_vkind_cases t) as [[B _]|[[_ K]|[[_ K]|[[_ K]|[[_ K]|[[_ K]|[[_ K]|[_ K]]]]]]]];
    [exact B | rewrite K in H; discriminate ..].
Qed.

(* [comment removed for export] *)
Lemma load_lo_sound v0 v : load_lo v0 = Some v -> dv rho v = sx32 (dv rho v0).
Proof.
  destruct v0 as [t w]. unfold load_lo. cbv zeta.
  destruct (vkind t =? 0)%uint63 eqn:K0.
  { pose proof (vkind0_plain t K0) as Hpl.
    destruct (t =? 0)%uint63 eqn:Et; intros H; inversion H; subst v; clear H.
    - apply Uint63.eqb_spec in Et. subst t. rewrite !dv_tag0. apply wbv_w_sext32.
    - rewrite fk_dv_ktag by (try exact Hpl; cbn; lia). rewrite fk_dvk_LO.
      rewrite (fk_dv_plain rho (FV t w)) by exact Hpl. reflexivity. }
  destruct (vkind t =? 1)%uint63 eqn:K1.
  { intros H; inversion H; subst v; clear H. apply Uint63.eqb_spec in K1.
    assert (Hb : to_Z (vbase t) < 2 ^ 60).
    { apply fk_vbase_lt. destruct (fk_vkind_cases t) as [[B _]|[[B _]|[[_ K]|[[_ K]|[[_ K]|[[_ K]|[[_ K]|[_ K]]]]]]]];
        try lia; rewrite K in K1; discriminate. }
    rewrite fk_dv_ktag by (try exact Hb; cbn; lia). rewrite fk_dvk_NLO.
    unfold dv. cbn [vtag vw]. rewrite K1. reflexivity. }
  destruct ((vkind t =? 2) || (vkind t =? 3) || (vkind t =? 4))%uint63 eqn:K234; [|discriminate].
  intros H; inversion H; subst v; clear H.
  apply orb_true_iff in K234 as [K|K]; [apply orb_true_iff in K as [K|K]|];
    apply Uint63.eqb_spec in K; unfold dv; cbn [vtag vw]; rewrite K.
  - change (dvk 2 ?x ?y) with (sx32 (bv_add x y)). symmetry. apply fk_sx32_sx32.
  - change (dvk 3 ?x ?y) with (hi32 (bv_add x y)). symmetry. apply fk_sx32_hi32.
  - change (dvk 4 ?x ?y) with (sx32 (bv_add (bv_opp x) y)). symmetry. apply fk_sx32_sx32.
Qed.

(* [comment removed for export] *)
Lemma load_hi_sound v0 v : load_hi v0 = Some v -> dv rho v = hi32 (dv rho v0).
Proof.
  destruct v0 as [t w]. unfold load_hi.
  destruct (vkind t =? 0)%uint63 eqn:K0; cbn [andb]; [|discriminate].
  destruct (negb (t =? 0)%uint63); [|discriminate].
  intros H; inversion H; subst v; clear H.
  pose proof (vkind0_plain t K0) as Hpl.
  rewrite fk_dv_ktag by (try exact Hpl; cbn; lia). rewrite fk_dvk_HI.
  rewrite (fk_dv_plain rho (FV t w)) by exact Hpl. reflexivity.
Qed.

Lemma slots_val_sget_add s g (bi k : int) :
  slots_val s g -> to_Z bi + to_Z k < 8 ->
  slot_val (sget (bi + k)%uint63 s) (g (Z.to_nat (to_Z bi) + Z.to_nat (to_Z k))%nat).
Proof.
  intros Hs Hlt. pose proof (i63_range bi) as Hb0. pose proof (i63_range k) as Hk0.
  assert (Hadd : to_Z (bi + k)%uint63 = to_Z bi + to_Z k).
  { rewrite add_spec, i63_wB. apply Z.mod_small. lia. }
  pose proof (slots_val_sget s g (bi + k)%uint63 Hs ltac:(lia)) as H.
  rewrite Hadd, Z2Nat.inj_add in H by lia. exact H.
Qed.

Lemma nth_error_firstn_lt {A} (l : list A) n j : (j < n)%nat -> nth_error (firstn n l) j = nth_error l j.
Proof.
  intros H. rewrite nth_error_firstn. destruct (Nat.ltb_spec j n); [reflexivity | lia].
Qed.

(* [comment removed for export] *)
Lemma load_all_sk_sound sz sgn (bi : int) s g :
  to_Z bi + Z.of_nat (msz_nat sz) <= 8 ->
  slots_val s g ->
  all_sk bi (msz_int sz) s = true ->
  exists bs, length bs = msz_nat sz
    /\ (forall j, (j < msz_nat sz)%nat -> g (Z.to_nat (to_Z bi) + j)%nat = nth_error bs j)
    /\ load_result sz sgn bs = dv rho (FV 0 (ext_load sz sgn (w_extract bi (msz_int sz) (w_of_sk s)))).
Proof.
  intros Hb Hs Hall. pose proof (i63_range bi) as Hb0. pose proof (msz_nat_pos sz) as Hn.
  exists (firstn (msz_nat sz) (skipn (Z.to_nat (to_Z bi)) (w_bytes (w_of_sk s)))).
  split; [|split].
  - rewrite firstn_length_le; [reflexivity|].
    rewrite length_skipn. unfold w_bytes. rewrite length_Z_to_le_bytes. lia.
  - intros j Hj. rewrite nth_error_firstn_lt by exact Hj. rewrite nth_error_skipn.
    apply (all_sk_sound bi (msz_int sz) s g); [rewrite to_Z_msz; exact Hb | exact Hs | exact Hall | lia |].
    rewrite to_Z_msz. lia.
  - rewrite dv_tag0. apply load_result_any. exact Hb.
Qed.

Theorem load_slots_sound sz sgn (bi : int) s g v :
  to_Z bi + Z.of_nat (msz_nat sz) <= 8 ->
  slots_val s g ->
  load_slots sz sgn bi s = Some v ->
  exists bs, length bs = msz_nat sz
    /\ (forall j, (j < msz_nat sz)%nat -> g (Z.to_nat (to_Z bi) + j)%nat = nth_error bs j)
    /\ load_result sz sgn bs = dv rho v.
Proof.
  intros Hb Hs Hl. pose proof (i63_range bi) as Hb0. pose proof (msz_nat_pos sz) as Hn.
  unfold load_slots in Hl. cbv zeta in Hl.
  destruct (all_sk bi (msz_int sz) s) eqn:Hall.
  { inversion Hl; subst v; clear Hl. apply load_all_sk_sound; assumption. }
  destruct sz; try discriminate. destruct sgn; try discriminate. cbn [msz_nat] in *.
  pose proof (slots_val_sget s g bi Hs ltac:(lia)) as G0.
  pose proof (slots_val_sget_add s g bi 1%uint63 Hs ltac:(change (to_Z 1) with 1; lia)) as G1.
  pose proof (slots_val_sget_add s g bi 2%uint63 Hs ltac:(change (to_Z 2) with 2; lia)) as G2.
  pose proof (slots_val_sget_add s g bi 3%uint63 Hs ltac:(change (to_Z 3) with 3; lia)) as G3.
  change (Z.to_nat (to_Z 1)) with 1%nat in G1. change (Z.to_nat (to_Z 2)) with 2%nat in G2.
  change (Z.to_nat (to_Z 3)) with 3%nat in G3.
  destruct (sget bi s) as [|v0 j0|]; try discriminate.
  destruct (sget (bi + 1)%uint63 s) as [|v1 j1|]; try discriminate.
  destruct (sget (bi + 2)%uint63 s) as [|v2 j2|]; try discriminate.
  destruct (sget (bi + 3)%uint63 s) as [|v3 j3|]; try discriminate.
  cbn [slot_val] in G0, G1, G2, G3.
  destruct (fv_eqb v0 v1 && fv_eqb v0 v2 && fv_eqb v0 v3) eqn:Ev; [|discriminate].
  apply andb_true_iff in Ev as [Ev E3]. apply andb_true_iff in Ev as [E1 E2].
  apply fv_eqb_dv in E1, E2, E3. rewrite <- E1 in G1. rewrite <- E2 in G2. rewrite <- E3 in G3.
  set (x := dv rho v0) in *.
  destruct ((j0 =? 0) && (j1 =? 1) && (j2 =? 2) && (j3 =? 3))%uint63 eqn:J.
  { repeat match type of J with (_ && _ = true) =>
      let H := fresh "Hj" in apply andb_true_iff in J as [J H] end.
    apply eqb_lit_nat in J, Hj1, Hj0, Hj. rewrite J in G0. rewrite Hj1 in G1. rewrite Hj0 in G2. rewrite Hj in G3.
    change (Z.to_nat (to_Z 0)) with 0%nat in G0. change (Z.to_nat (to_Z 1)) with 1%nat in G1.
    change (Z.to_nat (to_Z 2)) with 2%nat in G2. change (Z.to_nat (to_Z 3)) with 3%nat in G3.
    exists (firstn 4 (wbytes8 x)). split; [|split].
    - rewrite firstn_length_le; [reflexivity | rewrite length_wbytes8; lia].
    - intros j Hj'. rewrite nth_error_firstn_lt by exact Hj'.
      destruct j as [|[|[|[|j]]]]; try lia.
      + rewrite Nat.add_0_r. exact G0.
      + exact G1.
      + exact G2.
      + exact G3.
    - unfold load_result. rewrite fk_load_lo. symmetry. apply load_lo_sound. exact Hl. }
  destruct ((j0 =? 4) && (j1 =? 5) && (j2 =? 6) && (j3 =? 7))%uint63 eqn:J'; [|discriminate].
  repeat match type of J' with (_ && _ = true) =>
    let H := fresh "Hj" in apply andb_true_iff in J' as [J' H] end.
  apply eqb_lit_nat in J', Hj1, Hj0, Hj. rewrite J' in G0. rewrite Hj1 in G1. rewrite Hj0 in G2. rewrite Hj in G3.
  change (Z.to_nat (to_Z 4)) with 4%nat in G0. change (Z.to_nat (to_Z 5)) with 5%nat in G1.
  change (Z.to_nat (to_Z 6)) with 6%nat in G2. change (Z.to_nat (to_Z 7)) with 7%nat in G3.
  exists (firstn 4 (skipn 4 (wbytes8 x))). split; [|split].
  - rewrite firstn_length_le; [reflexivity | rewrite length_skipn, length_wbytes8; lia].
  - intros j Hj'. rewrite nth_error_firstn_lt by exact Hj'. rewrite nth_error_skipn.
    destruct j as [|[|[|[|j]]]]; try lia.
    + rewrite Nat.add_0_r. exact G0.
    + exact G1.
    + exact G2.
    + exact G3.
  - unfold load_result. rewrite fk_load_hi. symmetry. apply load_hi_sound. exact Hl.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rgs_ok (M : itrie region) : Prop := forall t rg, iget t M = Some rg -> region_ok rho t rg.

Lemma mem_ok_rgs_ok M m : mem_ok segs IM rho M m -> rgs_ok M.
Proof. intros [Hmem _] t rg Hg. exact (proj1 (Hmem t rg Hg)). Qed.

Lemma to_Z_lsl3 (j : int) : to_Z j <= 7 -> to_Z (j << 3)%uint63 = 8 * to_Z j.
Proof.
  intros Hj. pose proof (i63_range j) as Hj0. rewrite lsl_spec, i63_wB. change (2 ^ to_Z 3) with 8.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma resolve_slot_sound M s ob :
  rgs_ok M -> slot_val s ob -> slot_val (resolve_slot M s) ob.
Proof.
  intros HM Hs. destruct s as [b|[t [top off]] j|]; try exact Hs.
  unfold resolve_slot.
  destruct ((t <? kind_lim) && (j <=? 7))%uint63 eqn:C0; [|exact Hs].
  destruct (iget t M) as [rg|] eqn:Hg; [|exact Hs].
  apply andb_true_iff in C0 as [Hc1 Hc0]. apply ltb_spec in Hc1. apply leb_spec in Hc0.
  change (to_Z kind_lim) with (2 ^ 60) in Hc1. change (to_Z 7) with 7 in Hc0.
  pose proof (i63_range j) as Hj0.
  destruct (((j + 1) << 3) <=? rg_align rg)%uint63 eqn:Cal.
  { (* [comment removed for export] *)
    apply leb_spec in Cal.
    assert (Ej1 : to_Z ((j + 1) << 3)%uint63 = 8 * (to_Z j + 1)).
    { rewrite lsl_spec, add_spec, i63_wB. change (to_Z 1) with 1. change (2 ^ to_Z 3) with 8.
      rewrite (Z.mod_small (to_Z j + 1)) by (clear - Hj0 Hc0; lia).
      rewrite Z.mod_small by (clear - Hj0 Hc0; lia). clear. lia. }
    rewrite Ej1 in Cal.
    destruct (HM _ _ Hg) as (_ & _ & _ & _ & Hal & _).
    cbn [slot_val] in *. rewrite Hs. rewrite fk_wbytes8_nth by (clear - Hj0 Hc0; lia). f_equal.
    rewrite <- (Z_to_bv8_mod (bv_unsigned _ / _)).
    rewrite (fk_dv_plain rho (FV t (W64 top off))) by exact Hc1. cbn [vtag vw].
    rewrite bv_add_unsigned, wbv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
    rewrite Z2Nat.id by (clear - Hj0; lia).
    rewrite (fk_low_byte_aligned _ _ (to_Z (rg_align rg)) (to_Z j) ltac:(clear - Hj0 Hc0; lia) Cal Hal).
    rewrite (to_Z_w_byte j (W64 top off) Hc0). reflexivity. }
  cbv zeta.
  match goal with |- slot_val (if ?c then _ else _) _ => destruct c eqn:C2 end; [|exact Hs].
  repeat match type of C2 with (_ && _ = true) =>
    let H' := fresh "Hd" in apply andb_true_iff in C2 as [C2 H'] end.
  apply Uint63.eqb_spec in C2. apply (f_equal to_Z) in C2. rewrite i63_land1 in C2. change (to_Z 0) with 0 in C2.
  apply ltb_spec in Hd2, Hd1. apply leb_spec in Hd0. apply Uint63.eqb_spec in Hd.
  change (to_Z off_bound) with (2 ^ 62) in Hd2, Hd1.
  pose proof (i63_range off) as Ho.
  pose proof (i63_range (rg_clo rg)) as Hcl. pose proof (i63_range (rg_chi rg)) as Hch.
  destruct (fk_ptr_unsigned rho t rg top off (HM _ _ Hg) C2 Hd2 Hd1) as [E [B1 B2]].
  cbn [slot_val] in *. rewrite Hs. rewrite fk_wbytes8_nth by (clear - Hj0 Hc0; lia). f_equal.
  rewrite byte_land255, lsr_spec, (to_Z_lsl3 j Hc0).
  rewrite (fk_dv_plain rho (FV t (W64 top off))) by exact Hc1. cbn [vtag vw]. rewrite E.
  rewrite Z2Nat.id by (clear - Hj0; lia).
  assert (Ea : to_Z (rg_clo rg + off)%uint63 = to_Z (rg_clo rg) + to_Z off).
  { rewrite add_spec, i63_wB. apply Z.mod_small. clear - Ho Hcl Hch Hd0 Hd1 Hd2. lia. }
  assert (Eb : to_Z (rg_chi rg + off)%uint63 = to_Z (rg_chi rg) + to_Z off).
  { rewrite add_spec, i63_wB. apply Z.mod_small. clear - Ho Hch Hd1 Hd2. lia. }
  apply (f_equal to_Z) in Hd. rewrite !lsr_spec, (to_Z_lsl3 j Hc0), Ea, Eb in Hd.
  rewrite Ea. f_equal.
  apply (fk_div_bounded _ (to_Z (rg_chi rg) + to_Z off));
    [apply Z.pow_pos_nonneg; clear - Hj0; lia | clear - B1 B2; lia | exact Hd].
Qed.

Lemma resolve_slots_sound M s g : rgs_ok M -> slots_val s g -> slots_val (resolve_slots M s) g.
Proof.
  intros HM (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7). unfold resolve_slots, slots_val.
  cbn [sl0 sl1 sl2 sl3 sl4 sl5 sl6 sl7]. repeat split; apply resolve_slot_sound; assumption.
Qed.

Theorem load_slots2_sound M sz sgn (bi : int) s g v :
  rgs_ok M ->
  to_Z bi + Z.of_nat (msz_nat sz) <= 8 ->
  slots_val s g ->
  load_slots2 M sz sgn bi s = Some v ->
  exists bs, length bs = msz_nat sz
    /\ (forall j, (j < msz_nat sz)%nat -> g (Z.to_nat (to_Z bi) + j)%nat = nth_error bs j)
    /\ load_result sz sgn bs = dv rho v.
Proof.
  intros HM Hb Hs Hl. unfold load_slots2 in Hl.
  destruct (load_slots sz sgn bi s) as [v'|] eqn:E1.
  { inversion Hl; subst v'. exact (load_slots_sound sz sgn bi s g v Hb Hs E1). }
  cbv zeta in Hl.
  destruct (all_sk bi (msz_int sz) (resolve_slots M s)) eqn:Hall.
  { inversion Hl; subst v. apply load_all_sk_sound; [exact Hb | | exact Hall].
    apply resolve_slots_sound; assumption. }
  destruct sz; try discriminate. destruct sgn; try discriminate. cbn [msz_nat] in *.
  pose proof (i63_range bi) as Hb0.
  pose proof (slots_val_sget s g bi Hs ltac:(lia)) as G0.
  destruct (sget bi s) as [|[t w] j|]; try discriminate.
  destruct ((j =? 5) && (t <? kind_lim) && b5_nonzero M t w)%uint63 eqn:C; [|discriminate].
  apply andb_true_iff in C as [C _]. apply andb_true_iff in C as [Cj Ct].
  apply eqb_lit_nat in Cj. apply ltb_spec in Ct.
  change (to_Z kind_lim) with (2 ^ 60) in Ct. change (Z.to_nat (to_Z 5)) with 5%nat in Cj.
  inversion Hl; subst v. cbn [slot_val] in G0. rewrite Cj in G0.
  set (x := dv rho (FV t w)) in *.
  exists (firstn 1 (skipn 5 (wbytes8 x))). split; [|split].
  - rewrite firstn_length_le; [reflexivity | rewrite length_skipn, length_wbytes8; lia].
  - intros j' Hj'. assert (j' = 0%nat) by lia. subst j'.
    rewrite nth_error_firstn_lt by lia. rewrite nth_error_skipn, Nat.add_0_r. exact G0.
  - unfold load_result. rewrite fk_load_b5.
    rewrite fk_dv_ktag by (try exact Ct; cbn; lia). rewrite fk_dvk_B5.
    unfold x. rewrite (fk_dv_plain rho (FV t w)) by exact Ct. reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma cell_view_access m t top off (j : nat) :
  to_Z t < 2 ^ 60 -> to_Z top mod 2 = 0 ->
  cell_view m t (off >> 12)%uint63 ((off land 4095) >> 3)%uint63 (Z.to_nat (to_Z off mod 8) + j)%nat
  = rview segs m (aoff (dv rho (FV t (W64 top off))) j).
Proof. intros Hpl Htop. unfold cell_view. rewrite (access_addr t top off j Hpl Htop). reflexivity. Qed.

Theorem fm_load_sound : forall M m a sz sgn v,
  mem_ok segs IM rho M m ->
  fm_load IM M a sz sgn = Some v ->
  exists bs, ov_read_bytes segs m (dv rho a) (msz_nat sz) = Some bs
             /\ load_result sz sgn bs = dv rho v.
Proof.
  intros M m [t [top off]] sz sgn v Hmok Hload. pose proof (mem_ok_rgs_ok M m Hmok) as HMok.
  destruct Hmok as [Hmem _]. unfold fm_load in Hload. cbv zeta in Hload.
  destruct (negb ((top land 1) =? 0)%uint63) eqn:C1; [discriminate|].
  destruct (negb ((off land 7) + msz_int sz <=? 8)%uint63) eqn:C2; [discriminate|].
  destruct (iget t M) as [rg|] eqn:Hrg; [|discriminate].
  destruct (negb (in_region rg off (msz_int sz))) eqn:C3; [discriminate|].
  destruct (page_at IM rg t (off >> 12)%uint63) as [p|] eqn:Hp; [|discriminate].
  destruct (checks_inv top off sz rg C1 C2 C3) as (Htop & Hcell & Hoff & Hlen & Hlo & Hin).
  pose proof (i63_range off) as Hoff0.
  pose proof (Z.mod_pos_bound (to_Z off) 8 ltac:(lia)) as Hb.
  pose proof (msz_nat_pos sz) as Hn.
  destruct (Hmem t rg Hrg) as [Hreg Hpages].
  pose proof (proj1 Hreg) as Hpl.
  assert (Hpn : to_Z (off >> 12)%uint63 < 2 ^ 50).
  { rewrite to_Z_lsr12. apply Z.div_lt_upper_bound; lia. }
  destruct (Hpages _ _ Hpn Hp) as (Hpage & _ & _).
  assert (Hcic : (0 <= to_Z ((off land 4095) >> 3)%uint63 < clim rg (off >> 12)%uint63)
                 \/ (to_Z ((off land 4095) >> 3)%uint63 * 8 < blim rg (off >> 12)%uint63 < to_Z ((off land 4095) >> 3)%uint63 * 8 + 8)).
  { rewrite to_Z_lsr3, to_Z_land4095.
    apply (ci_cases rg _ (to_Z off) (Z.of_nat (msz_nat sz))); [lia | lia | exact Hcell | exact Hin | apply to_Z_lsr12]. }
  assert (Hci0 : 0 <= to_Z ((off land 4095) >> 3)%uint63) by (rewrite to_Z_lsr3, to_Z_land4095; Z.div_mod_to_equations; lia).
  set (pn := (off >> 12)%uint63) in *. set (ci := ((off land 4095) >> 3)%uint63) in *.
  (* [comment removed for export] *)
  assert (Hslow : forall s, slots_val s (cell_view m t pn ci) ->
            load_slots2 M sz sgn (off land 7)%uint63 s = Some v ->
            exists bs, ov_read_bytes segs m (dv rho (FV t (W64 top off))) (msz_nat sz) = Some bs
                       /\ load_result sz sgn bs = dv rho v).
  { intros s Hs Hl.
    destruct (load_slots2_sound M sz sgn (off land 7)%uint63 s _ v HMok ltac:(rewrite to_Z_land7; exact Hcell) Hs Hl)
      as (bs & Hlenbs & Hnth & Hres).
    exists bs. split; [|exact Hres].
    apply ov_read_bytes_intro; [exact Hlenbs|].
    intros j Hj. rewrite <- (Hnth j Hj), to_Z_land7.
    symmetry. apply cell_view_access; assumption. }
  assert (Hsv : slots_val (slots_at IM p pn ci) (cell_view m t pn ci)).
  { apply (slots_at_sound_any m t pn _ p ci Hpage Hci0). unfold clim in Hcic. lia. }
  destruct (cell_at IM p pn ci) as [c|] eqn:Hc.
  2:{ destruct (iget ci (pg_cells p)) as [[u| |sl]|] eqn:Hi; try discriminate.
      apply (Hslow sl); [|exact Hload].
      unfold slots_at in Hsv. rewrite Hi in Hsv. exact Hsv. }
  (* [comment removed for export] *)
  assert (Hci : 0 <= to_Z ci < clim rg pn).
  { destruct Hcic as [H|H]; [exact H|]. exfalso.
    pose proof (proj2 (proj2 (proj2 Hpage)) ci Hci0 H) as Hnone. rewrite Hnone in Hc. discriminate. }
  pose proof (proj1 (proj2 Hpage) _ _ Hci Hc) as Hcells.
  set (bi := Z.to_nat (to_Z off mod 8)).
  assert (Hread : ov_read_bytes segs m (dv rho (FV t (W64 top off))) (msz_nat sz)
                  = Some (firstn (msz_nat sz) (skipn bi (wbytes8 (dv rho c))))).
  { apply ov_read_bytes_intro.
    + rewrite firstn_length_le; [reflexivity|].
      rewrite length_skipn, length_wbytes8. unfold bi. lia.
    + intros j Hj. rewrite <- (access_addr t top off j Hpl Htop). fold bi. fold pn. fold ci.
      rewrite Hcells by (unfold bi; lia).
      rewrite nth_error_firstn, nth_error_skipn.
      destruct (Nat.ltb_spec j (msz_nat sz)); [reflexivity | lia]. }
  destruct (msize_eq_dec sz SZ8) as [->|Hne].
  - inversion Hload; subst v. eexists; split; [exact Hread|].
    assert (bi = 0%nat) by (unfold bi; cbn [msz_nat] in Hcell; lia).
    rewrite H, skipn_O. cbn [msz_nat].
    rewrite firstn_all2 by (rewrite length_wbytes8; lia).
    unfold load_result. apply (load_result_8 (dv rho c)).
  - destruct (vtag c =? 0)%uint63 eqn:Htag.
    + assert (Hv : v = FV 0 (ext_load sz sgn (w_extract (off land 7) (msz_int sz) (vw c)))).
      { destruct sz; try congruence; inversion Hload; reflexivity. }
      subst v. eexists; split; [exact Hread|].
      rewrite dv_tag0, (dv_tag0' c Htag), wbytes8_wbv.
      unfold bi. rewrite <- to_Z_land7.
      apply load_result_sub; [exact Hne|]. rewrite to_Z_land7. exact Hcell.
    + apply (Hslow (slots_of_val c)).
      * apply slots_of_val_sound. intros j Hj. exact (Hcells j Hj).
      * destruct sz; try congruence; exact Hload.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma length_store_bytes_of sz w : length (store_bytes_of sz w) = msz_nat sz.
Proof. destruct sz; apply length_Z_to_le_bytes. Qed.

Lemma rview_write_in' bs m a j :
  Z.of_nat (length bs) <= 2 ^ 64 -> (j < length bs)%nat ->
  rview segs (write_to_mem m a bs) (aoff a j) = nth_error bs j.
Proof.
  intros Hlen Hj. destruct (nth_error bs j) as [b|] eqn:E.
  - apply rview_write_in; assumption.
  - apply nth_error_None in E. lia.
Qed.

(* [comment removed for export] *)
Lemma frame_same_region t z off (k : nat) :
  0 <= z < 2 ^ 63 -> 0 <= off -> off + Z.of_nat k < 2 ^ 63 ->
  z <> off + Z.of_nat k ->
  adr rho t z <> aoff (adr rho t off) k.
Proof.
  intros Hz Hoff Hk Hne E. rewrite aoff_adr in E. apply adr_inj in E; lia.
Qed.

(* [comment removed for export] *)
Lemma frame_other_region t t' z off (k : nat) lo lenr lo' lenr' :
  bv_unsigned (rho t) + lenr < 2 ^ 63 -> bv_unsigned (rho t') + lenr' < 2 ^ 63 ->
  (bv_unsigned (rho t) + lenr <= bv_unsigned (rho t') + lo'
   \/ bv_unsigned (rho t') + lenr' <= bv_unsigned (rho t) + lo) ->
  0 <= lo' -> lo' <= z < lenr' -> 0 <= lo -> lo <= off -> off + Z.of_nat k < lenr ->
  adr rho t' z <> aoff (adr rho t off) k.
Proof.
  intros H1 H2 Hsep Hlo' Hz Hlo Hoff Hk E. rewrite aoff_adr in E.
  apply (f_equal bv_unsigned) in E. rewrite !adr_unsigned in E by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma page_ok_frame m t pn B p a bs :
  page_ok segs IM rho m t pn B p ->
  (forall ci (j k : nat), 0 <= to_Z ci -> to_Z ci * 8 + Z.of_nat j < B -> (j < 8)%nat -> (k < length bs)%nat ->
     adr rho t (to_Z pn * 4096 + to_Z ci * 8 + Z.of_nat j) <> aoff a k) ->
  page_ok segs IM rho (write_to_mem m a bs) t pn B p.
Proof.
  intros (Hw & Hc & Hs & Hcut) Hfr. split; [|split; [|split]].
  - intros Hwr j Hj. apply wview_write. apply Hw; assumption.
  - intros ci v Hci Hcell j Hj. rewrite rview_write_out.
    + apply Hc; assumption.
    + intros k Hk. apply Hfr; [lia | Z.div_mod_to_equations; lia | assumption | assumption].
  - intros ci sl Hci Hcb Hi j Hj. destruct (Hs ci sl Hci Hcb Hi j Hj) as [Hin Hout]. split; [|exact Hout].
    intros Hb. apply slot_ok_val. rewrite rview_write_out.
    + apply slot_ok_val. exact (Hin Hb).
    + intros k Hk. replace (to_Z j) with (Z.of_nat (Z.to_nat (to_Z j))) by lia.
      apply Hfr; [assumption | lia | lia | assumption].
  - exact Hcut.
Qed.

(* [comment removed for export] *)
Lemma insert_bytes_nth (bi n : int) (c v : w64) (j : nat) :
  1 <= to_Z n -> to_Z bi + to_Z n <= 8 -> (j < 8)%nat ->
  nth_error (w_bytes (w_insert bi n c v)) j =
  if (Z.to_nat (to_Z bi) <=? j)%nat && (j <? Z.to_nat (to_Z bi) + Z.to_nat (to_Z n))%nat
  then nth_error (Z_to_le_bytes (Z.to_nat (to_Z n)) (wZ v)) (j - Z.to_nat (to_Z bi))
  else nth_error (w_bytes c) j.
Proof.
  intros Hn Hbn Hj. pose proof (i63_range bi) as Hbi.
  rewrite w_bytes_insert by assumption.
  set (nb := Z.to_nat (to_Z bi)). set (nn := Z.to_nat (to_Z n)).
  assert (Hnb : (nb + nn <= 8)%nat) by (unfold nb, nn; lia).
  pose proof (length_w_bytes c) as HL.
  assert (Hl1 : length (firstn nb (w_bytes c)) = nb) by (rewrite firstn_length_le; lia).
  destruct (Nat.leb_spec nb j) as [H1|H1]; cbn [andb].
  - rewrite nth_error_app2 by lia. rewrite Hl1.
    destruct (Nat.ltb_spec j (nb + nn)) as [H2|H2].
    + rewrite nth_error_app1 by (rewrite length_Z_to_le_bytes; lia). reflexivity.
    + rewrite nth_error_app2 by (rewrite length_Z_to_le_bytes; lia).
      rewrite length_Z_to_le_bytes, nth_error_skipn. f_equal. lia.
  - rewrite nth_error_app1 by lia. rewrite nth_error_firstn.
    destruct (Nat.ltb_spec j nb); [reflexivity | lia].
Qed.

Lemma store_bytes_of_tag0 sz (w : w64) :
  store_bytes_of sz (wbv w) = Z_to_le_bytes (msz_nat sz) (wZ w).
Proof.
  destruct sz; unfold store_bytes_of, low32; cbn [msz_nat].
  - apply (store_bytes_of_word 8 1); [reflexivity | lia].
  - apply (store_bytes_of_word 16 2); [reflexivity | lia].
  - apply (store_bytes_of_word 32 4); [reflexivity | lia].
  - rewrite wbv_unsigned. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma store_bytes_of_firstn sz (x : word) :
  store_bytes_of sz x = firstn (msz_nat sz) (wbytes8 x).
Proof.
  rewrite <- (wbv_w_of_bv x) at 1. rewrite store_bytes_of_tag0, wZ_w_of_bv.
  unfold wbytes8. rewrite Z_to_le_bytes_firstn by (destruct sz; cbn; lia). reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition store_newc (p : page) (pn ci bi : int) (sz : msize) (v : fval) : cell :=
  match sz with
  | SZ8 => CV v
  | _ => match cell_at IM p pn ci with
         | Some c => if ((vtag c =? 0) && (vtag v =? 0))%uint63
                     then CV (FV 0 (w_insert bi (msz_int sz) (vw c) (vw v)))
                     else store_cell IM p pn ci bi (msz_int sz) v
         | None => store_cell IM p pn ci bi (msz_int sz) v
         end
  end.

Definition store_page (p : page) (pn ci bi : int) (sz : msize) (v : fval) : page :=
  PG true (pg_kind p) (iset ci (store_newc p pn ci bi sz v) (pg_cells p)).

Definition store_region (rg : region) (pn : int) (p' : page) : region :=
  RGK (rg_lo rg) (rg_len rg) (rg_align rg) (rg_dflt rg) (iset pn p' (rg_pages rg)) (rg_clo rg) (rg_chi rg) (rg_kind rg).

Lemma fm_store_inv M t top off sz v M' :
  fm_store IM M (FV t (W64 top off)) sz v = Some M' ->
  exists rg p,
    iget t M = Some rg
    /\ page_at IM rg t (off >> 12)%uint63 = Some p
    /\ pg_wr p = true
    /\ negb ((top land 1) =? 0)%uint63 = false
    /\ negb ((off land 7) + msz_int sz <=? 8)%uint63 = false
    /\ negb (in_region rg off (msz_int sz)) = false
    /\ M' = iset t (store_region rg (off >> 12)%uint63
                     (store_page p (off >> 12)%uint63 ((off land 4095) >> 3)%uint63
                                 (off land 7)%uint63 sz v)) M.
Proof.
  intros Hst. unfold fm_store in Hst. cbv zeta in Hst.
  destruct (negb ((top land 1) =? 0)%uint63) eqn:C1; [discriminate|].
  destruct (negb ((off land 7) + msz_int sz <=? 8)%uint63) eqn:C2; [discriminate|].
  destruct (iget t M) as [rg|] eqn:Hrg; [|discriminate].
  destruct (negb (in_region rg off (msz_int sz))) eqn:C3; [discriminate|].
  destruct (page_at IM rg t (off >> 12)%uint63) as [p|] eqn:Hp; [|discriminate].
  destruct (negb (pg_wr p)) eqn:C4; [discriminate|]. apply negb_false_iff in C4.
  exists rg, p. inversion Hst. repeat split; assumption.
Qed.

(* [comment removed for export] *)
Lemma page_at_store_region rg t pn p' pn1 :
  page_at IM (store_region rg pn p') t pn1 =
  if (pn1 =? pn)%uint63 then Some p' else page_at IM rg t pn1.
Proof.
  unfold page_at, page_in_region, store_region. cbn [rg_pages rg_dflt rg_lo rg_len].
  rewrite iget_iset. destruct (pn1 =? pn)%uint63; reflexivity.
Qed.

Lemma cell_at_store_page p pn ci bi sz v ci1 :
  cell_at IM (store_page p pn ci bi sz v) pn ci1 =
  if (ci1 =? ci)%uint63
  then match store_newc p pn ci bi sz v with CV x => Some x | CU => None | CB _ => None end
  else cell_at IM p pn ci1.
Proof.
  unfold cell_at, store_page. cbn [pg_cells pg_kind]. rewrite iget_iset.
  destruct (ci1 =? ci)%uint63; reflexivity.
Qed.

Lemma iget_store_page p pn ci bi sz v ci1 :
  iget ci1 (pg_cells (store_page p pn ci bi sz v)) =
  if (ci1 =? ci)%uint63 then Some (store_newc p pn ci bi sz v) else iget ci1 (pg_cells p).
Proof. unfold store_page. cbn [pg_cells]. apply iget_iset. Qed.

(* [comment removed for export] *)
Lemma store_newc_sound m t pn B p ci (bi : int) sz v g' :
  page_ok segs IM rho m t pn B p -> 0 <= to_Z ci ->
  (to_Z ci < B / 8 \/ to_Z ci * 8 < B < to_Z ci * 8 + 8) ->
  to_Z bi + Z.of_nat (msz_nat sz) <= 8 ->
  (forall j : nat, (j < 8)%nat -> to_Z bi <= Z.of_nat j < to_Z bi + Z.of_nat (msz_nat sz) ->
      g' j = nth_error (wbytes8 (dv rho v)) (Z.to_nat (Z.of_nat j - to_Z bi))) ->
  (forall j : nat, (j < 8)%nat -> ~ (to_Z bi <= Z.of_nat j < to_Z bi + Z.of_nat (msz_nat sz)) ->
      g' j = cell_view m t pn ci j) ->
  cell_val (store_newc p pn ci bi sz v) g'.
Proof.
  intros Hpage Hci0 Hcic Hb Hin Hout. pose proof (i63_range bi) as Hb0. pose proof (msz_nat_pos sz) as Hn.
  assert (Hslow : cell_val (store_cell IM p pn ci bi (msz_int sz) v) g').
  { unfold store_cell. apply norm_slots_sound.
    apply (store_slots_sound bi (msz_int sz) v _ (cell_view m t pn ci) g').
    - rewrite to_Z_msz. exact Hb.
    - apply (slots_at_sound_any m t pn B p ci); assumption.
    - intros j Hj Hr. rewrite to_Z_msz in Hr. apply Hin; assumption.
    - intros j Hj Hr. rewrite to_Z_msz in Hr. apply Hout; assumption. }
  destruct (msize_eq_dec sz SZ8) as [->|Hne].
  { cbn [store_newc cell_val msz_nat] in *. intros j Hj.
    rewrite (Hin j Hj) by lia. f_equal. lia. }
  assert (E : store_newc p pn ci bi sz v =
              match cell_at IM p pn ci with
              | Some c => if ((vtag c =? 0) && (vtag v =? 0))%uint63
                          then CV (FV 0 (w_insert bi (msz_int sz) (vw c) (vw v)))
                          else store_cell IM p pn ci bi (msz_int sz) v
              | None => store_cell IM p pn ci bi (msz_int sz) v
              end) by (destruct sz; try congruence; reflexivity).
  rewrite E. clear E.
  destruct (cell_at IM p pn ci) as [c|] eqn:Hcc; [|exact Hslow].
  destruct ((vtag c =? 0) && (vtag v =? 0))%uint63 eqn:T; [|exact Hslow].
  apply andb_true_iff in T as [T1 T2].
  assert (Hci : 0 <= to_Z ci < B / 8).
  { destruct Hcic as [H|H]; [lia|]. exfalso. rewrite (proj2 (proj2 (proj2 Hpage)) ci Hci0 H) in Hcc. discriminate. }
  pose proof (proj1 (proj2 Hpage) _ _ Hci Hcc) as Hcells.
  cbn [cell_val]. intros j Hj. rewrite dv_tag0, wbytes8_wbv.
  assert (Hs1 : 1 <= to_Z (msz_int sz)) by (rewrite to_Z_msz; lia).
  assert (Hs2 : to_Z bi + to_Z (msz_int sz) <= 8) by (rewrite to_Z_msz; lia).
  rewrite (insert_bytes_nth _ _ _ _ j Hs1 Hs2 Hj). rewrite to_Z_msz, Nat2Z.id.
  destruct (Nat.leb_spec (Z.to_nat (to_Z bi)) j) as [B1|B1]; cbn [andb].
  - destruct (Nat.ltb_spec j (Z.to_nat (to_Z bi) + msz_nat sz)) as [B2|B2].
    + rewrite (Hin j Hj) by lia. rewrite (dv_tag0' v T2), wbytes8_wbv.
      replace (Z.to_nat (Z.of_nat j - to_Z bi)) with (j - Z.to_nat (to_Z bi))%nat by lia.
      rewrite <- (Z_to_le_bytes_firstn (msz_nat sz) 8) by lia.
      rewrite nth_error_firstn_lt by lia. reflexivity.
    + rewrite (Hout j Hj) by lia. unfold cell_view.
      rewrite (Hcells j Hj), (dv_tag0' c T1), wbytes8_wbv. reflexivity.
  - rewrite (Hout j Hj) by lia. unfold cell_view.
    rewrite (Hcells j Hj), (dv_tag0' c T1), wbytes8_wbv. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sget_store_slots_out bi n v s (j : int) :
  0 <= to_Z j < 8 -> to_Z bi + to_Z n <= to_Z j -> sget j (store_slots bi n v s) = sget j s.
Proof.
  intros Hj Hout. pose proof (i63_range bi). pose proof (i63_range n).
  assert (E : ((bi <=? j) && (j <? bi + n))%uint63 = false).
  { destruct (bi <=? j)%uint63 eqn:E1; [|reflexivity]. destruct (j <? bi + n)%uint63 eqn:E2; [|reflexivity].
    exfalso. apply Uint63.leb_spec in E1. apply Uint63.ltb_spec in E2. rewrite Uint63.add_spec, i63_wB in E2.
    pose proof (Z.mod_le (to_Z bi + to_Z n) (2 ^ 63) ltac:(lia) ltac:(lia)). lia. }
  destruct (int_cases8 j Hj) as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; unfold sget, store_slots; cbv zeta;
    cbn [Uint63.eqb sl0 sl1 sl2 sl3 sl4 sl5 sl6 sl7]; rewrite E; reflexivity.
Qed.

Lemma norm_slots_SU7 s : sl7 s = SU -> norm_slots s = CB s.
Proof.
  intros H7. destruct (norm_slots_shape s) as [E | [(b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & ->) | (v0 & j0 & v1 & j1 & v2 & j2 & v3 & j3 & v4 & j4 & v5 & j5 & v6 & j6 & v7 & j7 & ->)]];
    [exact E | discriminate H7 | discriminate H7].
Qed.

(* [comment removed for export] *)
Lemma store_newc_cut m t pn B p ci (bi : int) sz v :
  page_ok segs IM rho m t pn B p -> 0 <= to_Z ci -> to_Z ci * 8 < B < to_Z ci * 8 + 8 ->
  to_Z ci * 8 + to_Z bi + Z.of_nat (msz_nat sz) <= B ->
  exists sl', store_newc p pn ci bi sz v = CB sl'
              /\ forall j : int, 0 <= to_Z j < 8 -> B <= to_Z ci * 8 + to_Z j -> sget j sl' = SU.
Proof.
  intros (_ & _ & Hslots & Hcut) Hci0 Hb Hacc. pose proof (i63_range bi) as Hbi. pose proof (msz_nat_pos sz) as Hn.
  destruct (msize_eq_dec sz SZ8) as [->|Hne]; [cbn [msz_nat] in Hacc; lia|].
  pose proof (Hcut ci Hci0 Hb) as Hnone.
  (* [comment removed for export] *)
  assert (Hold : forall j : int, 0 <= to_Z j < 8 -> B <= to_Z ci * 8 + to_Z j -> sget j (slots_at IM p pn ci) = SU).
  { intros j Hj Hjb. unfold slots_at. rewrite Hnone.
    destruct (iget ci (pg_cells p)) as [[u| |sl]|] eqn:Hi;
      try (destruct (int_cases8 j Hj) as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; reflexivity).
    exact (proj2 (Hslots ci sl Hci0 ltac:(lia) Hi j Hj) Hjb). }
  assert (Hst : forall j : int, 0 <= to_Z j < 8 -> B <= to_Z ci * 8 + to_Z j ->
                 sget j (store_slots bi (msz_int sz) v (slots_at IM p pn ci)) = SU).
  { intros j Hj Hjb. rewrite sget_store_slots_out; [exact (Hold j Hj Hjb) | exact Hj | rewrite to_Z_msz; lia]. }
  assert (E : store_newc p pn ci bi sz v = store_cell IM p pn ci bi (msz_int sz) v).
  { destruct sz; try congruence; cbn [store_newc]; rewrite Hnone; reflexivity. }
  rewrite E. unfold store_cell.
  pose proof (Hst 7%uint63 ltac:(cbn; lia) ltac:(change (to_Z 7%uint63) with 7; lia)) as H7.
  rewrite (norm_slots_SU7 _ H7).
  eexists. split; [reflexivity|]. exact Hst.
Qed.

Theorem fm_store_sound : forall M m a sz v M',
  mem_ok segs IM rho M m ->
  fm_store IM M a sz v = Some M' ->
  store_ok segs m (dv rho a) (msz_nat sz) = true
  /\ mem_ok segs IM rho M' (write_to_mem m (dv rho a) (store_bytes_of sz (dv rho v))).
Proof.
  intros M m [t [top off]] sz v M' [Hmem Hsep] Hst.
  destruct (fm_store_inv _ _ _ _ _ _ _ Hst) as (rg & p & Hrg & Hp & C4 & C1 & C2 & C3 & HM').
  clear Hst.
  destruct (checks_inv top off sz rg C1 C2 C3) as (Htop & Hcell & Hoff & Hlen & Hlo & Hin).
  pose proof (i63_range off) as Hoff0.
  pose proof (Z.mod_pos_bound (to_Z off) 8 ltac:(lia)) as Hb.
  pose proof (msz_nat_pos sz) as Hn.
  set (pn := (off >> 12)%uint63) in *.
  set (ci := ((off land 4095) >> 3)%uint63) in *.
  set (bi := Z.to_nat (to_Z off mod 8)).
  destruct (Hmem t rg Hrg) as [Hreg Hpages].
  pose proof (proj1 Hreg) as Hpl.
  assert (Hpn : to_Z pn < 2 ^ 50).
  { unfold pn. rewrite to_Z_lsr12. apply Z.div_lt_upper_bound; lia. }
  destruct (Hpages _ _ Hpn Hp) as [Hpage Hpb].
  pose proof Hpage as (Hwv & Hcells & Hslots & Hcut).
  assert (Hcic : (0 <= to_Z ci < clim rg pn) \/ (to_Z ci * 8 < blim rg pn < to_Z ci * 8 + 8)).
  { unfold ci, pn. rewrite to_Z_lsr3, to_Z_land4095.
    apply (ci_cases rg _ (to_Z off) (Z.of_nat (msz_nat sz))); [lia | lia | exact Hcell | exact Hin | apply to_Z_lsr12]. }
  assert (Hci0 : 0 <= to_Z ci) by (unfold ci; rewrite to_Z_lsr3, to_Z_land4095; Z.div_mod_to_equations; lia).
  pose proof (clim_le rg pn) as Hcl512. pose proof (blim_le rg pn) as Hbl4096.
  assert (Hdec : to_Z pn * 4096 + to_Z ci * 8 + to_Z off mod 8 = to_Z off).
  { unfold pn, ci. rewrite to_Z_lsr12, to_Z_lsr3, to_Z_land4095. apply off_decomp. lia. }
  (* [comment removed for export] *)
  assert (Hacc : to_Z ci * 8 + to_Z off mod 8 + Z.of_nat (msz_nat sz) <= blim rg pn).
  { unfold blim. pose proof (Z.mod_pos_bound (to_Z off) 4096 ltac:(lia)).
    assert (to_Z pn * 4096 <= to_Z off) by (unfold pn; rewrite to_Z_lsr12; Z.div_mod_to_equations; lia).
    assert (to_Z ci * 8 + to_Z off mod 8 = to_Z off mod 4096) by (unfold ci; rewrite to_Z_lsr3, to_Z_land4095; Z.div_mod_to_equations; lia).
    assert (to_Z off mod 4096 + Z.of_nat (msz_nat sz) <= 4096) by (Z.div_mod_to_equations; lia).
    lia. }
  assert (Haddr : forall j : nat,
            adr rho t (to_Z pn * 4096 + to_Z ci * 8 + Z.of_nat (bi + j))
            = aoff (dv rho (FV t (W64 top off))) j).
  { intros j. apply access_addr; assumption. }
  rewrite (dv_adr t top off Hpl Htop) in *.
  set (bytes := store_bytes_of sz (dv rho v)).
  assert (Hlb : length bytes = msz_nat sz) by apply length_store_bytes_of.
  split.
  { (* [comment removed for export] *)
    apply store_ok_intro. intros j Hj. rewrite <- Haddr.
    rewrite <- Z.add_assoc. apply (Hwv C4). unfold bi. lia. }
  set (p' := store_page p pn ci (off land 7)%uint63 sz v) in *.
  set (rg' := store_region rg pn p') in *.
  subst M'.
  (* [comment removed for export] *)
  assert (Hnew : cell_val (store_newc p pn ci (off land 7)%uint63 sz v)
                   (cell_view (write_to_mem m (adr rho t (to_Z off)) bytes) t pn ci)).
  { apply (store_newc_sound m t pn (blim rg pn) p ci); [exact Hpage | exact Hci0 | unfold clim in Hcic; lia | rewrite to_Z_land7; exact Hcell | |].
    - intros j Hj Hr. rewrite to_Z_land7 in Hr. unfold cell_view.
      replace j with (bi + (j - bi))%nat at 1 by (unfold bi; lia).
      rewrite Haddr. rewrite rview_write_in' by (rewrite Hlb; unfold bi; lia).
      unfold bytes. rewrite store_bytes_of_firstn, nth_error_firstn_lt by (unfold bi; lia).
      f_equal. rewrite to_Z_land7. unfold bi. lia.
    - intros j Hj Hr. rewrite to_Z_land7 in Hr. unfold cell_view.
      apply rview_write_out. intros k Hk. rewrite Hlb in Hk.
      apply frame_same_region; unfold bi in *; lia. }
  (* [comment removed for export] *)
  assert (HM'get : forall t1 rg1, iget t1 (iset t rg' M) = Some rg1 ->
            (t1 = t /\ rg1 = rg') \/ (t1 <> t /\ iget t1 M = Some rg1)).
  { intros t1 rg1 H. rewrite iget_iset in H.
    destruct (t1 =? t)%uint63 eqn:E.
    - apply Uint63.eqb_spec in E. left. split; [exact E | congruence].
    - apply eqb_false_spec in E. right. split; assumption. }
  assert (HM'len : forall t1 rg1, iget t1 (iset t rg' M) = Some rg1 ->
            exists rg0, iget t1 M = Some rg0 /\ rg_len rg0 = rg_len rg1 /\ rg_lo rg0 = rg_lo rg1).
  { intros t1 rg1 H. destruct (HM'get _ _ H) as [[-> ->]|[_ H']].
    - exists rg. repeat split; assumption.
    - exists rg1. repeat split; assumption. }
  split.
  2:{ (* [comment removed for export] *)
    intros t1 t2 rg1 rg2 Hne H1 H2.
    destruct (HM'len _ _ H1) as (r1 & G1 & L1 & O1).
    destruct (HM'len _ _ H2) as (r2 & G2 & L2 & O2).
    rewrite <- L1, <- L2, <- O1, <- O2. exact (Hsep t1 t2 r1 r2 Hne G1 G2). }
  intros t1 rg1 H1.
  destruct (HM'get _ _ H1) as [[-> ->]|[Hne1 G1]].
  - (* [comment removed for export] *)
    split; [exact Hreg|]. intros pn1 p1 Hpn1 Hp1.
    change (blim rg' pn1) with (blim rg pn1).
    assert (Hp1' : (pn1 = pn /\ p1 = p') \/ (pn1 <> pn /\ page_at IM rg t pn1 = Some p1)).
    { unfold rg' in Hp1. rewrite page_at_store_region in Hp1.
      destruct (pn1 =? pn)%uint63 eqn:E.
      - apply Uint63.eqb_spec in E. left. split; [exact E | congruence].
      - apply eqb_false_spec in E. right. split; assumption. }
    destruct Hp1' as [[-> ->]|[Hnepn Hp1']].
    + (* [comment removed for export] *)
      split; [|exact Hpb]. split; [|split; [|split]].
      * intros _ j Hj. apply wview_write. apply (Hwv C4). exact Hj.
      * intros ci1 v1 Hci1 Hcell1 j Hj.
        unfold p' in Hcell1. rewrite cell_at_store_page in Hcell1.
        destruct (ci1 =? ci)%uint63 eqn:E.
        -- (* [comment removed for export] *)
           apply Uint63.eqb_spec in E. subst ci1.
           destruct (store_newc p pn ci (off land 7)%uint63 sz v) as [x| |sl]; try discriminate.
           inversion Hcell1; subst x. exact (Hnew j Hj).
        -- (* [comment removed for export] *)
           apply eqb_false_spec in E.
           assert (Hne : to_Z ci1 <> to_Z ci) by (intros Q; apply E, to_Z_inj, Q).
           rewrite rview_write_out.
           ++ apply Hcells; [exact Hci1 | exact Hcell1 | exact Hj].
           ++ intros k Hk. rewrite Hlb in Hk.
              apply frame_same_region; unfold bi in *; lia.
      * intros ci1 sl Hci1 Hcb1 Hi1 j Hj.
        unfold p' in Hi1. rewrite iget_store_page in Hi1.
        destruct (ci1 =? ci)%uint63 eqn:E.
        -- apply Uint63.eqb_spec in E. subst ci1. inversion Hi1 as [Hi1']. split.
           ++ intros Hjb. rewrite Hi1' in Hnew.
              cbn [cell_val] in Hnew. apply slot_ok_val.
              pose proof (slots_val_sget _ _ j Hnew Hj) as Hs. unfold cell_view in Hs.
              rewrite Z2Nat.id in Hs by lia. exact Hs.
           ++ intros Hjb.
              assert (Hcutc : to_Z ci * 8 < blim rg pn < to_Z ci * 8 + 8) by lia.
              destruct (store_newc_cut m t pn (blim rg pn) p ci (off land 7)%uint63 sz v Hpage Hci0 Hcutc
                          ltac:(rewrite to_Z_land7; lia)) as (sl' & Esl' & Hsu).
              rewrite Esl' in Hi1'. injection Hi1' as ->. exact (Hsu j Hj Hjb).
        -- apply eqb_false_spec in E.
           assert (Hne : to_Z ci1 <> to_Z ci) by (intros Q; apply E, to_Z_inj, Q).
           destruct (Hslots ci1 sl Hci1 Hcb1 Hi1 j Hj) as [Hsin Hsout]. split; [|exact Hsout].
           intros Hjb. apply slot_ok_val. rewrite rview_write_out.
           ++ apply slot_ok_val. exact (Hsin Hjb).
           ++ intros k Hk. rewrite Hlb in Hk.
              apply frame_same_region; unfold bi in *; lia.
      * intros ci1 Hci1 Hcut1. unfold p'. rewrite cell_at_store_page.
        destruct (ci1 =? ci)%uint63 eqn:E; [|exact (Hcut ci1 Hci1 Hcut1)].
        apply Uint63.eqb_spec in E. subst ci1.
        destruct (store_newc_cut m t pn (blim rg pn) p ci (off land 7)%uint63 sz v Hpage Hci0 Hcut1
                    ltac:(rewrite to_Z_land7; lia)) as (sl' & Esl' & _).
        rewrite Esl'. reflexivity.
    + (* [comment removed for export] *)
      destruct (Hpages _ _ Hpn1 Hp1') as [Hok Hb1]. split; [|exact Hb1].
      apply page_ok_frame; [exact Hok|].
      intros ci1 j k Hci1 Hcb1 Hj Hk. rewrite Hlb in Hk.
      assert (Hne : to_Z pn1 <> to_Z pn) by (intros Q; apply Hnepn, to_Z_inj, Q).
      pose proof (i63_range pn1). pose proof (blim_le rg pn1).
      apply frame_same_region; unfold bi in *; lia.
  - (* [comment removed for export] *)
    destruct (Hmem t1 rg1 G1) as [Hreg1 Hpages1]. split; [exact Hreg1|].
    intros pn1 p1 Hpn1 Hp1. destruct (Hpages1 _ _ Hpn1 Hp1) as [Hok Hb1]. split; [|exact Hb1].
    apply page_ok_frame; [exact Hok|].
    intros ci1 j k Hci1 Hcb1 Hj Hk. rewrite Hlb in Hk.
    destruct Hreg as (_ & _ & Hr & _). destruct Hreg1 as (_ & _ & Hr1 & _).
    pose proof (blim_bytes rg1 pn1 (to_Z ci1 * 8 + Z.of_nat j) ltac:(lia)) as [Hcb1' _].
    pose proof (proj1 Hb1) as Hb1lo. pose proof (proj1 Hpb) as Hpblo.
    pose proof (blim_bytes rg pn (to_Z ci * 8 + to_Z off mod 8) ltac:(lia)) as [Hinpn _].
    clear Hb1 Hpb Hcic Hcl512.
    pose proof (i63_range pn1). pose proof (i63_range (rg_lo rg)). pose proof (i63_range (rg_lo rg1)).
    apply (frame_other_region t t1 _ _ k (to_Z (rg_lo rg)) (to_Z (rg_len rg))
             (to_Z (rg_lo rg1)) (to_Z (rg_len rg1)));
      [exact Hr | exact Hr1 | | lia | lia | lia | lia | lia].
    apply (Hsep t t1 rg rg1); [intros Q; apply Hne1; symmetry; exact Q | exact Hrg | exact G1].
Qed.


(* [comment removed for export] *)
Theorem fm_store_regions : forall M a sz v M' t,
  fm_store IM M a sz v = Some M' ->
  match iget t M, iget t M' with
  | Some rg, Some rg' => rg_len rg' = rg_len rg /\ rg_align rg' = rg_align rg
  | None, None => True
  | _, _ => False
  end.
Proof.
  intros M [t0 [top off]] sz v M' t Hst.
  destruct (fm_store_inv _ _ _ _ _ _ _ Hst) as (rg & p & Hrg & _ & _ & _ & _ & _ & ->).
  rewrite iget_iset. destruct (t =? t0)%uint63 eqn:E.
  - apply Uint63.eqb_spec in E. subst t0. rewrite Hrg. cbn. split; reflexivity.
  - destruct (iget t M); [split; reflexivity | exact I].
Qed.

(* [comment removed for export] *)
Theorem fm_store_regions' : forall M a sz v M' t,
  fm_store IM M a sz v = Some M' ->
  match iget t M, iget t M' with
  | Some rg, Some rg' =>
      rg_lo rg' = rg_lo rg /\ rg_len rg' = rg_len rg /\ rg_align rg' = rg_align rg
      /\ rg_dflt rg' = rg_dflt rg
  | None, None => True
  | _, _ => False
  end.
Proof.
  intros M [t0 [top off]] sz v M' t Hst.
  destruct (fm_store_inv _ _ _ _ _ _ _ Hst) as (rg & p & Hrg & _ & _ & _ & _ & _ & ->).
  rewrite iget_iset. destruct (t =? t0)%uint63 eqn:E.
  - apply Uint63.eqb_spec in E. subst t0. rewrite Hrg. cbn. repeat split; reflexivity.
  - destruct (iget t M); [repeat split; reflexivity | exact I].
Qed.

(* [comment removed for export] *)
Theorem fm_store_bounds : forall M a sz v M' t,
  fm_store IM M a sz v = Some M' ->
  match iget t M, iget t M' with
  | Some rg, Some rg' => rg_clo rg' = rg_clo rg /\ rg_chi rg' = rg_chi rg
  | None, None => True
  | _, _ => False
  end.
Proof.
  intros M [t0 [top off]] sz v M' t Hst.
  destruct (fm_store_inv _ _ _ _ _ _ _ Hst) as (rg & p & Hrg & _ & _ & _ & _ & _ & ->).
  rewrite iget_iset. destruct (t =? t0)%uint63 eqn:E.
  - apply Uint63.eqb_spec in E. subst t0. rewrite Hrg. cbn. split; reflexivity.
  - destruct (iget t M); [split; reflexivity | exact I].
Qed.

(* [comment removed for export] *)
Definition claimed_wr (M : itrie region) (x : word) : Prop :=
  exists t rg pn p j,
    iget t M = Some rg /\ to_Z pn < 2 ^ 50 /\ page_at IM rg t pn = Some p /\ pg_wr p = true
    /\ 0 <= j < 4096 /\ to_Z pn * 4096 + j < to_Z (rg_len rg)        (* [comment removed for export] *)
    /\ x = adr rho t (to_Z pn * 4096 + j).

(* [comment removed for export] *)
Lemma fm_store_written_claimed M a sz v M' (k : nat) :
  to_Z (vtag a) < 2 ^ 60 ->
  fm_store IM M a sz v = Some M' -> (k < msz_nat sz)%nat ->
  claimed_wr M (aoff (dv rho a) k).
Proof.
  destruct a as [t [top off]]. cbn [vtag]. intros Hpl Hst Hk.
  destruct (fm_store_inv _ _ _ _ _ _ _ Hst) as (rg & p & Hrg & Hp & C4 & C1 & C2 & C3 & _).
  destruct (checks_inv top off sz rg C1 C2 C3) as (Htop & Hcell & Hoff & Hlen & Hlo & Hin).
  pose proof (i63_range off) as Hoff0.
  pose proof (Z.mod_pos_bound (to_Z off) 8 ltac:(lia)) as Hb.
  exists t, rg, (off >> 12)%uint63, p,
    (to_Z ((off land 4095) >> 3)%uint63 * 8 + Z.of_nat (Z.to_nat (to_Z off mod 8) + k)).
  split; [exact Hrg|]. split.
  { rewrite to_Z_lsr12. apply Z.div_lt_upper_bound; lia. }
  split; [exact Hp|]. split; [exact C4|].
  pose proof (cell_index_range (to_Z off) ltac:(lia)) as Hci.
  pose proof (off_decomp (to_Z off) ltac:(lia)) as Hdec.
  split; [|split].
  - rewrite to_Z_lsr3, to_Z_land4095. lia.
  - rewrite to_Z_lsr12, to_Z_lsr3, to_Z_land4095. lia.
  - rewrite <- (access_addr t top off k Hpl Htop). f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma fm_store_plain M m a sz v M' :
  mem_ok segs IM rho M m -> fm_store IM M a sz v = Some M' -> to_Z (vtag a) < 2 ^ 60.
Proof.
  destruct a as [t [top off]]. intros Hmem Hst.
  destruct (fm_store_inv _ _ _ _ _ _ _ Hst) as (rg & p & Hrg & _).
  exact (region_plain M m t rg Hmem Hrg).
Qed.

(* [comment removed for export] *)
Theorem fm_store_frame_strong : forall M a sz v M',
  to_Z (vtag a) < 2 ^ 60 ->
  fm_store IM M a sz v = Some M' ->
  forall m x, ~ claimed_wr M x ->
    write_to_mem m (dv rho a) (store_bytes_of sz (dv rho v)) x = m x.
Proof.
  intros M a sz v M' Hpl Hst m x Hx. apply write_to_mem_out.
  intros k Hk E. rewrite length_store_bytes_of in Hk. apply Hx. rewrite E.
  exact (fm_store_written_claimed M a sz v M' k Hpl Hst Hk).
Qed.

Theorem fm_store_frame : forall M m a sz v M',
  mem_ok segs IM rho M m ->
  fm_store IM M a sz v = Some M' ->
  forall x, ~ claimed_wr M x ->
    write_to_mem m (dv rho a) (store_bytes_of sz (dv rho v)) x = m x.
Proof.
  intros M m a sz v M' Hmem Hst x Hx.
  exact (fm_store_frame_strong M a sz v M' (fm_store_plain M m a sz v M' Hmem Hst) Hst m x Hx).
Qed.

(* [comment removed for export] *)
Theorem fm_store_wr_mono : forall M a sz v M',
  fm_store IM M a sz v = Some M' ->
  forall x, claimed_wr M' x -> claimed_wr M x.
Proof.
  intros M [t [top off]] sz v M' Hst x (t1 & rg1 & pn1 & p1 & j & H1 & Hpn1 & Hp1 & Hw1 & Hj & Hjl & ->).
  destruct (fm_store_inv _ _ _ _ _ _ _ Hst) as (rg & p & Hrg & Hp & C4 & _ & _ & _ & ->).
  rewrite iget_iset in H1. destruct (t1 =? t)%uint63 eqn:E.
  - apply Uint63.eqb_spec in E. subst t1. inversion H1; subst rg1. clear H1.
    rewrite page_at_store_region in Hp1. destruct (pn1 =? (off >> 12))%uint63 eqn:E2.
    + apply Uint63.eqb_spec in E2. subst pn1.
      exists t, rg, (off >> 12)%uint63, p, j. repeat split; try assumption; lia.
    + exists t, rg, pn1, p1, j. repeat split; try assumption; lia.
  - exists t1, rg1, pn1, p1, j. repeat split; try assumption; lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma fm_store_iget_other M a sz v M' t1 :
  fm_store IM M a sz v = Some M' -> t1 <> vtag a -> iget t1 M' = iget t1 M.
Proof.
  destruct a as [t [top off]]. cbn [vtag]. intros Hst Hne.
  destruct (fm_store_inv _ _ _ _ _ _ _ Hst) as (rg & p & _ & _ & _ & _ & _ & _ & ->).
  apply iget_iset_other. intros Q. apply Hne. symmetry. exact Q.
Qed.

(* [comment removed for export] *)
Lemma fm_store_iget_same M a sz v M' :
  fm_store IM M a sz v = Some M' ->
  exists rg p,
    iget (vtag a) M = Some rg
    /\ page_at IM rg (vtag a) (wlo (vw a) >> 12)%uint63 = Some p
    /\ pg_wr p = true
    /\ iget (vtag a) M' =
        Some (store_region rg (wlo (vw a) >> 12)%uint63
                (store_page p (wlo (vw a) >> 12)%uint63 ((wlo (vw a) land 4095) >> 3)%uint63
                            (wlo (vw a) land 7)%uint63 sz v)).
Proof.
  destruct a as [t [top off]]. cbn [vtag vw wlo]. intros Hst.
  destruct (fm_store_inv _ _ _ _ _ _ _ Hst) as (rg & p & Hrg & Hp & C4 & _ & _ & _ & ->).
  exists rg, p. repeat split; try assumption. apply iget_iset_same.
Qed.

(* [comment removed for export] *)
Lemma fm_store_page_at_other M a sz v M' rg rg' pn1 :
  fm_store IM M a sz v = Some M' ->
  iget (vtag a) M = Some rg -> iget (vtag a) M' = Some rg' ->
  pn1 <> (wlo (vw a) >> 12)%uint63 ->
  page_at IM rg' (vtag a) pn1 = page_at IM rg (vtag a) pn1.
Proof.
  intros Hst Hrg Hrg' Hne.
  destruct (fm_store_iget_same M a sz v M' Hst) as (rg0 & p & Hrg0 & _ & _ & HM').
  rewrite Hrg in Hrg0. inversion Hrg0; subst rg0. rewrite Hrg' in HM'. inversion HM'; subst rg'.
  rewrite page_at_store_region. rewrite (eqb_false_complete _ _ Hne). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma fm_store_page_at_same M a sz v M' rg rg' p :
  fm_store IM M a sz v = Some M' ->
  iget (vtag a) M = Some rg -> iget (vtag a) M' = Some rg' ->
  page_at IM rg (vtag a) (wlo (vw a) >> 12)%uint63 = Some p ->
  page_at IM rg' (vtag a) (wlo (vw a) >> 12)%uint63 =
  Some (store_page p (wlo (vw a) >> 12)%uint63 ((wlo (vw a) land 4095) >> 3)%uint63
                   (wlo (vw a) land 7)%uint63 sz v).
Proof.
  intros Hst Hrg Hrg' Hp.
  destruct (fm_store_iget_same M a sz v M' Hst) as (rg0 & p0 & Hrg0 & Hp0 & _ & HM').
  rewrite Hrg in Hrg0. inversion Hrg0; subst rg0. rewrite Hp in Hp0. inversion Hp0; subst p0.
  rewrite Hrg' in HM'. inversion HM'; subst rg'.
  rewrite page_at_store_region, Uint63.eqb_refl. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma cell_at_store_page_other p pn ci bi sz v ci1 :
  ci1 <> ci -> cell_at IM (store_page p pn ci bi sz v) pn ci1 = cell_at IM p pn ci1.
Proof.
  intros Hne. rewrite cell_at_store_page, (eqb_false_complete _ _ Hne). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma cell_at_store_page_same p pn ci bi sz v :
  cell_at IM (store_page p pn ci bi sz v) pn ci =
  match store_newc p pn ci bi sz v with CV x => Some x | CU => None | CB _ => None end.
Proof. rewrite cell_at_store_page, Uint63.eqb_refl. reflexivity. Qed.

Lemma store_newc_8 p pn ci bi v : store_newc p pn ci bi SZ8 v = CV v.
Proof. reflexivity. Qed.


End MemSound.
