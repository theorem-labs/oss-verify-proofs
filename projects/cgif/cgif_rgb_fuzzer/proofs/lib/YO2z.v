(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mremap.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0s YK0i YK0j YK15 YN06 YN02 YQ0b YK0v YQ0k.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YP0j YP0g YP0h YP0q YP0r YP0t YP0m YP0o YP10
YP0p YP0v YP0u YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO04 YO2f YO37 YO2i YO2k
YO2a YO2c YO2e YO2b YO2g YO2h YO30 YQ01.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section h. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition bytes_at (B : malloc_syms) (m : word -> option byte) (a : Z) (w : nat) (v : Z) : Prop :=
forall k, (k < w)%nat -> mbyte (ms_segs B) m (a + Z.of_nat k) = Some (Z_to_bv 8 (le_byte v w k)).
Lemma loc_addr_padd L p d : loc_addr L (LMem (padd p d)) = loc_addr L (LMem p) + d.
Proof. destruct p; cbn; lia. Qed.
Lemma direct_region_unique s g am fr g2 a2 :
WF s -> usedX [] s g am -> am_sc am = 63 -> ss_fr (nth_slot am 0) = Some fr -> fr_kind fr = FUser ->
usedX [] s g2 a2 -> prid (am_mem a2) = prid (am_mem am) -> g2 = g.
Proof.
intros HW Hu H63 Hfr Hk Hu2 Ep.
destruct (sptr_eq_dec' g2 g) as [E|Hne]; [exact E|]. exfalso.
pose proof (inv_groups HW g am Hu) as GG. pose proof GG as ((Glast & _ & Glen & _) & _ & Gsl & Gcl & Gmp & _).
destruct Gcl as [(C1 & C2 & C3 & _) | (C1 & _)]; [|lia].
destruct (Gmp ltac:(lia)) as (r & rg & Em & Hr & Hkd & Hl & Hlen & Hfit & _).
pose proof (used_group_region [] None U0 s g2 a2 HW Hu2) as (rg2 & Hr2 & _ & _ & Ho2 & Hext2 & _).
rewrite Ep, Em in Hr2. cbn [prid] in Hr2. rewrite Hr in Hr2. injection Hr2 as <-.
pose proof (extent_pos [] None s g2 a2 (inv_groups HW g2 a2 Hu2)) as EP2.
assert (EXT : group_extent am = am_maplen am * PGSZ - IB).
{ unfold group_extent, stride_of. rewrite C2. cbn [Z.eqb andb Z.add Z.mul].
destruct (am_maplen am =? 0) eqn:E; [apply Z.eqb_eq in E; lia|]. cbn [negb]. unfold PGSZ. lia. }
destruct (inv_laminar HW g am g2 a2 Hu Hu2 ltac:(auto) ltac:(symmetry; exact Ep)) as [SD | [IN | IN]].
- unfold spans_disjoint in SD. rewrite Em in SD. cbn [poff] in SD. unfold IB in *. lia.
- destruct IN as (j & frj & c & ac & Hj & Hfrj & Hkj & Huc & Hml & Hmc & Hpo & _).
rewrite Em in Hpo. cbn [poff] in Hpo. rewrite Hmc in Hpo. unfold slot_start in Hpo. rewrite poff_padd in Hpo.
pose proof (used_group_region [] None U0 s g2 a2 HW Hu2) as (_ & _ & _ & _ & Ho2' & _).
pose proof (stride_pos [] None s g2 a2 (inv_groups HW g2 a2 Hu2)). unfold UNIT in *. nia.
- destruct IN as (j & frj & c & ac & Hj & Hfrj & Hkj & _). rewrite C2 in Hj.
assert (j = 0) as -> by lia. rewrite Hfr in Hfrj. injection Hfrj as <-. rewrite Hk in Hkj. discriminate.
Qed.
Definition newam (am : ameta) (fr : frame) (n : Z) (rx : nat) (mlx : Z) : ameta :=
mkAMeta None None (SP rx 0) 0 0 0 63 mlx 0 [resize_slot (mlx * 4096 - UNIT) 0 (nth_slot am 0) (fr_off fr) n].
Section u.
Variable B : malloc_syms.
Variables (Lx : layout) (memx : word -> option byte) (g : sptr) (am : ameta) (fr : frame) (n : Z) (rx : nat) (mlx : Z).
Variables (h3 h16 : Z).
Hypothesis Hhdr : ss_hdr (nth_slot am 0) = Some (h3, h16).
Let amx := newam am fr n rx mlx.
Let RET := ly_reg Lx rx.
Let G := loc_addr Lx (LMem g).
Let OFF := fr_off fr.
Let NEEDX := mlx * 4096.
Let P' := RET + 16 + 16 * OFF.
Let END' := RET + NEEDX - 4.
Let RSV' := NEEDX - 20 - 16 * OFF - n.
Let RC' := if 5 <=? RSV' then 5 else RSV'.
Hypothesis Hml : 1 <= mlx.
Hypothesis Hoff0 : OFF = 0 -> h16 = 0.
Hypothesis Y1 : bytes_at B memx RET 8 G.
Hypothesis Y2 : bytes_at B memx (RET + 8) 4 0.
Hypothesis Y3 : bytes_at B memx (RET + 12) 1 0.
Hypothesis Y4 : OFF <> 0 -> bytes_at B memx (RET + 13) 1 h3 /\ bytes_at B memx (RET + 14) 2 h16.
Hypothesis Y5 : bytes_at B memx (P' - 4) 1 0.
Hypothesis Y6 : bytes_at B memx (P' - 3) 1 (32 * RC').
Hypothesis Y7 : bytes_at B memx (P' - 2) 2 OFF.
Hypothesis Y8 : bytes_at B memx G 8 0.
Hypothesis Y9 : bytes_at B memx (G + 8) 8 0.
Hypothesis Y10 : bytes_at B memx (G + 16) 8 RET.
Hypothesis Y11 : bytes_at B memx (G + 24) 4 0.
Hypothesis Y12 : bytes_at B memx (G + 28) 4 0.
Hypothesis Y13 : bytes_at B memx (G + 32) 8 (4064 + NEEDX).
Hypothesis Y14 : 0 < RSV' -> bytes_at B memx (P' + n) 1 0.
Hypothesis Y15 : 5 <= RSV' -> bytes_at B memx (END' - 4) 4 RSV' /\ bytes_at B memx (END' - 5) 1 0.
Hypothesis Y16 : bytes_at B memx END' 1 0.
Lemma nc_stride : stride_of amx = NEEDX - UNIT.
Proof.
clear - Hml. unfold stride_of. cbn [am_last am_maplen amx newam Z.eqb andb].
destruct (mlx =? 0) eqn:E; [apply Z.eqb_eq in E; lia | reflexivity].
Qed.
Lemma nc_slot0 : nth_slot amx 0 = resize_slot (NEEDX - UNIT) 0 (nth_slot am 0) OFF n.
Proof. reflexivity. Qed.
Lemma nc_slot_start : slot_start amx 0 = SP rx 16.
Proof. clear - Hml NEEDX amx. unfold slot_start. rewrite nc_stride. cbn. f_equal. unfold UNIT. lia. Qed.
Lemma cell_of_bytes l w v z :
loc_addr Lx l = z -> match v with VZ k => bytes_at B memx z w k | VP p => bytes_at B memx z w (loc_addr Lx (LMem p)) | _ => False end ->
cell_mem B Lx memx (MCell l w v).
Proof.
intros Hz Hb. unfold cell_mem. cbn [mc_loc mc_w mc_val]. rewrite Hz. destruct v; try exact Hb; destruct Hb.
Qed.
Lemma nc_group_cells : Forall (cell_mem B Lx memx) (group_cells g amx).
Proof.
unfold group_cells. cbn [am_mem am_maplen am_aidx am_last amx newam].
replace (mlx =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
change (zseq 0 (0 + 1)) with [0]. cbn [flat_map]. rewrite app_nil_r.
unfold slot_cells. rewrite nc_slot_start. rewrite nc_slot0. unfold resize_slot. cbn [ss_hdr ss_fr fr_off].
repeat apply Forall_cons; try apply Forall_nil.
- apply cell_of_bytes with (z := RET); [cbn; lia | exact Y1].
- apply cell_of_bytes with (z := RET + 8); [cbn; unfold RET; lia | exact Y2].
- apply cell_of_bytes with (z := RET + 12); [cbn; unfold RET; lia | exact Y3].
- assert (ERC : (if 5 <=? NEEDX - UNIT - IB - UNIT * OFF - n then 5 else NEEDX - UNIT - IB - UNIT * OFF - n) = RC').
{ unfold RC', RSV', UNIT, IB. replace (NEEDX - 16 - 4 - 16 * OFF - n) with (NEEDX - 20 - 16 * OFF - n) by lia. reflexivity. }
assert (EH3 : hdr_byte3 amx 0 {| fr_off := OFF; fr_n := n; fr_kind := FUser |} = 32 * RC').
{ unfold hdr_byte3. cbn [fr_kind]. unfold rsv_code. rewrite nc_stride. cbn [fr_off fr_n]. rewrite ERC. lia. }
assert (EH16 : hdr_off16 amx 0 {| fr_off := OFF; fr_n := n; fr_kind := FUser |} = OFF).
{ unfold hdr_off16. cbn [fr_off]. rewrite Z.mul_0_r. unfold UNIT. rewrite Z.div_0_l by lia. lia. }
destruct (Z.eqb_spec OFF 0) as [E0|E0].
+ rewrite ERC. cbn [app]. repeat apply Forall_cons; try apply Forall_nil.
* apply cell_of_bytes with (z := P' - 3); [cbn; unfold P', RET; lia |]. replace (0 + RC' * 32) with (32 * RC') by lia. exact Y6.
* apply cell_of_bytes with (z := P' - 2); [cbn; unfold P', RET; lia |].
rewrite Z.mul_0_r. unfold UNIT. rewrite Z.div_0_l by lia. rewrite <- E0. exact Y7.
+ rewrite Hhdr. cbn [app]. destruct (Y4 E0) as [Y4a Y4b]. repeat apply Forall_cons; try apply Forall_nil.
* apply cell_of_bytes with (z := RET + 13); [cbn; unfold RET; lia | exact Y4a].
* apply cell_of_bytes with (z := RET + 14); [cbn; unfold RET; lia | exact Y4b].
* apply cell_of_bytes with (z := P' - 4); [cbn; unfold P', RET, UNIT; lia | exact Y5].
* apply cell_of_bytes with (z := P' - 3); [cbn; unfold P', RET, UNIT; lia | rewrite EH3; exact Y6].
* apply cell_of_bytes with (z := P' - 2); [cbn; unfold P', RET, UNIT; lia | rewrite EH16; exact Y7].
Qed.
Lemma nc_meta_cells : Forall (cell_mem B Lx memx) (meta_slot_cells g (Some (MUsed amx))).
Proof.
unfold meta_slot_cells. cbn [am_prev am_next am_mem am_avail am_freed amx newam optr].
unfold META_prev, META_next, META_mem, META_avail, META_freed, META_bits.
assert (EB : meta_bits amx = 4064 + NEEDX) by (unfold meta_bits; cbn; unfold NEEDX; lia).
repeat apply Forall_cons; try apply Forall_nil.
- apply cell_of_bytes with (z := G); [rewrite loc_addr_padd; unfold G; lia | exact Y8].
- apply cell_of_bytes with (z := G + 8); [rewrite loc_addr_padd; unfold G; lia | exact Y9].
- apply cell_of_bytes with (z := G + 16); [rewrite loc_addr_padd; unfold G; lia | cbn [loc_addr]; rewrite Z.add_0_r; exact Y10].
- apply cell_of_bytes with (z := G + 24); [rewrite loc_addr_padd; unfold G; lia | exact Y11].
- apply cell_of_bytes with (z := G + 28); [rewrite loc_addr_padd; unfold G; lia | exact Y12].
- apply cell_of_bytes with (z := G + 32); [rewrite loc_addr_padd; unfold G; lia | rewrite EB; exact Y13].
Qed.
Lemma nc_tail_cells : Forall (cell_mem B Lx memx) (group_tail_cells amx).
Proof.
unfold group_tail_cells. cbn [am_last am_mem amx newam]. change (zseq 0 (0 + 1)) with [0]. cbn [flat_map]. rewrite app_nil_r.
assert (EXT : group_extent amx = NEEDX - 4) by (unfold group_extent; rewrite nc_stride; cbn [am_last amx newam]; unfold UNIT, IB; lia).
apply Forall_cons.
- apply cell_of_bytes with (z := END'); [cbn; rewrite EXT; unfold END', RET; lia | exact Y16].
- unfold frame_tail_cells. rewrite nc_slot0. unfold resize_slot. cbn [ss_fr fr_kind fr_n fr_off].
assert (ERSV : reserved_of amx {| fr_off := OFF; fr_n := n; fr_kind := FUser |} = RSV').
{ unfold reserved_of. rewrite nc_stride. cbn [fr_off fr_n]. unfold RSV', UNIT, IB. lia. }
rewrite ERSV.
assert (EFP : loc_addr Lx (LMem (frame_ptr amx 0 {| fr_off := OFF; fr_n := n; fr_kind := FUser |})) = P').
{ unfold frame_ptr. rewrite nc_slot_start. cbn. unfold P', RET, UNIT. lia. }
assert (ESE : loc_addr Lx (LMem (slot_end amx 0)) = END').
{ unfold slot_end. rewrite nc_slot_start, nc_stride. cbn. unfold END', RET, UNIT, IB. lia. }
apply Forall_app. split.
+ destruct (Z.ltb_spec 0 RSV'); [|apply Forall_nil]. apply Forall_cons; [|apply Forall_nil].
apply cell_of_bytes with (z := P' + n); [rewrite loc_addr_padd, EFP; lia | exact (Y14 ltac:(lia))].
+ destruct (Z.leb_spec 5 RSV'); [|apply Forall_nil]. destruct (Y15 ltac:(lia)) as [Y15a Y15b].
apply Forall_cons; [| apply Forall_cons; [|apply Forall_nil]].
* apply cell_of_bytes with (z := END' - 4); [rewrite loc_addr_padd, ESE; lia | exact Y15a].
* apply cell_of_bytes with (z := END' - 5); [rewrite loc_addr_padd, ESE; lia | exact Y15b].
Qed.
End u.
Definition live_sum (l : list YP0j.region) : Z :=
fold_right (fun rg0 acc => if rg_live rg0 then rg_len rg0 + acc else acc) 0 l.
Lemma live_sum_nonneg l :
(forall j x, nth_error l j = Some x -> 0 <= rg_len x) -> 0 <= live_sum l.
Proof.
induction l as [|y l IH]; intros NN; cbn; [lia|].
assert (IH' := IH ltac:(intros j z Hj; exact (NN (S j) z Hj))).
pose proof (NN 0%nat y eq_refl). unfold live_sum in IH'. destruct (rg_live y); lia.
Qed.
Lemma live_sum_ge1 l k x :
(forall j x, nth_error l j = Some x -> 0 <= rg_len x) ->
nth_error l k = Some x -> rg_live x = true -> rg_len x <= live_sum l.
Proof.
revert k. induction l as [|y l IH]; intros k NN Hk Hx; [destruct k; discriminate|].
assert (NN' : forall j z, nth_error l j = Some z -> 0 <= rg_len z) by (intros j z Hj; exact (NN (S j) z Hj)).
pose proof (live_sum_nonneg l NN') as SUM. unfold live_sum in *. cbn. destruct k as [|k].
- cbn in Hk. injection Hk as ->. rewrite Hx. lia.
- cbn in Hk. pose proof (IH k NN' Hk Hx). pose proof (NN 0%nat y eq_refl). destruct (rg_live y); lia.
Qed.
Lemma live_sum_ge2 l k1 k2 x1 x2 :
(forall j x, nth_error l j = Some x -> 0 <= rg_len x) ->
k1 <> k2 -> nth_error l k1 = Some x1 -> rg_live x1 = true -> nth_error l k2 = Some x2 -> rg_live x2 = true ->
rg_len x1 + rg_len x2 <= live_sum l.
Proof.
revert k1 k2. induction l as [|y l IH]; intros k1 k2 NN Hne H1 L1 H2 L2; [destruct k1; discriminate|].
assert (NN' : forall j z, nth_error l j = Some z -> 0 <= rg_len z) by (intros j z Hj; exact (NN (S j) z Hj)).
pose proof (live_sum_nonneg l NN') as SUM. pose proof (NN 0%nat y eq_refl) as Y0. unfold live_sum in *. cbn.
destruct k1 as [|k1]; destruct k2 as [|k2]; cbn in H1, H2; [congruence| | |].
- injection H1 as ->. rewrite L1. pose proof (live_sum_ge1 l k2 x2 NN' H2 L2). unfold live_sum in *. lia.
- injection H2 as ->. rewrite L2. pose proof (live_sum_ge1 l k1 x1 NN' H1 L1). unfold live_sum in *. lia.
- pose proof (IH k1 k2 NN' ltac:(lia) H1 L1 H2 L2). destruct (rg_live y); lia.
Qed.
Lemma ranges_disjoint_pointwise lo1 n1 lo2 n2 :
0 < n1 -> 0 < n2 ->
(forall x, lo1 <= x < lo1 + n1 -> ~ (lo2 <= x < lo2 + n2)) ->
ranges_disjoint (lo1, n1) (lo2, n2).
Proof.
intros H1 H2 H. unfold ranges_disjoint. cbn [fst snd].
destruct (Z_lt_le_dec lo1 (lo2 + n2)); [|lia]. destruct (Z_lt_le_dec lo2 (lo1 + n1)); [|lia].
exfalso. apply (H (Z.max lo1 lo2)); lia.
Qed.
Lemma same_views segs (m m' : word -> option byte) x : m' (Z_to_bv 64 x) = m (Z_to_bv 64 x) ->
mbyte segs m' x = mbyte segs m x /\ (writable_at segs m x <-> writable_at segs m' x).
Proof. intros E. unfold mbyte, writable_at, wview. rewrite E. tauto. Qed.
Lemma mbyte_of_present segs (m : word -> option byte) x b :
mbyte segs m x = Some b -> present m x -> m (Z_to_bv 64 x) = Some b.
Proof. intros Hb [b' Hb']. unfold mbyte in Hb. rewrite Hb' in Hb |- *. exact Hb. Qed.
Section RD.
Variable B : malloc_syms.
Variables (L : layout) (A : astate) (mem : word -> option byte) (md : Model).
Variables (g : sptr) (am : ameta) (fr : frame) (n : Z).
Hypothesis MX : MRx B L A mem md.
Hypothesis Hu : usedX [] A g am.
Hypothesis Hfr : ss_fr (nth_slot am 0) = Some fr.
Hypothesis H63 : am_sc am = 63.
Hypothesis Hbig : MMAP_THRESHOLD < fr_n fr.
Hypothesis Hn : fr_n fr + PGSZ <= n < 2 ^ 62.
Hypothesis Hin : In (frame_ptr am 0 fr, fr_n fr) (user_blocks A).
Definition r : nat := prid (am_mem am).
Definition MEM : Z := ly_reg L r.
Definition OLDLEN : Z := am_maplen am * 4096.
Definition NEEDED : Z := needed fr n.
Definition OFF : Z := fr_off fr.
Definition NOLD : Z := fr_n fr.
Definition G : Z := ptr_addr L g.
Definition P : Z := MEM + 16 + 16 * OFF.
Lemma M : MRc B L A mem md. Proof. exact (MRx_MRc _ _ _ _ _ MX). Qed.
Lemma HW : WF A. Proof. exact (mc_wf _ _ _ _ _ M). Qed.
Lemma LG : ledger_ok B L A md. Proof. exact (mc_ledger _ _ _ _ _ M). Qed.
Lemma LX : ledger_x L A md. Proof. exact (MRx_ledger_x _ _ _ _ _ MX). Qed.
Lemma HL : layout_ok L A. Proof. exact (mc_layout _ _ _ _ _ M). Qed.
Lemma Mg : MT A g = Some (MUsed am). Proof. exact (proj1 (usedX_MT _ _ _ _ Hu)). Qed.
Lemma ND : List.NoDup (keys A). Proof. exact (proj1 (inv_keys HW)). Qed.
Lemma Hing : In (g, am) (used_metas A). Proof. apply (used_metas_iff A g am ND). exact Mg. Qed.
Lemma shape :
am_last am = 0 /\ 1 <= am_maplen am /\ am_avail am = 0 /\ am_freed am = 0 /\ am_aidx am = 0 /\
am_prev am = None /\ am_next am = None /\ am_slots am = [nth_slot am 0] /\
stride_of am = OLDLEN - UNIT /\ fr_kind fr = FUser /\ am_mem am = SP r 0 /\
0 <= OFF <= 255 /\ 0 <= NOLD /\ 16 * OFF + NOLD + 20 <= OLDLEN.
Proof.
destruct (rm_shape U0 A g am 0 HW Hu H63) as (Hl & Hml & Hav & Hfd & Hai & Hp & Hnx & Hlen).
pose proof (inv_groups HW g am Hu) as (_ & _ & Gsl & Gcl & Gmp & _).
assert (Hst : stride_of am = OLDLEN - UNIT).
{ unfold stride_of, OLDLEN. rewrite Hl. cbn [Z.eqb andb]. destruct (am_maplen am =? 0) eqn:E; [apply Z.eqb_eq in E; lia | reflexivity]. }
pose proof (Gsl 0 ltac:(lia)) as (_ & _ & S3). rewrite Hfr in S3. destruct S3 as (_ & _ & (F1 & F2 & F3 & _) & _).
assert (Hk : fr_kind fr = FUser).
{ destruct Gcl as [(_ & _ & _ & _ & _ & [C6 | (fr0 & E0 & K0 & _)]) | (C & _)]; [discriminate | | lia].
rewrite Hfr in E0. injection E0 as <-. exact K0. }
destruct (Gmp ltac:(lia)) as (r0 & rg & Em & _).
assert (Er : am_mem am = SP r 0) by (unfold r; rewrite Em; reflexivity).
assert (Esl : am_slots am = [nth_slot am 0]).
{ unfold nth_slot. destruct (am_slots am) as [|x [|]]; cbn in Hlen; try lia. reflexivity. }
rewrite Hst in F3. unfold OFF, NOLD, UNIT, IB in *. repeat split; auto; lia.
Qed.
Lemma reg : exists rg, region_of A r = Some rg /\ rg_kind rg = RkMap /\ rg_live rg = true /\ rg_len rg = OLDLEN.
Proof.
pose proof (inv_groups HW g am Hu) as (_ & _ & _ & _ & Gmp & _). destruct shape as (_ & Hml & _).
destruct (Gmp ltac:(lia)) as (r0 & rg & Em & Hr & Hk & Hl & Hlen & _).
exists rg. unfold r. rewrite Em. cbn [prid]. unfold OLDLEN, PGSZ in *. repeat split; auto.
Qed.
Lemma hdr : exists h3 h16, ss_hdr (nth_slot am 0) = Some (h3, h16) /\ 0 <= h3 <= 255 /\ 0 <= h16 <= 65535 /\
(OFF = 0 -> h3 = 32 * rsv_code am fr /\ h16 = 0).
Proof.
pose proof (inv_groups HW g am Hu) as (_ & _ & Gsl & _ & _). destruct shape as (Hl & Hml & _).
pose proof (Gsl 0 ltac:(lia)) as (S1 & S2 & S3). rewrite Hfr in S3. destruct S3 as (_ & _ & _ & S4).
destruct (ss_hdr (nth_slot am 0)) as [[h3 h16]|] eqn:E; [| pose proof (S1 eq_refl); lia].
exists h3, h16. split; [reflexivity|]. destruct (S2 h3 h16 eq_refl) as [R1 R2]. split; [exact R1|]. split; [exact R2|].
intros E0. specialize (S4 E0). injection S4 as E3 E16.
unfold hdr_byte3 in E3. destruct shape as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hk & _). rewrite Hk in E3.
unfold hdr_off16 in E16. rewrite Z.mul_0_r in E16. unfold UNIT in E16. rewrite Z.div_0_l in E16 by lia.
unfold OFF in E0. lia.
Qed.
Lemma placed : MEM mod PGSZ = 0 /\ 4096 <= MEM /\ MEM + OLDLEN <= alloc_ceiling /\
(forall a, MEM <= a < MEM + OLDLEN -> ~ in_img B a) /\ 4096 <= OLDLEN.
Proof.
destruct reg as (rg & Hr & Hk & Hl & Hlen). destruct shape as (_ & Hml & _).
destruct (lg_placed _ _ _ _ LG r rg Hr Hl) as (P1 & P2 & P3 & P4). rewrite Hlen in *.
unfold MEM, OLDLEN in *. repeat split; auto. lia.
Qed.
Lemma needed_facts' : n + 16 * OFF + 20 <= NEEDED /\ NEEDED mod PGSZ = 0 /\ 0 < NEEDED < 2 ^ 63 /\ NEEDED < n + 16 * OFF + 20 + 4096.
Proof.
destruct shape as (Hl & _).
pose proof (needed_facts A g am fr n HW Hu Hfr Hl ltac:(unfold MMAP_THRESHOLD, PGSZ in *; lia) ltac:(lia)) as (N1 & N2 & N3).
unfold NEEDED, OFF, UNIT, IB in *. split; [lia|]. split; [exact N2|]. split; [exact N3|].
unfold needed, page_round, PGSZ, UNIT, IB. pose proof (Z_div_mod_eq_full (n + 16 * fr_off fr + 16 + 4 + 4096 - 1) 4096).
pose proof (Z.mod_pos_bound (n + 16 * fr_off fr + 16 + 4 + 4096 - 1) 4096 ltac:(lia)). lia.
Qed.
Lemma g_home : exists a k rr o rg, In a (st_areas A) /\ 0 <= k < METAS_PER_AREA /\ g = padd a (AREA_HDR + META_SIZE * k) /\
a = SP rr o /\ region_of A rr = Some rg /\ rg_live rg = true /\ rg_kind rg <> RkMap /\ PGSZ <= o /\ o + PGSZ <= rg_len rg /\
G = ly_reg L rr + o + AREA_HDR + META_SIZE * k /\ 4096 <= G /\ G + 40 <= alloc_ceiling /\
(forall x, G <= x < G + 40 -> ~ in_img B x).
Proof.
destruct (meta_in_area A g (MUsed am) HW (In_of_mlookup _ _ _ Mg)) as (a & k & Ha & Hk & Eg).
destruct (inv_areas HW) as (_ & Hareas & _). destruct (Hareas a Ha) as (rr & o & rg & Ea & Hom & Ho & Hr & Hl & Hsz & Hkind).
pose proof (lg_placed _ _ _ _ LG rr rg Hr Hl) as (Q1 & Q2 & Q3 & Q4).
assert (EG : G = ly_reg L rr + o + AREA_HDR + META_SIZE * k).
{ unfold G, ptr_addr. rewrite Eg, Ea. cbn. lia. }
exists a, k, rr, o, rg. unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *.
repeat split; auto; try lia.
- destruct (rg_kind rg); [discriminate | discriminate | destruct Hkind].
- intros x Hx. apply Q4. lia.
Qed.
Lemma old_cell c : In c (image A) -> cell_mem B L mem c.
Proof. intros Hc. exact (proj1 (Forall_forall _ _) (mc_cells _ _ _ _ _ M) c Hc). Qed.
Lemma group_cell_in_image c : In c (group_cells g am) -> In c (image A).
Proof. intros Hc. unfold image. rewrite !in_app_iff. right. right. apply in_flat_map. exists (g, am). split; [exact Hing | exact Hc]. Qed.
Lemma old_present x : MEM <= x < MEM + OLDLEN -> present mem x.
Proof.
intros Hx. destruct reg as (rg & Hr & Hk & Hl & Hlen).
pose proof (proj1 (Forall_forall _ _) (mc_foot _ _ _ _ _ M) _ (footprint_region_In A r rg Hr Hk Hl)) as F.
unfold foot_ok in F. cbn [fst snd loc_addr] in F. apply F. rewrite Hlen. unfold MEM in Hx. lia.
Qed.
Lemma Hmd0 : m_halted md = None /\ m_vm_lazy md = [] /\ m_vm_materialized md = [].
Proof. exact (mc_md _ _ _ _ _ M). Qed.
Lemma old_bytes : exists h3 h16, ss_hdr (nth_slot am 0) = Some (h3, h16) /\ (OFF = 0 -> h16 = 0) /\
bytes_at B mem MEM 8 G /\ bytes_at B mem (MEM + 8) 4 0 /\ bytes_at B mem (MEM + 12) 1 0 /\
(OFF <> 0 -> bytes_at B mem (MEM + 13) 1 h3 /\ bytes_at B mem (MEM + 14) 2 h16) /\
bytes_at B mem (P - 4) 1 0 /\ bytes_at B mem (P - 2) 2 OFF.
Proof.
destruct hdr as (h3 & h16 & Hh & R3 & R16 & H0). exists h3, h16. split; [exact Hh|]. split; [intros E; exact (proj2 (H0 E))|].
destruct shape as (Hl & Hml & Hav & Hfd & Hai & Hp & Hnx & Hsl & Hst & Hk & Em & Ho & _).
assert (ESS : loc_addr L (LMem (slot_start am 0)) = MEM + 16).
{ unfold slot_start. rewrite loc_addr_padd, Em. cbn [loc_addr]. unfold MEM, UNIT. lia. }
assert (EM0 : loc_addr L (LMem (am_mem am)) = MEM) by (rewrite Em; cbn; unfold MEM; lia).
assert (EH16 : hdr_off16 am 0 fr = OFF) by (unfold hdr_off16, OFF; rewrite Z.mul_0_r; unfold UNIT; rewrite Z.div_0_l by lia; lia).
pose proof (slot_start_cells A g am 0 HW Hing ltac:(rewrite Hl; lia)) as [S4 S3]. rewrite Hh in S3. destruct S3 as [S3 S2].
assert (G1 : In (MCell (LMem (am_mem am)) 8 (VP g)) (image A)).
{ apply group_cell_in_image. unfold group_cells. left. reflexivity. }
assert (G2 : In (MCell (LMem (padd (am_mem am) 8)) 4 (VZ (am_aidx am))) (image A)).
{ apply group_cell_in_image. unfold group_cells. right. left. replace (am_maplen am =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
pose proof (old_cell _ G1) as C1. pose proof (old_cell _ G2) as C2. pose proof (old_cell _ S4) as C3. pose proof (old_cell _ S3) as C4. pose proof (old_cell _ S2) as C5.
unfold cell_mem in C1, C2, C3, C4, C5. cbn [mc_loc mc_w mc_val sval_num] in C1, C2, C3, C4, C5.
rewrite EM0 in C1. rewrite loc_addr_padd, EM0, Hai in C2. rewrite loc_addr_padd, ESS in C3. rewrite loc_addr_padd, ESS in C4. rewrite loc_addr_padd, ESS in C5.
change (loc_addr L (LMem g)) with G in C1.
replace (MEM + 16 + -4) with (MEM + 12) in C3 by lia. replace (MEM + 16 + -3) with (MEM + 13) in C4 by lia. replace (MEM + 16 + -2) with (MEM + 14) in C5 by lia.
split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [intros _; split; [exact C4 | exact C5]|].
destruct (Z.eqb_spec OFF 0) as [E0|E0].
-
destruct (H0 E0) as [E3 E16]. subst h16. unfold P. rewrite E0. replace (MEM + 16 + 16 * 0 - 4) with (MEM + 12) by lia.
replace (MEM + 16 + 16 * 0 - 2) with (MEM + 14) by lia. split; [exact C3 | exact C5].
- assert (FC : forall c, In c [MCell (LMem (padd (padd (slot_start am 0) (UNIT * fr_off fr)) (-4))) 1 (VZ 0);
MCell (LMem (padd (padd (slot_start am 0) (UNIT * fr_off fr)) (-3))) 1 (VZ (hdr_byte3 am 0 fr));
MCell (LMem (padd (padd (slot_start am 0) (UNIT * fr_off fr)) (-2))) 2 (VZ (hdr_off16 am 0 fr))] -> In c (image A)).
{ intros c Hc. apply group_cell_in_image. apply (In_group_slot g am 0); [rewrite Hl; lia|]. unfold slot_cells. rewrite Hfr.
apply in_app_iff. right. apply in_app_iff. right. fold OFF. replace (OFF =? 0) with false by (symmetry; apply Z.eqb_neq; exact E0). exact Hc. }
pose proof (old_cell _ (FC _ ltac:(left; reflexivity))) as C6. pose proof (old_cell _ (FC _ ltac:(right; right; left; reflexivity))) as C8.
unfold cell_mem in C6, C8. cbn [mc_loc mc_w mc_val sval_num] in C6, C8. rewrite !loc_addr_padd, ESS in C6. rewrite !loc_addr_padd, ESS, EH16 in C8. fold OFF in C6. fold OFF in C8. unfold P, UNIT in *.
replace (MEM + 16 + 16 * OFF - 4) with (MEM + 16 + 16 * OFF + -4) by lia. replace (MEM + 16 + 16 * OFF - 2) with (MEM + 16 + 16 * OFF + -2) by lia.
split; [exact C6 | exact C8].
Qed.
Lemma map_byte_off_meta k rg x : region_of A k = Some rg -> rg_kind rg = RkMap -> rg_live rg = true ->
ly_reg L k <= x < ly_reg L k + rg_len rg -> ~ (G + 16 <= x < G + 40).
Proof.
intros Hr2 Hk2 Hl2 Hx GX.
destruct g_home as (a0 & k0 & rr & o & rg0 & _ & Hk0 & _ & _ & Hrr & Hlrr & Hkdrr & Ho & Hsz & EG & _).
assert (Hne2 : k <> rr) by (intros E; rewrite E in Hr2; rewrite Hrr in Hr2; injection Hr2 as <-; exact (Hkdrr Hk2)).
pose proof (reg_lo_le rg0) as RLO. assert (RL2 : reg_lo rg = 0) by (unfold reg_lo; rewrite Hk2; reflexivity).
pose proof (lx_regs _ _ _ LX k rr rg rg0 Hne2 Hr2 Hrr Hl2 Hlrr ltac:(rewrite RL2; lia) ltac:(unfold PGSZ in *; lia)) as D.
unfold ranges_disjoint in D. rewrite RL2 in D. cbn [fst snd] in D.
unfold METAS_PER_AREA, AREA_HDR, META_SIZE, PGSZ in *. clear - D GX EG Ho Hsz Hk0 Hx RLO. lia.
Qed.
Section OK.
Variable RET : Z.
Hypothesis Hne : OLDLEN <> NEEDED.
Hypothesis RETal : RET mod PGSZ = 0.
Hypothesis RETpos : 0 < RET.
Hypothesis RETce : RET + NEEDED <= alloc_ceiling.
Hypothesis DISJ : forall e, In e (vm_maps (m_vmmaps md)) -> e <> (w64 MEM, w64 OLDLEN) ->
ranges_disjoint (RET, NEEDED) (iv_lo e, iv_len e).
Hypothesis NIMG : forall x, RET <= x < RET + NEEDED -> ~ in_img B x.
Definition r' : nat := length (st_regions A).
Definition L' : layout := Layout (ly_ctx L) (fun k => if Nat.eqb k r' then RET else ly_reg L k) (ly_brk0 L) (ly_sec L).
Definition A' : astate := A_ok A g am fr n.
Definition am' : ameta := newam am fr n r' (NEEDED / 4096).
Definition vm' : VmMaps := mremap_maps_next (m_vmmaps md) (w64 MEM) (w64 RET) (w64 NEEDED).
Definition md' : Model := with_vmmaps vm' md.
Definition rgn : YP0j.region := mkRegion RkMap NEEDED [] true.
Lemma r_lt : (r < r')%nat.
Proof. destruct reg as (rg & Hr & _). exact (region_of_lt _ _ _ Hr). Qed.
Lemma ml' : NEEDED = NEEDED / 4096 * 4096 /\ 1 <= NEEDED / 4096.
Proof.
pose proof needed_facts' as (N1 & N2 & N3 & _). destruct shape as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ho & Hno & _).
unfold PGSZ in N2. pose proof (Z_div_mod_eq_full NEEDED 4096). lia.
Qed.
Lemma am_ok_eq : am_ok A am fr n = am'.
Proof.
pose proof needed_facts' as (N1 & N2 & N3 & _). destruct shape as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hk & _).
unfold am', newam, am_ok.
exact (rm_amR U0 A g am fr n NEEDED HW Hu H63).
Qed.
Lemma A'_fields :
st_metas A' = st_metas (upd_meta g (MUsed am') A) /\ st_areas A' = st_areas A /\ st_brk A' = st_brk A /\
st_regions A' = lupd (st_regions A ++ [rgn]) r (mkRegion RkMap (rg_len (nth r (st_regions A ++ [rgn]) (mkRegion RkMap 0 [] false))) [] false) /\
ctx_cells A' = ctx_cells A /\ st_meta_alloc_shift A' = st_meta_alloc_shift A /\
st_avail_meta_areas A' = st_avail_meta_areas A.
Proof.
unfold A', A_ok, A2, A1, YO30.r', YO30.rid. rewrite am_ok_eq. fold r. fold r'.
unfold upd_meta, set_regions. cbn. repeat split; reflexivity.
Qed.
Lemma region_of_A' k :
region_of A' k = if Nat.eqb k r then Some (mkRegion RkMap OLDLEN [] false)
else if Nat.eqb k r' then Some rgn else region_of A k.
Proof.
destruct A'_fields as (_ & _ & _ & ER & _). unfold region_of. rewrite ER, nth_error_lupd.
destruct reg as (rg & Hr & _ & _ & Hlen). pose proof r_lt as RL. unfold region_of in Hr.
rewrite length_app. cbn [length].
destruct (Nat.eqb_spec k r) as [->|Hk].
- replace (Nat.ltb r (length (st_regions A) + 1)) with true by (symmetry; apply Nat.ltb_lt; unfold r' in RL; lia). cbn [andb].
f_equal. f_equal. unfold r' in RL. rewrite app_nth1 by lia. rewrite (nth_error_nth _ _ _ Hr). exact Hlen.
- cbn [andb]. destruct (Nat.eqb_spec k r') as [->|Hk'].
+ unfold r'. rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity.
+ destruct (Nat.lt_ge_cases k r') as [Hlt|Hge].
* unfold r' in Hlt. rewrite nth_error_app1 by lia. reflexivity.
* unfold r' in Hge, Hk'. rewrite nth_error_app2 by lia. destruct (k - length (st_regions A))%nat as [|j] eqn:E; [lia|].
symmetry. destruct j; cbn; apply nth_error_None; lia.
Qed.
Lemma len_A' : length (st_regions A') = S r'.
Proof. destruct A'_fields as (_ & _ & _ & ER & _). rewrite ER, length_lupd, length_app. cbn. unfold r'. lia. Qed.
Lemma used_metas_A' : exists u1 u2, used_metas A = u1 ++ (g, am) :: u2 /\ used_metas A' = u1 ++ (g, am') :: u2.
Proof.
destruct (used_metas_upd A g am Mg) as (u1 & u2 & E1 & E2). exists u1, u2. split; [exact E1|].
rewrite <- (E2 am'). destruct A'_fields as (EM & _). unfold used_metas. rewrite EM. reflexivity.
Qed.
Lemma MT_A' q : MT A' q = if sptr_eqb q g then Some (MUsed am') else MT A q.
Proof. destruct A'_fields as (EM & _). unfold MT. rewrite EM. change (mlookup (st_metas (upd_meta g (MUsed am') A)) q) with (MT (upd_meta g (MUsed am') A) q). apply MT_upd. Qed.
Lemma keys_A' : keys A' = keys A.
Proof.
destruct A'_fields as (EM & _). unfold keys. rewrite EM. change (keys (upd_meta g (MUsed am') A) = keys A).
apply keys_upd_In. unfold keys. apply in_map_iff. exists (g, MUsed am). split; [reflexivity | exact (In_of_mlookup _ _ _ Mg)].
Qed.
Lemma yields_ok : yields (realloc (Some (frame_ptr am 0 fr)) n A) [(KMremap r OLDLEN NEEDED, 1)] (Some (p_ok A am fr n), A').
Proof.
destruct shape as (Hl & _).
pose proof (realloc_tree A g am fr n HW Hu Hfr H63 Hl ltac:(unfold MMAP_THRESHOLD, PGSZ in *; lia) ltac:(lia)) as T.
change (YO30.p am fr) with (frame_ptr am 0 fr) in T. rewrite T.
change (old_len am) with OLDLEN. change (needed fr n) with NEEDED. change (YO30.rid am) with r.
replace (OLDLEN =? NEEDED) with false by (symmetry; apply Z.eqb_neq; exact Hne).
cbn. repeat split; reflexivity.
Qed.
Lemma WF_A' : WF A'.
Proof.
exact (realloc_wf A _ NOLD n _ _ _ HW Hin ltac:(unfold NOLD, MMAP_THRESHOLD, PGSZ in *; lia) ltac:(lia) yields_ok).
Qed.
Definition oentry : loc * Z := (LMem (SP r 0), OLDLEN).
Definition nentry : loc * Z := (LMem (SP r' 0), NEEDED).
Lemma footprint_A'_split0 : exists l1 l2, footprint A = l1 ++ oentry :: l2 /\ footprint A' = l1 ++ l2 ++ [nentry].
Proof.
destruct reg as (rg & Hr & Hk & Hl & Hlen). pose proof r_lt as RL. destruct A'_fields as (_ & EA & _).
set (F := fun s k => match region_of s k with
| Some rg => match rg_kind rg with RkMap => if rg_live rg then [(LMem (SP k 0), rg_len rg)] else [] | _ => [] end
| None => [] end).
assert (EF : forall s, footprint s = (LCtx 0, CTX_SIZE) :: map (fun ar => (LMem ar, PGSZ)) (st_areas s) ++ flat_map (F s) (seq 0 (length (st_regions s)))) by reflexivity.
assert (ES : seq 0 r' = seq 0 r ++ r :: seq (S r) (r' - S r)).
{ replace r' with (r + S (r' - S r))%nat at 1 by lia. rewrite seq_app. reflexivity. }
assert (ES' : seq 0 (S r') = seq 0 r' ++ [r']) by (rewrite seq_S; reflexivity).
exists ((LCtx 0, CTX_SIZE) :: map (fun ar => (LMem ar, PGSZ)) (st_areas A) ++ flat_map (F A) (seq 0 r)),
(flat_map (F A) (seq (S r) (r' - S r))).
assert (FR : F A r = [oentry]) by (unfold F; rewrite Hr, Hk, Hl, Hlen; reflexivity).
split.
- rewrite (EF A). fold r'. rewrite ES, flat_map_app. change (flat_map (F A) (r :: ?sq)) with (F A r ++ flat_map (F A) sq).
rewrite FR. cbn [app]. rewrite <- app_assoc. reflexivity.
- rewrite (EF A'), EA, len_A', ES', ES, !flat_map_app.
change (flat_map (F A') (r :: ?sq)) with (F A' r ++ flat_map (F A') sq).
assert (E1 : forall k, k <> r -> k <> r' -> F A' k = F A k) by (intros k H1 H2; unfold F; rewrite region_of_A';
replace (Nat.eqb k r) with false by (symmetry; apply Nat.eqb_neq; exact H1); replace (Nat.eqb k r') with false by (symmetry; apply Nat.eqb_neq; exact H2); reflexivity).
rewrite (flat_map_ext_in (F A') (F A) (seq 0 r)) by (intros k Hk'; apply in_seq in Hk'; apply E1; lia).
rewrite (flat_map_ext_in (F A') (F A) (seq (S r) _)) by (intros k Hk'; apply in_seq in Hk'; apply E1; lia).
replace (F A' r) with (@nil (loc * Z)) by (unfold F; rewrite region_of_A', Nat.eqb_refl; reflexivity).
replace (flat_map (F A') [r']) with [nentry]
by (cbn [flat_map]; unfold F; rewrite region_of_A', Nat.eqb_refl; replace (Nat.eqb r' r) with false by (symmetry; apply Nat.eqb_neq; lia); cbn; reflexivity).
cbn [app]. rewrite <- !app_assoc. reflexivity.
Qed.
Lemma footprint_A'_split : exists l1 l2, footprint A = l1 ++ oentry :: l2 /\ footprint A' = l1 ++ l2 ++ [nentry] /\
(forall e, In e (l1 ++ l2) -> In e (footprint A) /\ e <> oentry).
Proof.
destruct footprint_A'_split0 as (l1 & l2 & E1 & E2). exists l1, l2. split; [exact E1|]. split; [exact E2|].
assert (ND1 : ~ In oentry (l1 ++ l2)).
{ intros Hi. pose proof (proj1 (proj2 (proj2 HL))) as PD. rewrite E1, map_app in PD. cbn [map] in PD.
assert (D : ranges_disjoint (crange L oentry) (crange L oentry)).
{ apply in_app_iff in Hi as [Hi|Hi].
- apply pairwise_app_inv in PD as (_ & _ & X). apply X; [apply in_map; exact Hi | left; reflexivity].
- apply pairwise_app_inv in PD as (_ & [X _] & _). apply X. apply in_map. exact Hi. }
unfold ranges_disjoint, crange, oentry in D. cbn [fst snd] in D. pose proof placed as (_ & _ & _ & _ & P5). lia. }
intros e He. split.
- rewrite E1. apply in_app_iff in He as [He|He]; apply in_app_iff; [left | right; right]; exact He.
- intros ->. exact (ND1 He).
Qed.
Lemma In_footprint_A' e : In e (footprint A') <-> (In e (footprint A) /\ e <> oentry) \/ e = nentry.
Proof.
destruct footprint_A'_split as (l1 & l2 & E1 & E2 & OLD). rewrite E2. split.
- intros H. rewrite app_assoc in H. apply in_app_iff in H as [H|[H|[]]]; [left; exact (OLD e H) | right; symmetry; exact H].
- intros [[H Hne']| ->].
+ rewrite app_assoc. apply in_app_iff. left. rewrite E1 in H. apply in_app_iff in H as [H|[H|H]]; [apply in_app_iff; left; exact H | exfalso; exact (Hne' (eq_sym H)) | apply in_app_iff; right; exact H].
+ apply in_app_iff. right. apply in_app_iff. right. left. reflexivity.
Qed.
Lemma oentry_in : In oentry (footprint A).
Proof. destruct reg as (rg & Hr & Hk & Hl & Hlen). unfold oentry. rewrite <- Hlen. apply footprint_region_In; assumption. Qed.
Lemma layout_le_L' : layout_le A L L'.
Proof.
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. intros k Hk. unfold L'. cbn.
destruct (Nat.eqb_spec k r'); [unfold r' in *; lia | reflexivity].
Qed.
Lemma L'_old k : (k < r')%nat -> ly_reg L' k = ly_reg L k.
Proof. intros Hk. unfold L'. cbn. destruct (Nat.eqb_spec k r'); [lia | reflexivity]. Qed.
Lemma L'_new : ly_reg L' r' = RET.
Proof. unfold L'. cbn. rewrite Nat.eqb_refl. reflexivity. Qed.
Lemma loc_addr_L' l : (match l with LMem p => (prid p < r')%nat | LCtx _ => True end) -> loc_addr L' l = loc_addr L l.
Proof. intros H. destruct l as [o|[k o]]; cbn; [reflexivity|]. cbn in H. destruct (Nat.eqb_spec k r'); [lia | reflexivity]. Qed.
Lemma ptrs_below_A : ptrs_below A.
Proof. exact (WF_ptrs_below A HW (MRx_ama _ _ _ _ _ MX)). Qed.
Lemma crange_L'_old e : In e (footprint A) -> crange L' e = crange L e.
Proof.
intros He. unfold crange. f_equal. apply loc_addr_L'.
destruct (In_footprint_inv A e He) as [-> | [(ar & Har & ->) | (k & rr & Hr & Hk & Hl & ->)]]; cbn [fst]; [exact I| |].
- destruct (inv_areas HW) as (_ & Hareas & _). destruct (Hareas ar Har) as (k & o & rr & -> & _ & _ & Hr & _). cbn. exact (region_of_lt _ _ _ Hr).
- cbn. exact (region_of_lt _ _ _ Hr).
Qed.
Lemma old_entry_clear e x : In e (footprint A) -> e <> oentry ->
loc_addr L (fst e) <= x < loc_addr L (fst e) + snd e ->
~ (MEM <= x < MEM + OLDLEN) /\ ~ (RET <= x < RET + NEEDED) /\ 4096 <= x < alloc_ceiling.
Proof.
intros He Hneo Hx. pose proof (footprint_low B L A mem md e x M He Hx) as LOW.
assert (D0 : ranges_disjoint (crange L e) (crange L oentry)).
{ pose proof (proj1 (proj2 (proj2 HL))) as PD.
destruct (pairwise_map_In ranges_disjoint (crange L) (footprint A) e oentry PD He oentry_in Hneo) as [D|D]; [exact D | apply ranges_disjoint_sym; exact D]. }
assert (D1 : ~ (MEM <= x < MEM + OLDLEN)).
{ unfold ranges_disjoint, crange, oentry in D0; cbn [fst snd loc_addr] in D0. unfold MEM. intros X. lia. }
split; [exact D1|]. split; [|exact LOW]. intros X.
destruct (In_footprint_inv A e He) as [-> | [(ar & Har & ->) | (k & rr & Hr & Hk & Hl & ->)]]; cbn [fst snd loc_addr] in Hx.
-   apply (NIMG x X). apply (so_ctx_img _ (mc_syms _ _ _ _ _ M)). rewrite (mc_ctx _ _ _ _ _ M) in Hx. lia.
-
destruct (inv_areas HW) as (_ & Hareas & _). destruct (Hareas ar Har) as (k & o & rr & -> & Hom & Ho & Hr & Hl & Hsz & _). cbn [loc_addr] in Hx.
pose proof (reg_lo_le rr) as RLO.
destruct (lx_cov _ _ _ LX k rr x Hr Hl ltac:(unfold PGSZ in *; lia)) as (e' & He' & Hxe').
assert (HneX : e' <> (w64 MEM, w64 OLDLEN)).
{ intros ->. unfold iv_lo, iv_len, w64 in Hxe'. cbn [fst snd] in Hxe'. pose proof placed as (_ & P2 & P3 & _ & P5). pose proof alloc_ceiling_lt.
rewrite !Z_to_bv_unsigned, !bv_wrap_small in Hxe' by (change (bv_modulus 64) with (2 ^ 64); lia). exact (D1 Hxe'). }
pose proof (DISJ e' He' HneX) as D. unfold ranges_disjoint in D. cbn [fst snd] in D. clear - D Hxe' X Hx Ho RLO Hsz. lia.
-
assert (Hkr : k <> r) by (intros ->; apply Hneo; unfold oentry; destruct reg as (rg & Hr2 & _ & _ & Hlen2); rewrite Hr in Hr2; injection Hr2 as <-; rewrite Hlen2; reflexivity).
pose proof (lg_maps _ _ _ _ LG k rr Hr Hl ltac:(rewrite Hk; discriminate)) as He'.
destruct (lg_placed _ _ _ _ LG k rr Hr Hl) as (_ & Q2 & Q3 & _). pose proof alloc_ceiling_lt.
pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (inv_areas HW)))))))) k rr Hr) as LEN0.
assert (HneX : (w64 (ly_reg L k), w64 (rg_len rr)) <> (w64 MEM, w64 OLDLEN)).
{ intros E. apply (f_equal fst) in E. cbn [fst] in E. apply (f_equal bv_unsigned) in E. rename E into E1. unfold w64 in E1. pose proof placed as (_ & P2 & P3 & _ & P5).
rewrite !Z_to_bv_unsigned, !bv_wrap_small in E1 by (change (bv_modulus 64) with (2 ^ 64); lia).
unfold ranges_disjoint, crange, oentry in D0; cbn [fst snd loc_addr] in D0. unfold MEM in *. lia. }
pose proof (DISJ _ He' HneX) as D. unfold ranges_disjoint, iv_lo, iv_len, w64 in D. cbn [fst snd] in D.
rewrite !Z_to_bv_unsigned, !bv_wrap_small in D by (change (bv_modulus 64) with (2 ^ 64); lia). lia.
Qed.
Lemma Hmd : m_halted md = None /\ m_vm_lazy md = [] /\ m_vm_materialized md = [].
Proof. exact (mc_md _ _ _ _ _ M). Qed.
Lemma EMEM : bv_unsigned (w64 MEM) = MEM.
Proof. pose proof placed as (_ & P2 & P3 & _ & P5). pose proof alloc_ceiling_lt. unfold w64. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. Qed.
Lemma EOLD : bv_unsigned (w64 OLDLEN) = OLDLEN.
Proof. pose proof placed as (_ & P2 & P3 & _ & P5). pose proof alloc_ceiling_lt. unfold w64. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. Qed.
Lemma ERET : bv_unsigned (w64 RET) = RET.
Proof. pose proof needed_facts' as (_ & _ & N3 & _). pose proof alloc_ceiling_lt. unfold w64. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. Qed.
Lemma ENEED : bv_unsigned (w64 NEEDED) = NEEDED.
Proof. pose proof needed_facts' as (_ & _ & N3 & _). pose proof alloc_ceiling_lt. unfold w64. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. Qed.
Lemma vm'_facts :
vm_maps (m_vmmaps md') = (w64 RET, w64 NEEDED) :: map_remove (vm_maps (m_vmmaps md)) (w64 MEM) /\
vm_noaccess (m_vmmaps md') = vm_noaccess (m_vmmaps md) /\
vm_reserved (m_vmmaps md') = vm_reserved (m_vmmaps md) /\
vm_limit (m_vmmaps md') = vm_limit (m_vmmaps md) /\
vm_start_brk (m_vmmaps md') = vm_start_brk (m_vmmaps md) /\
vm_brk (m_vmmaps md') = vm_brk (m_vmmaps md) /\
m_halted md' = m_halted md /\ m_vm_lazy md' = [] /\ m_vm_materialized md' = [].
Proof.
destruct Hmd as (H1 & H2 & H3). unfold md', vm', mremap_maps_next, with_vmmaps. cbn. rewrite H2, H3. repeat split; reflexivity.
Qed.
Lemma old_entry_in : In (w64 MEM, w64 OLDLEN) (vm_maps (m_vmmaps md)).
Proof. destruct reg as (rg & Hr & Hk & Hl & Hlen). unfold MEM. rewrite <- Hlen. apply (lg_maps _ _ _ _ LG r rg Hr Hl). rewrite Hk. discriminate. Qed.
Lemma len_nonneg k rg : region_of A k = Some rg -> 0 <= rg_len rg.
Proof. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (inv_areas HW)))))))) k rg). Qed.
Lemma other_region k rg : k <> r -> region_of A k = Some rg -> rg_live rg = true -> reg_lo rg < rg_len rg ->
(ly_reg L k + rg_len rg <= MEM \/ MEM + OLDLEN <= ly_reg L k + reg_lo rg) /\
(rg_kind rg <> RkBrk -> w64 (ly_reg L k) <> w64 MEM /\ ranges_disjoint (RET, NEEDED) (ly_reg L k, rg_len rg)).
Proof.
intros Hk Hrk Hlk Hlo. destruct reg as (rg0 & Hr & Hk0 & Hl0 & Hlen). pose proof placed as (_ & P2 & P3 & _ & P5).
pose proof (lx_regs _ _ _ LX k r rg rg0 Hk Hrk Hr Hlk Hl0 Hlo ltac:(unfold reg_lo; rewrite Hk0; lia)) as D.
unfold reg_lo in D at 3 4. rewrite Hk0 in D. unfold ranges_disjoint in D. cbn [fst snd] in D. rewrite Hlen in D. fold MEM in D.
pose proof (reg_lo_le rg) as RLO.
assert (D' : ly_reg L k + rg_len rg <= MEM \/ MEM + OLDLEN <= ly_reg L k + reg_lo rg) by lia.
split; [exact D'|]. intros Hnb.
destruct (lg_placed _ _ _ _ LG k rg Hrk Hlk) as (_ & Q2 & Q3 & _). pose proof alloc_ceiling_lt.
assert (NB : w64 (ly_reg L k) <> w64 MEM).
{ intros E. apply (f_equal bv_unsigned) in E. rewrite EMEM in E. unfold w64 in E.
rewrite Z_to_bv_unsigned, bv_wrap_small in E by (change (bv_modulus 64) with (2 ^ 64); lia).
unfold reg_lo in *. destruct (rg_kind rg); try lia. exact (Hnb eq_refl). }
split; [exact NB|].
pose proof (lg_maps _ _ _ _ LG k rg Hrk Hlk Hnb) as He.
assert (HneE : (w64 (ly_reg L k), w64 (rg_len rg)) <> (w64 MEM, w64 OLDLEN)) by (intros E; apply NB; exact (f_equal fst E)).
pose proof (DISJ _ He HneE) as DD. unfold ranges_disjoint, iv_lo, iv_len, w64 in DD |- *. cbn [fst snd] in DD |- *.
pose proof (len_nonneg k rg Hrk).
rewrite !Z_to_bv_unsigned, !bv_wrap_small in DD by (change (bv_modulus 64) with (2 ^ 64); lia). exact DD.
Qed.
Lemma nslots_A' : nslots A' = nslots A.
Proof.
destruct A'_fields as (_ & _ & _ & ER & _). destruct reg as (rg & Hr & Hk & Hl & Hlen). pose proof r_lt as RL. unfold r' in RL.
assert (E1 : nslots A' = fold_right (fun rg0 acc => region_slots rg0 + acc) 0 (st_regions A ++ [rgn]) - 1).
{ unfold nslots. apply (nslots_kill_lists (st_regions A ++ [rgn]) (st_regions A') r rg).
- rewrite nth_error_app1 by lia. exact Hr.
- exact Hl. - exact Hk.
- intros k. rewrite ER, nth_error_lupd, length_app. cbn [length].
destruct (Nat.eqb_spec k r); [|reflexivity]. subst k.
replace (Nat.ltb r (length (st_regions A) + 1)) with true by (symmetry; apply Nat.ltb_lt; lia). cbn [andb].
rewrite app_nth1 by lia. rewrite (nth_error_nth _ _ _ Hr). reflexivity. }
rewrite E1. unfold nslots. clear.
enough (EE : forall l z, fold_right (fun rg0 acc => region_slots rg0 + acc) z l = fold_right (fun rg0 acc => region_slots rg0 + acc) 0 l + z).
{ rewrite fold_right_app, EE. cbn. lia. }
induction l as [|x l IH]; intros z; cbn; [lia|]. rewrite IH. lia.
Qed.
Lemma live_bytes_A' : live_bytes A' = live_bytes A - OLDLEN + NEEDED.
Proof.
destruct reg as (rg & Hr & Hk & Hl & Hlen). pose proof r_lt as RL. unfold r' in RL.
set (A1 := set_regions (st_regions A ++ [rgn]) A).
assert (E1 : live_bytes A' = live_bytes A1 - rg_len rg).
{ apply (live_bytes_kill A1 A' r rg).
- unfold region_of, A1. cbn. rewrite nth_error_app1 by lia. exact Hr.
- exact Hl.
- intros k. rewrite region_of_A'. unfold region_of, A1. cbn. destruct (Nat.eqb_spec k r); [rewrite Hlen; reflexivity|].
destruct (Nat.eqb_spec k r').
+ subst k. unfold r'. rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity.
+ destruct (Nat.lt_ge_cases k r') as [Hlt|Hge]; unfold r' in *.
* rewrite nth_error_app1 by lia. reflexivity.
* rewrite nth_error_app2 by lia. rewrite (proj2 (nth_error_None (st_regions A) k)) by lia.
symmetry. apply nth_error_None. cbn. lia. }
rewrite E1, Hlen. unfold live_bytes, A1. cbn. rewrite fold_right_app. cbn.
enough (EE : forall l z, fold_right (fun rg0 acc => if rg_live rg0 then rg_len rg0 + acc else acc) z l =
fold_right (fun rg0 acc => if rg_live rg0 then rg_len rg0 + acc else acc) 0 l + z) by (rewrite EE; lia).
induction l as [|x l IH]; intros z; cbn; [lia|]. rewrite IH. destruct (rg_live x); lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma ledger_ok_A' : ledger_ok B L' A' md'.
Proof.
pose proof vm'_facts as (VM & VN & VR & VL & VS & VB & _). destruct A'_fields as (_ & _ & EB & _).
pose proof placed as (P1 & P2 & P3 & P4 & P5). pose proof needed_facts' as (N1 & N2 & N3 & _). pose proof old_entry_in as EIN.
pose proof r_lt as RL. pose proof alloc_ceiling_lt as ACL.
assert (OTHER : forall k rg, region_of A' k = Some rg -> rg_live rg = true -> k <> r' ->
k <> r /\ region_of A k = Some rg /\ (k < r')%nat /\ ly_reg L' k = ly_reg L k).
{ intros k rg Hk Hl Hk'. rewrite region_of_A' in Hk. destruct (Nat.eqb_spec k r); [injection Hk as <-; discriminate|].
destruct (Nat.eqb_spec k r'); [lia|]. pose proof (region_of_lt _ _ _ Hk). split; [exact n0|]. split; [exact Hk|]. split; [exact H|]. apply L'_old. exact H. }
split.
- rewrite VR. apply LG.
- rewrite VL. apply LG.
- intros k rg Hk Hl Hnb. rewrite VM. destruct (Nat.eq_dec k r') as [->|Hk'].
+ rewrite region_of_A', Nat.eqb_refl in Hk. replace (Nat.eqb r' r) with false in Hk by (symmetry; apply Nat.eqb_neq; lia).
injection Hk as <-. cbn [rg_len rgn]. rewrite L'_new. left. reflexivity.
+ destruct (OTHER k rg Hk Hl Hk') as (Hkr & HkA & Hlt & ->). right. apply In_map_remove. split; [exact (lg_maps _ _ _ _ LG k rg HkA Hl Hnb)|].
cbn [fst]. pose proof (reg_lo_le rg).
destruct (Z_lt_le_dec (reg_lo rg) (rg_len rg)) as [Hlo|Hlo].
* exact (proj1 (proj2 (other_region k rg Hkr HkA Hl Hlo) Hnb)).
*
intros E. pose proof (lg_maps _ _ _ _ LG k rg HkA Hl Hnb) as He. destruct (lx_maps _ _ _ LX _ He) as [LEN _].
unfold iv_len, w64 in LEN. cbn [snd] in LEN. destruct (lg_placed _ _ _ _ LG k rg HkA Hl) as (_ & Q2 & Q3 & _). pose proof (len_nonneg k rg HkA).
rewrite Z_to_bv_unsigned, bv_wrap_small in LEN by (change (bv_modulus 64) with (2 ^ 64); lia).
destruct (lx_disj _ _ _ LX _ _ He EIN) as [EE|DD].
-- apply (f_equal snd) in EE. cbn [snd] in EE. apply (f_equal bv_unsigned) in EE. rewrite EOLD in EE. unfold w64 in EE.
rewrite Z_to_bv_unsigned, bv_wrap_small in EE by (change (bv_modulus 64) with (2 ^ 64); lia).
unfold reg_lo in Hlo. destruct (rg_kind rg); try lia.
exact (Hnb eq_refl).
-- unfold ranges_disjoint, iv_lo, iv_len in DD. cbn [fst snd] in DD. rewrite E, EMEM, EOLD in DD. unfold w64 in DD.
rewrite Z_to_bv_unsigned, bv_wrap_small in DD by (change (bv_modulus 64) with (2 ^ 64); lia).
apply (f_equal bv_unsigned) in E. rewrite EMEM in E. unfold w64 in E. rewrite Z_to_bv_unsigned, bv_wrap_small in E by (change (bv_modulus 64) with (2 ^ 64); lia). lia.
- intros k rg off Hk Hl Hres Ho1 Ho2 Ho3 Hnrw.
assert (Hk' : k <> r') by (intros ->; rewrite region_of_A', Nat.eqb_refl in Hk; replace (Nat.eqb r' r) with false in Hk by (symmetry; apply Nat.eqb_neq; lia); injection Hk as <-; discriminate).
destruct (OTHER k rg Hk Hl Hk') as (Hkr & HkA & Hlt & EL). rewrite EL, VN, VM.
destruct (lg_noaccess _ _ _ _ LG k rg off HkA Hl Hres Ho1 Ho2 Ho3 Hnrw) as [Q1 Q2]. split; [exact Q1|].
apply map_contains_cons. unfold map_contains in Q2 |- *. apply existsb_exists in Q2 as (e & He & Pe). apply existsb_exists.
exists e. split; [|exact Pe]. apply In_map_remove. split; [exact He|].
apply andb_prop in Pe as [Pe1 Pe2]. apply Z.leb_le in Pe1. apply Z.leb_le in Pe2.
destruct (lg_placed _ _ _ _ LG k rg HkA Hl) as (_ & Q3 & Q4 & _).
assert (Eo : bv_unsigned (w64 (ly_reg L k + off)) = ly_reg L k + off).
{ clear - Q3 Q4 Ho1 Ho2 ACL. unfold w64. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). unfold PGSZ in *. lia. }
assert (Ep : bv_unsigned (w64 PGSZ) = PGSZ) by reflexivity. rewrite Eo, Ep in *.
destruct (other_region k rg Hkr HkA Hl ltac:(unfold reg_lo; rewrite Hres; unfold PGSZ in *; lia)) as [D _]. unfold reg_lo in D. rewrite Hres in D.
intros Efst. destruct (lx_disj _ _ _ LX e _ He EIN) as [-> | DD].
+ cbn [fst snd] in Pe1, Pe2. rewrite EMEM, EOLD in *. unfold PGSZ in *. lia.
+ unfold ranges_disjoint, iv_lo, iv_len in DD. cbn [fst snd] in DD. rewrite Efst, EMEM, EOLD in DD.
destruct (lx_maps _ _ _ LX e He) as [Pe _]. unfold iv_len, iv_lo in *. rewrite Efst, EMEM in *. unfold PGSZ in *. lia.
- rewrite VS. unfold L'. cbn [ly_brk0]. apply LG.
- rewrite EB, VB. unfold L'. cbn [ly_brk0 ly_reg]. pose proof (lg_brk _ _ _ _ LG) as HB.
destruct (st_brk A) as [| |rb pg] eqn:Ebrk; try exact HB.
pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (inv_areas HW)))))))) as BR. rewrite Ebrk in BR. destruct BR as (_ & rgb & Hrb & _).
pose proof (region_of_lt _ _ _ Hrb). destruct (Nat.eqb_spec rb r'); [unfold r' in *; lia | exact HB].
- intros k rg Hk Hl. destruct (Nat.eq_dec k r') as [->|Hk'].
+ rewrite region_of_A', Nat.eqb_refl in Hk. replace (Nat.eqb r' r) with false in Hk by (symmetry; apply Nat.eqb_neq; lia).
injection Hk as <-. cbn [rg_len rgn]. rewrite L'_new. unfold PGSZ in *.
assert (HR4096 : 4096 <= RET).
{ pose proof (Z.div_mod RET 4096 ltac:(lia)) as DM. rewrite RETal in DM. set (q := RET / 4096) in DM. clearbody q. clear -DM RETpos. lia. }
repeat split; try lia. exact NIMG.
+ destruct (OTHER k rg Hk Hl Hk') as (Hkr & HkA & Hlt & ->). exact (lg_placed _ _ _ _ LG k rg HkA Hl).
- rewrite VM, nslots_A'. cbn [length]. pose proof (lg_count _ _ _ _ LG). pose proof (length_map_remove_lt _ (w64 MEM) _ EIN eq_refl). lia.
- rewrite VM, live_bytes_A'. destruct reg as (rg & Hr & Hk & Hl & Hlen).
assert (NN : forall j x, nth_error (st_regions A) j = Some x -> 0 <= rg_len x) by (intros j x Hj; exact (len_nonneg j x Hj)).
pose proof (live_sum_ge1 (st_regions A) r rg NN Hr Hl) as LE. rewrite Hlen in LE. change (live_sum (st_regions A)) with (live_bytes A) in LE.
apply Forall_cons.
+ cbn [snd]. rewrite ENEED. lia.
+ apply Forall_forall. intros e He. apply In_map_remove in He as [He Hfe].
destruct (lx_in _ _ _ LX e He) as (k & rg' & Hk' & Hl' & G1 & G2).
destruct (Nat.eq_dec k r) as [->|Hkr].
* rewrite Hr in Hk'. injection Hk' as <-. exfalso.
destruct (lx_disj _ _ _ LX e _ He EIN) as [-> | DD]; [apply Hfe; reflexivity|].
unfold ranges_disjoint, iv_lo, iv_len in DD. cbn [fst snd] in DD. rewrite EMEM, EOLD in DD.
destruct (lx_maps _ _ _ LX e He) as [Pe _]. unfold iv_lo, iv_len in *. fold MEM in G1, G2. lia.
*
pose proof (live_sum_ge2 (st_regions A) k r rg' rg NN Hkr Hk' Hl' Hr Hl) as LE2. rewrite Hlen in LE2.
change (live_sum (st_regions A)) with (live_bytes A) in LE2.
unfold iv_lo, iv_len in *. lia.
- pose proof vm'_facts as (_ & _ & _ & _ & _ & _ & _ & VLZ & VMT).
unfold vm_backing_used. rewrite VLZ, VMT. cbn [length Z.of_nat maps_subtract_all Z.mul]. rewrite Z.add_0_r.
unfold vm_backed_maps. rewrite VM.
pose proof (live_bytes_maps_subtract_all (vm_noaccess (m_vmmaps md')) ((w64 RET, w64 NEEDED) :: map_remove (vm_maps (m_vmmaps md)) (w64 MEM))) as X1.
cbn [State.live_bytes] in X1. rewrite ENEED in X1.
pose proof (live_bytes_map_remove _ _ _ EIN) as LR. rewrite EOLD in LR.
pose proof (lx_lb _ _ _ LX). rewrite live_bytes_A'. lia.
-   exact (lg_ceil _ _ _ _ LG).
Qed.
Lemma ledger_x_A' : ledger_x L' A' md'.
Proof.
pose proof vm'_facts as (VM & VN & VR & VL & VS & VB & _).
pose proof placed as (P1 & P2 & P3 & P4 & P5). pose proof needed_facts' as (N1 & N2 & N3 & _). pose proof old_entry_in as EIN.
pose proof r_lt as RL. pose proof alloc_ceiling_lt as ACL. pose proof EMEM as EM. pose proof EOLD as EO. pose proof ERET as ER. pose proof ENEED as EN.
assert (OTHER : forall k rg, region_of A' k = Some rg -> rg_live rg = true -> k <> r' ->
k <> r /\ region_of A k = Some rg /\ (k < r')%nat /\ ly_reg L' k = ly_reg L k).
{ intros k rg Hk Hl Hk'. rewrite region_of_A' in Hk. destruct (Nat.eqb_spec k r); [injection Hk as <-; discriminate|].
destruct (Nat.eqb_spec k r'); [lia|]. pose proof (region_of_lt _ _ _ Hk). split; [exact n0|]. split; [exact Hk|]. split; [exact H|]. apply L'_old. exact H. }
assert (NEWR : forall rg, region_of A' r' = Some rg -> rg = rgn).
{ intros rg Hk. rewrite region_of_A', Nat.eqb_refl in Hk. replace (Nat.eqb r' r) with false in Hk by (symmetry; apply Nat.eqb_neq; lia). injection Hk as <-. reflexivity. }
assert (KEEP : forall e x, In e (vm_maps (m_vmmaps md)) -> iv_lo e <= x < iv_lo e + iv_len e -> ~ (MEM <= x < MEM + OLDLEN) ->
fst e <> w64 MEM /\ ~ (RET <= x < RET + NEEDED)).
{ intros e x He Hx Hnx.
assert (HneE : e <> (w64 MEM, w64 OLDLEN)).
{ intros ->. unfold iv_lo, iv_len in Hx. cbn [fst snd] in Hx. rewrite EM, EO in Hx. exact (Hnx Hx). }
split.
- intros Ef. destruct (lx_disj _ _ _ LX e _ He EIN) as [EE|DD]; [exact (HneE EE)|].
destruct (lx_maps _ _ _ LX e He) as [Le _]. destruct (lx_maps _ _ _ LX _ EIN) as [Lo _].
unfold ranges_disjoint, iv_lo, iv_len in DD, Le, Lo, Hx. cbn [fst snd] in DD, Le, Lo. rewrite Ef, EM, EO in *. clear - DD Le Lo P5. lia.
- pose proof (DISJ e He HneE) as D. unfold ranges_disjoint in D. cbn [fst snd] in D. clear - D Hx N3. intros X. lia. }
assert (OUT : forall k rg x, k <> r -> region_of A k = Some rg -> rg_live rg = true ->
ly_reg L k + reg_lo rg <= x < ly_reg L k + rg_len rg -> ~ (MEM <= x < MEM + OLDLEN)).
{ intros k rg x Hk Hrk Hlk Hx. destruct (other_region k rg Hk Hrk Hlk ltac:(lia)) as [D _]. clear - D Hx. lia. }
split.
-   intros k rg x Hk Hl Hx. rewrite VM. destruct (Nat.eq_dec k r') as [->|Hk'].
+ pose proof (NEWR rg Hk) as ->. exists (w64 RET, w64 NEEDED). split; [left; reflexivity|].
unfold iv_lo, iv_len. cbn [fst snd]. rewrite ER, EN. rewrite L'_new in Hx. unfold reg_lo in Hx. cbn in Hx. lia.
+ destruct (OTHER k rg Hk Hl Hk') as (Hkr & HkA & Hlt & EL). rewrite EL in Hx.
destruct (lx_cov _ _ _ LX k rg x HkA Hl Hx) as (e & He & Hxe).
destruct (KEEP e x He Hxe (OUT k rg x Hkr HkA Hl Hx)) as [Hfe _].
exists e. split; [right; apply In_map_remove; auto | exact Hxe].
-   intros e He. rewrite VM in He. destruct He as [<-|He].
+ unfold iv_lo, iv_len. cbn [fst snd]. rewrite ER, EN. lia.
+ apply In_map_remove in He as [He _]. exact (lx_maps _ _ _ LX e He).
-   intros e1 e2 H1 H2. rewrite VM in H1, H2.
assert (NEWD : forall e, In e (map_remove (vm_maps (m_vmmaps md)) (w64 MEM)) ->
ranges_disjoint (iv_lo (w64 RET, w64 NEEDED), iv_len (w64 RET, w64 NEEDED)) (iv_lo e, iv_len e)).
{ intros e He. apply In_map_remove in He as [He Hfe]. unfold iv_lo at 1. unfold iv_len at 1. cbn [fst snd]. rewrite ER, EN.
apply DISJ; [exact He|]. intros ->. apply Hfe. reflexivity. }
destruct H1 as [<-|H1]; destruct H2 as [<-|H2].
+ left. reflexivity.
+ right. apply NEWD. exact H2.
+ right. apply ranges_disjoint_sym. apply NEWD. exact H1.
+ apply In_map_remove in H1 as [H1 _]. apply In_map_remove in H2 as [H2 _]. exact (lx_disj _ _ _ LX e1 e2 H1 H2).
-   intros k1 k2 rg1 rg2 Hne12 Hk1 Hk2 Hl1 Hl2 Hlo1 Hlo2.
assert (NEWvs : forall k rg, k <> r' -> region_of A' k = Some rg -> rg_live rg = true -> reg_lo rg < rg_len rg ->
ranges_disjoint (ly_reg L' r' + reg_lo rgn, rg_len rgn - reg_lo rgn) (ly_reg L' k + reg_lo rg, rg_len rg - reg_lo rg)).
{ intros k rg Hk' Hk Hl Hlo. destruct (OTHER k rg Hk Hl Hk') as (Hkr & HkA & Hlt & EL). rewrite EL, L'_new.
unfold reg_lo at 1 2. cbn [rg_kind rg_len rgn]. rewrite Z.add_0_r, Z.sub_0_r.
apply ranges_disjoint_pointwise; [lia | lia |]. intros x Hx Hx2.
destruct (lx_cov _ _ _ LX k rg x HkA Hl ltac:(lia)) as (e & He & Hxe).
exact (proj2 (KEEP e x He Hxe (OUT k rg x Hkr HkA Hl ltac:(lia))) Hx). }
destruct (Nat.eq_dec k1 r') as [->|Hk1']; [|destruct (Nat.eq_dec k2 r') as [->|Hk2']].
+ pose proof (NEWR rg1 Hk1) as ->. apply NEWvs; auto.
+ pose proof (NEWR rg2 Hk2) as ->. apply ranges_disjoint_sym. apply NEWvs; auto.
+ destruct (OTHER k1 rg1 Hk1 Hl1 Hk1') as (_ & Hk1A & _ & ->). destruct (OTHER k2 rg2 Hk2 Hl2 Hk2') as (_ & Hk2A & _ & ->).
exact (lx_regs _ _ _ LX k1 k2 rg1 rg2 Hne12 Hk1A Hk2A Hl1 Hl2 Hlo1 Hlo2).
-   intros e He. rewrite VM in He. destruct He as [<-|He].
+ exists r', rgn. rewrite region_of_A', Nat.eqb_refl. replace (Nat.eqb r' r) with false by (symmetry; apply Nat.eqb_neq; lia).
split; [reflexivity|]. split; [reflexivity|]. rewrite L'_new. unfold iv_lo, iv_len. cbn [fst snd rg_len rgn]. rewrite ER, EN. lia.
+ apply In_map_remove in He as [He Hfe]. destruct (lx_in _ _ _ LX e He) as (k & rg & Hk & Hl & G1 & G2).
destruct (Nat.eq_dec k r) as [->|Hkr].
* exfalso. destruct reg as (rg0 & Hr & _ & _ & Hlen). rewrite Hr in Hk. injection Hk as <-. rewrite Hlen in G2. fold MEM in G1, G2.
destruct (lx_maps _ _ _ LX e He) as [Le _].
destruct (lx_disj _ _ _ LX e _ He EIN) as [EE|DD]; [apply Hfe; rewrite EE; reflexivity|].
unfold ranges_disjoint, iv_lo, iv_len in DD, Le, G1, G2. cbn [fst snd] in DD. rewrite EM, EO in DD. clear - DD Le G1 G2 P5. lia.
* pose proof (region_of_lt _ _ _ Hk) as Hlt. exists k, rg. rewrite region_of_A'.
replace (Nat.eqb k r) with false by (symmetry; apply Nat.eqb_neq; exact Hkr).
replace (Nat.eqb k r') with false by (symmetry; apply Nat.eqb_neq; unfold r'; lia).
split; [exact Hk|]. split; [exact Hl|]. rewrite L'_old by (unfold r'; exact Hlt). auto.
-   rewrite VM, live_bytes_A'. cbn [State.live_bytes]. rewrite EN.
pose proof (live_bytes_map_remove _ _ _ EIN) as LR. rewrite EO in LR. pose proof (lx_lb _ _ _ LX). lia.
-   intros e He. rewrite VN in He. destruct (lx_noacc _ _ _ LX e He) as (E & HE & S1 & S2 & HD).
destruct reg as (rg0 & Hr & Hk0 & Hl0 & Hlen).
pose proof (HD r rg0 Hr Hl0 Hk0 ltac:(lia)) as Dr. rewrite Hlen in Dr. fold MEM in Dr.
destruct (lx_maps _ _ _ LX E HE) as [LE _].
assert (HfE : fst E <> w64 MEM).
{ intros Ef. unfold ranges_disjoint, iv_lo, iv_len in Dr, LE. cbn [fst snd] in Dr. rewrite Ef, EM in *. clear - Dr LE P5. lia. }
exists E. rewrite VM. split; [right; apply In_map_remove; auto|]. split; [exact S1|]. split; [exact S2|].
intros k rg Hk Hl Hkd Hlen'. destruct (Nat.eq_dec k r') as [->|Hk'].
+ pose proof (NEWR rg Hk) as ->. rewrite L'_new. cbn [rg_len rgn]. apply ranges_disjoint_sym.
pose proof (DISJ E HE ltac:(intros ->; apply HfE; reflexivity)) as D. exact D.
+ destruct (OTHER k rg Hk Hl Hk') as (Hkr & HkA & Hlt & ->). exact (HD k rg HkA Hl Hkd Hlen').
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma footprint_pos' e : In e (footprint A) -> 0 < snd e.
Proof. exact (footprint_pos B L A mem md 0 MX e). Qed.
Lemma layout_ok_A' : layout_ok L' A'.
Proof.
pose proof HL as (Y1 & Y2 & Y3 & Y4). pose proof needed_facts' as (N1 & N2 & N3 & _). pose proof alloc_ceiling_lt as ACL.
destruct footprint_A'_split as (l1 & l2 & E1 & E2 & OLD).
split; [exact Y1|]. split; [|split].
- intros k rg Hk Hl. destruct (Nat.eq_dec k r') as [->|Hk'].
+ rewrite L'_new. exact RETal.
+ rewrite region_of_A' in Hk. destruct (Nat.eqb_spec k r); [injection Hk as <-; discriminate|].
destruct (Nat.eqb_spec k r'); [lia|]. rewrite (L'_old k (region_of_lt _ _ _ Hk)). exact (Y2 k rg Hk Hl).
- rewrite E2, app_assoc, map_app. apply pairwise_app.
+ rewrite E1, map_app in Y3. cbn [map] in Y3. apply pairwise_remove in Y3. rewrite <- map_app in Y3.
erewrite map_ext_in; [exact Y3|]. intros e He. apply crange_L'_old. exact (proj1 (OLD e He)).
+ cbn. split; [intros ? []| exact I].
+ intros x y Hx Hy. destruct Hy as [<-|[]]. apply in_map_iff in Hx as (e & <- & He). destruct (OLD e He) as [HeA Hne'].
rewrite (crange_L'_old e HeA). unfold crange at 2. unfold nentry. cbn [fst snd loc_addr]. rewrite L'_new, Z.add_0_r.
unfold crange. apply ranges_disjoint_pointwise; [exact (footprint_pos' e HeA) | lia |].
intros z Hz. exact (proj1 (proj2 (old_entry_clear e z HeA Hne' Hz))).
- intros e He. apply In_footprint_A' in He as [[HeA Hne']| ->].
+ rewrite (crange_L'_old e HeA). exact (Y4 e HeA).
+ unfold crange, nentry. cbn [fst snd loc_addr]. rewrite L'_new. lia.
Qed.
Lemma tail_geom_A' : tail_geom L' A'.
Proof. exact (tail_geom_of_WF A' L' WF_A' layout_ok_A'). Qed.
Lemma bounded_A' : bounded A'.
Proof.
destruct A'_fields as (_ & EA & _ & _ & _ & ESH & _). pose proof (mc_bounded _ _ _ _ _ M) as (_ & B2 & B3).
apply (bounded_of_WF A' WF_A'); rewrite ?EA, ?ESH; assumption.
Qed.
Lemma span_ok_A' : span_ok A'.
Proof.
destruct A'_fields as (EM & _). destruct shape as (Hl & _ & _ & _ & Hai & _).
apply (span_ok_same_metas (upd_meta g (MUsed am') A)); [| exact EM].
apply (span_ok_upd_same3 A g am); [exact (MRx_span _ _ _ _ _ MX) | exact Mg | | |]; unfold am', newam; cbn; symmetry; assumption || exact (eq_sym H63).
Qed.
Lemma ama_ok_A' : ama_ok A'.
Proof.
destruct A'_fields as (_ & EA & _ & _ & _ & _ & EAV). intros Hne'. rewrite EAV, len_A'. rewrite EA in Hne'.
pose proof (MRx_ama _ _ _ _ _ MX Hne'). unfold r'. lia.
Qed.
Lemma rsv_ok_A' : rsv_ok A'.
Proof.
intros q a i f Hf Hkf. pose proof needed_facts' as (N1 & N2 & N3 & N4). destruct ml' as [E1 E2].
unfold frames in Hf. apply in_flat_map in Hf as ([q' a'] & Hqa & Hf).
destruct used_metas_A' as (u1 & u2 & U1 & U2). rewrite U2 in Hqa.
assert (CASE : (q', a') = (g, am') \/ In (q', a') (used_metas A)).
{ apply in_app_iff in Hqa as [H|[H|H]]; [right | left; symmetry; exact H | right]; rewrite U1; apply in_app_iff; [left | right; right]; exact H. }
destruct CASE as [E | Hold].
- injection E as -> ->. apply in_flat_map in Hf as (j & Hj & Hf).
change (am_last am') with 0 in Hj. change (zseq 0 (0 + 1)) with [0] in Hj. destruct Hj as [<-|[]].
unfold am' in Hf. rewrite (nc_slot0 am fr n r' (NEEDED / 4096)) in Hf. unfold resize_slot in Hf. cbn [ss_fr In] in Hf. destruct Hf as [E|[]]. injection E as <- <- <- <-.
unfold reserved_of. rewrite (nc_stride am fr n r' (NEEDED / 4096) E2). cbn [fr_off fr_n]. unfold UNIT, IB. fold OFF. rewrite <- E1. lia.
- apply (MRx_rsv _ _ _ _ _ MX q a i f); [| exact Hkf]. unfold frames. apply in_flat_map. exists (q', a'). auto.
Qed.
Section b0.
Variable mem' : word -> option byte.
Variable SCR : Z -> Prop.
Hypothesis SCR_hi : forall x, SCR x -> alloc_ceiling <= x \/ (in_img B x /\ ~ static_owned B x /\ ~ (ms_ctx B <= x < ms_ctx B + CTX_SIZE)).
Definition P' : Z := RET + 16 + 16 * OFF.
Definition END' : Z := RET + NEEDED - 4.
Definition RSV' : Z := NEEDED - 20 - 16 * OFF - n.
Definition RC' : Z := if 5 <=? RSV' then 5 else RSV'.
Hypothesis COPY : forall i, 0 <= i < 16 + 16 * OFF + NOLD -> i <> 16 * OFF + 13 -> mem' (w64 (RET + i)) = mem (w64 (MEM + i)).
Hypothesis Wp3 : bytes_at B mem' (P' - 3) 1 (32 * RC').
Hypothesis Wg16 : bytes_at B mem' (G + 16) 8 RET.
Hypothesis Wg24 : bytes_at B mem' (G + 24) 4 0.
Hypothesis Wg28 : bytes_at B mem' (G + 28) 4 0.
Hypothesis Wg32 : bytes_at B mem' (G + 32) 8 (4064 + NEEDED).
Hypothesis Wend : bytes_at B mem' END' 1 0.
Hypothesis Wpn : 0 < RSV' -> bytes_at B mem' (P' + n) 1 0.
Hypothesis We45 : 5 <= RSV' -> bytes_at B mem' (END' - 4) 4 RSV' /\ bytes_at B mem' (END' - 5) 1 0.
Hypothesis PRES : forall x, RET <= x < RET + NEEDED -> present mem' x.
Hypothesis FRAME : forall x, 0 <= x < 2 ^ 64 -> ~ (RET <= x < RET + NEEDED) -> ~ (MEM <= x < MEM + OLDLEN) ->
~ (G + 16 <= x < G + 40) -> ~ SCR x -> mem' (w64 x) = mem (w64 x).
Lemma copied i w v :
bytes_at B mem (MEM + i) w v -> 0 <= i -> i + Z.of_nat w <= 16 + 16 * OFF + NOLD ->
(i + Z.of_nat w <= 16 * OFF + 13 \/ 16 * OFF + 13 < i) ->
bytes_at B mem' (RET + i) w v.
Proof.
intros Hb Hi Hw Hskip k Hk. destruct shape as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ho & Hno & Hfit).
specialize (Hb k Hk). pose proof (old_present (MEM + i + Z.of_nat k) ltac:(lia)) as PR.
pose proof (mbyte_of_present _ _ _ _ Hb PR) as RAW.
unfold mbyte. replace (RET + i + Z.of_nat k) with (RET + (i + Z.of_nat k)) by lia. unfold w64 in COPY.
rewrite (COPY (i + Z.of_nat k)) by lia. replace (MEM + (i + Z.of_nat k)) with (MEM + i + Z.of_nat k) by lia. rewrite RAW. reflexivity.
Qed.
Lemma kept x : (exists e, In e (footprint A) /\ e <> oentry /\ loc_addr L (fst e) <= x < loc_addr L (fst e) + snd e) ->
~ (G + 16 <= x < G + 40) -> mem' (w64 x) = mem (w64 x).
Proof.
intros (e & He & Hne' & Hx) HG. destruct (old_entry_clear e x He Hne' Hx) as (X1 & X2 & X3). pose proof alloc_ceiling_lt.
apply FRAME; [lia | exact X2 | exact X1 | exact HG |].
intros HS. destruct (SCR_hi x HS) as [Hhi | (Himg & Hns & Hnc)]; [lia|].
destruct (In_footprint_inv A e He) as [-> | [(ar & Har & ->) | (k & rr & Hr & Hk & Hl & ->)]]; cbn [fst snd loc_addr] in Hx.
- apply Hnc. rewrite <- (mc_ctx _ _ _ _ _ M). lia.
- destruct (inv_areas HW) as (_ & Hareas & _). destruct (Hareas ar Har) as (k & o & rr & -> & Hom & Ho & Hr & Hl & Hsz & _). cbn [loc_addr] in Hx.
apply (proj2 (proj2 (proj2 (lg_placed _ _ _ _ LG k rr Hr Hl))) x); [unfold PGSZ in *; lia | exact Himg].
- apply (proj2 (proj2 (proj2 (lg_placed _ _ _ _ LG k rr Hr Hl))) x); [lia | exact Himg].
Qed.
Lemma G_home : exists e, In e (footprint A) /\ e <> oentry /\ loc_addr L (fst e) <= G /\ G + 40 <= loc_addr L (fst e) + snd e.
Proof.
destruct g_home as (a & k & rr & o & rg & Ha & Hk & Eg & Ea & Hr & Hl & Hkd & Ho & Hsz & EG & _).
exists (LMem a, PGSZ). split; [right; apply in_app_iff; left; apply in_map_iff; exists a; auto|].
split; [unfold oentry; rewrite Ea; intros X; injection X as _ Xo; unfold PGSZ in *; lia|].
rewrite Ea. cbn [fst snd loc_addr]. unfold METAS_PER_AREA, AREA_HDR, META_SIZE, PGSZ in *. lia.
Qed.
Lemma G_L' : loc_addr L' (LMem g) = G.
Proof.
destruct g_home as (a & k & rr & o & rg & Ha & Hk & Eg & Ea & Hr & _). apply loc_addr_L'. rewrite Eg, Ea. cbn. exact (region_of_lt _ _ _ Hr).
Qed.
Lemma new_cells :
Forall (cell_mem B L' mem') (group_cells g am') /\ Forall (cell_mem B L' mem') (meta_slot_cells g (Some (MUsed am'))) /\
Forall (cell_mem B L' mem') (group_tail_cells am').
Proof.
destruct old_bytes as (h3 & h16 & Hh & H16 & O1 & O2 & O3 & O45 & O6 & O8). destruct ml' as [E1 E2].
destruct shape as (_ & _ & _ & _ & _ & Hp & Hnx & _ & _ & _ & _ & Ho & Hno & Hfit). pose proof needed_facts' as (N1 & _).
destruct g_home as (a & k & rr & o & rg & Ha & Hk & Eg & Ea & Hr & _ & _ & _ & _ & EG & _).
pose proof G_L' as GL.
assert (Y1 : bytes_at B mem' (ly_reg L' r') 8 (loc_addr L' (LMem g))).
{ rewrite L'_new, GL. replace RET with (RET + 0) by lia. apply (copied 0 8%nat G); [rewrite Z.add_0_r; exact O1 | lia | cbn; lia | cbn; lia]. }
assert (C : forall i w v, bytes_at B mem (MEM + i) w v -> 0 <= i -> i + Z.of_nat w <= 16 + 16 * OFF + NOLD ->
(i + Z.of_nat w <= 16 * OFF + 13 \/ 16 * OFF + 13 < i) -> bytes_at B mem' (ly_reg L' r' + i) w v).
{ intros. rewrite L'_new. apply copied; assumption. }
assert (EP : ly_reg L' r' + 16 + 16 * fr_off fr = P') by (rewrite L'_new; reflexivity). fold OFF in EP.
assert (A3 : bytes_at B mem' (P' - 3) 1 (32 * (if 5 <=? NEEDED / 4096 * 4096 - 20 - 16 * fr_off fr - n then 5 else NEEDED / 4096 * 4096 - 20 - 16 * fr_off fr - n))).
{ rewrite <- E1. exact Wp3. }
unfold OFF, NOLD in *.
split; [|split].
- apply (nc_group_cells B L' mem' g am fr n r' (NEEDED / 4096) h3 h16 Hh E2 H16 Y1).
+ apply (C 8 4%nat 0 O2); cbn; lia.
+ apply (C 12 1%nat 0 O3); cbn; lia.
+ intros Hoff. destruct (O45 Hoff) as [O4 O5]. split; [apply (C 13 1%nat h3 O4) | apply (C 14 2%nat h16 O5)]; cbn; lia.
+ replace (ly_reg L' r' + 16 + 16 * fr_off fr - 4) with (ly_reg L' r' + (16 + 16 * fr_off fr - 4)) by lia.
apply (C (16 + 16 * fr_off fr - 4) 1%nat 0); [| lia | cbn; lia | cbn; lia]. unfold P, OFF in O6. replace (MEM + (16 + 16 * fr_off fr - 4)) with (MEM + 16 + 16 * fr_off fr - 4) by lia. exact O6.
+ rewrite EP. exact A3.
+ replace (ly_reg L' r' + 16 + 16 * fr_off fr - 2) with (ly_reg L' r' + (16 + 16 * fr_off fr - 2)) by lia.
apply (C (16 + 16 * fr_off fr - 2) 2%nat (fr_off fr)); [| lia | cbn; lia | cbn; lia]. unfold P, OFF in O8. replace (MEM + (16 + 16 * fr_off fr - 2)) with (MEM + 16 + 16 * fr_off fr - 2) by lia. exact O8.
-
destruct G_home as (eG & HeG & HneG & G1 & G2).
assert (OLDM : forall c, In c (meta_slot_cells g (Some (MUsed am))) -> cell_mem B L mem c).
{ intros c Hc. apply old_cell. exact (meta_cells_in_image A g am c HW Hu Hc). }
unfold meta_slot_cells in OLDM. rewrite Hp, Hnx in OLDM. cbn [optr] in OLDM.
assert (K : forall i, 0 <= i < 16 -> mem' (w64 (G + i)) = mem (w64 (G + i))).
{ intros i Hi. apply kept; [exists eG; split; [exact HeG|]; split; [exact HneG|]; lia | lia]. }
apply (nc_meta_cells B L' mem' g am fr n r' (NEEDED / 4096)); rewrite ?GL, ?L'_new.
+ pose proof (OLDM _ ltac:(left; reflexivity)) as C0. unfold cell_mem in C0. cbn [mc_loc mc_w mc_val sval_num] in C0. rewrite loc_addr_padd in C0.
change (loc_addr L (LMem g)) with G in C0. unfold META_prev in C0. intros j Hj. rewrite <- (C0 j Hj).
replace (G + 0 + Z.of_nat j) with (G + Z.of_nat j) by lia. replace (G + Z.of_nat j) with (G + Z.of_nat j) by lia.
exact (proj1 (same_views (ms_segs B) mem mem' (G + Z.of_nat j) (K (Z.of_nat j) ltac:(lia)))).
+ pose proof (OLDM _ ltac:(right; left; reflexivity)) as C0. unfold cell_mem in C0. cbn [mc_loc mc_w mc_val sval_num] in C0. rewrite loc_addr_padd in C0.
change (loc_addr L (LMem g)) with G in C0. unfold META_next in C0. intros j Hj. rewrite <- (C0 j Hj).
replace (G + 8 + Z.of_nat j) with (G + (8 + Z.of_nat j)) by lia.
exact (proj1 (same_views (ms_segs B) mem mem' (G + (8 + Z.of_nat j)) (K (8 + Z.of_nat j) ltac:(lia)))).
+ exact Wg16.
+ exact Wg24.
+ exact Wg28.
+ rewrite <- E1. exact Wg32.
- apply (nc_tail_cells B L' mem' g am fr n r' (NEEDED / 4096) E2); rewrite ?L'_new, <- ?E1; fold OFF P' END' RSV'.
+ exact Wp3.
+ intros H. apply Wpn. exact H.
+ intros H. replace (RET + NEEDED - 4) with END' by reflexivity. apply We45. exact H.
+ exact Wend.
Qed.
Hypothesis PRESG : forall x, G + 16 <= x < G + 40 -> present mem' x.
Lemma cell_mem_L' m c : refs_below r' c -> cell_mem B L m c -> cell_mem B L' m c.
Proof.
intros [H1 H2] H. unfold cell_mem in *. destruct c as [l w v]; cbn [mc_loc mc_w mc_val] in *.
rewrite (loc_addr_L' l H1). destruct v as [z|q|z|]; try exact H.
cbn [sval_num] in *. rewrite (loc_addr_L' (LMem q) H2). exact H.
Qed.
Lemma areas_cells_metas_eq s s' l : st_metas s' = st_metas s -> areas_cells s' l = areas_cells s l.
Proof. intros E. induction l as [|a t IH]; cbn; [reflexivity|]. rewrite IH. unfold area_cells. rewrite E. reflexivity. Qed.
Lemma tail_cell_prid a2 c : In c (group_tail_cells a2) -> exists q, mc_loc c = LMem q /\ prid q = prid (am_mem a2).
Proof.
intros Hc. unfold group_tail_cells in Hc. destruct Hc as [<-|Hc]; [eexists; split; [reflexivity | apply prid_padd]|].
apply in_flat_map in Hc as (i & _ & Hc). unfold frame_tail_cells in Hc.
destruct (ss_fr (nth_slot a2 i)) as [f|]; [|destruct Hc]. destruct (fr_kind f); [|destruct Hc].
apply in_app_iff in Hc as [Hc|Hc].
- destruct (0 <? reserved_of a2 f); [|destruct Hc]. destruct Hc as [<-|[]].
eexists; split; [reflexivity|]. unfold frame_ptr, slot_start. rewrite !prid_padd. reflexivity.
- destruct (5 <=? reserved_of a2 f); [|destruct Hc]. destruct Hc as [<-|[<-|[]]]; (eexists; split; [reflexivity|]); unfold slot_end, slot_start; rewrite !prid_padd; reflexivity.
Qed.
Definition NEW : list mcell := group_cells g am' ++ meta_slot_cells g (Some (MUsed am')).
Lemma NEW_in_image c : In c NEW -> In c (image A').
Proof.
intros Hc. unfold NEW in Hc. apply in_app_iff in Hc as [Hc|Hc].
- apply (In_image_group A' g am'); [| exact Hc]. destruct used_metas_A' as (u1 & u2 & _ & ->). apply in_app_iff. right. left. reflexivity.
- apply (meta_cells_in_image A' g am' c WF_A'); [| exact Hc]. apply usedX_intro; [reflexivity|]. rewrite MT_A', sptr_eqb_refl. reflexivity.
Qed.
Lemma not_new_off_meta c j : In c (image A') -> ~ In c NEW -> (j < mc_w c)%nat ->
~ (G + 16 <= loc_addr L' (mc_loc c) + Z.of_nat j < G + 40).
Proof.
intros Hc HnN Hj Hx. pose proof (image_cells_disjoint A' L' WF_A' layout_ok_A') as PD. pose proof G_L' as GL.
assert (K : forall c', In c' (meta_slot_cells g (Some (MUsed am'))) -> ranges_disjoint (cell_range L' c) (cell_range L' c')).
{ intros c' Hc'. assert (Hc'N : In c' NEW) by (unfold NEW; apply in_app_iff; right; exact Hc').
destruct (pairwise_map_In ranges_disjoint (cell_range L') (image A') c c' PD Hc (NEW_in_image c' Hc'N) ltac:(intros ->; exact (HnN Hc'N))) as [D|D];
[exact D | apply ranges_disjoint_sym; exact D]. }
unfold meta_slot_cells in K. unfold META_prev, META_next, META_mem, META_avail, META_freed, META_bits in K.
pose proof (K _ ltac:(do 3 right; left; reflexivity)) as D3.
pose proof (K _ ltac:(do 4 right; left; reflexivity)) as D4. pose proof (K _ ltac:(do 5 right; left; reflexivity)) as D5.
pose proof (K _ ltac:(do 2 right; left; reflexivity)) as D2'.
unfold ranges_disjoint, cell_range in D2', D3, D4, D5. cbn [fst snd mc_loc mc_w] in D2', D3, D4, D5.
rewrite loc_addr_padd, GL in D2', D3, D4, D5. clear - D2' D3 D4 D5 Hj Hx. lia.
Qed.
Lemma memrep_A' : memrep B L' A' mem'.
Proof.
destruct new_cells as (NC1 & NC2 & NC3). destruct used_metas_A' as (u1 & u2 & U1 & U2).
pose proof ptrs_below_A as PB. destruct A'_fields as (EM & EA & _ & _ & ECTX & _).
assert (NDK : ~ In g (map fst (u1 ++ u2))).
{ pose proof (NoDup_used_metas_keys A ND) as NDu. rewrite U1, map_app in NDu. cbn [map fst] in NDu. apply NoDup_remove_2 in NDu. rewrite map_app. exact NDu. }
assert (OLDU : forall q a, In (q, a) (u1 ++ u2) -> In (q, a) (used_metas A) /\ q <> g).
{ intros q a Hqa. split; [rewrite U1; apply in_app_iff in Hqa as [?|?]; apply in_app_iff; [left | right; right]; assumption|].
intros ->. apply NDK. apply in_map_iff. exists (g, a). auto. }
assert (KEEPC : forall c e, (In c (image A) \/ In c (tail_cells A)) -> cell_mem B L mem c -> In e (footprint A) -> e <> oentry ->
range_incl (cell_range L c) (crange L e) ->
(forall j, (j < mc_w c)%nat -> ~ (G + 16 <= loc_addr L (mc_loc c) + Z.of_nat j < G + 40)) ->
cell_mem B L' mem' c).
{ intros c e Hc Hcm He Hne' Hincl Hoff. apply cell_mem_L'; [exact (PB c Hc)|].
apply (cell_keep B L mem mem' c Hcm). intros j Hj. apply kept; [| exact (Hoff j Hj)].
exists e. split; [exact He|]. split; [exact Hne'|]. unfold range_incl, cell_range, crange in Hincl. cbn [fst snd] in Hincl. lia. }
split; [|split].
-   apply Forall_forall. intros c Hc.
destruct (In_dec mcell_eq_dec c NEW) as [HN|HN].
{ unfold NEW in HN. apply in_app_iff in HN as [HN|HN]; [exact (proj1 (Forall_forall _ _) NC1 c HN) | exact (proj1 (Forall_forall _ _) NC2 c HN)]. }
pose proof (fun j Hj => not_new_off_meta c j Hc HN Hj) as OFFM.
assert (LOC : forall j, refs_below r' c -> loc_addr L' (mc_loc c) + Z.of_nat j = loc_addr L (mc_loc c) + Z.of_nat j).
{ intros j [H1 _]. rewrite (loc_addr_L' _ H1). reflexivity. }
unfold image in Hc. apply in_app_iff in Hc as [Hc|Hc]; [|apply in_app_iff in Hc as [Hc|Hc]].
+   rewrite ECTX in Hc.
assert (HcA : In c (image A)) by (unfold image; apply in_app_iff; left; exact Hc).
destruct (ctx_cell_home L A c Hc) as [He Hincl].
apply (KEEPC c (LCtx 0, CTX_SIZE)); [left; exact HcA | exact (old_cell c HcA) | exact He | unfold oentry; discriminate | exact Hincl |].
intros j Hj. rewrite <- (LOC j (PB c (or_introl HcA))). exact (OFFM j Hj).
+   rewrite EA, (areas_cells_metas_eq (upd_meta g (MUsed am') A) A' _ EM) in Hc.
apply areas_cells_upd in Hc as [Hc|Hc]; [| exfalso; apply HN; unfold NEW; apply in_app_iff; right; exact Hc].
assert (HcA : In c (image A)) by (unfold image; apply in_app_iff; right; apply in_app_iff; left; exact Hc).
destruct (In_areas_cells A _ c Hc) as (a & next & Ha & Hca). destruct (area_cell_home L A a next c Ha Hca) as [He Hincl].
apply (KEEPC c (LMem a, PGSZ)); [left; exact HcA | exact (old_cell c HcA) | exact He | | exact Hincl |].
* destruct (inv_areas HW) as (_ & Hareas & _). destruct (Hareas a Ha) as (k & o & rr & -> & Hom & Ho & _).
unfold oentry. intros X. injection X as _ Xo. unfold PGSZ in *. lia.
* intros j Hj. rewrite <- (LOC j (PB c (or_introl HcA))). exact (OFFM j Hj).
+   apply in_flat_map in Hc as ([q a] & Hqa & Hc). cbn [fst snd] in Hc. rewrite U2 in Hqa.
apply in_app_iff in Hqa as [Hqa|[Hqa|Hqa]]; [| injection Hqa as <- <-; exfalso; apply HN; unfold NEW; apply in_app_iff; left; exact Hc |].
all: destruct (OLDU q a ltac:(apply in_app_iff; auto)) as [HqaA Hqg].
all: assert (HcA : In c (image A)) by (apply (In_image_group A q a); assumption).
all: pose proof (proj1 (used_metas_usedX A q a HW) HqaA) as Huq.
all: destruct (group_cell_home L A q a c HW Huq Hc) as (rg2 & Hr2 & Hk2 & Hl2 & He & Hincl).
all: apply (KEEPC c _ (or_introl HcA) (old_cell c HcA) He); [| exact Hincl | intros j Hj; rewrite <- (LOC j (PB c (or_introl HcA))); exact (OFFM j Hj)].
all: unfold oentry; intros X; injection X as Xr _; apply Hqg;
exact (direct_region_unique A g am fr q a HW Hu H63 Hfr (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 shape)))))))))) Huq Xr).
-   apply Forall_forall. intros c Hc.
unfold tail_cells in Hc. apply in_flat_map in Hc as ([q a] & Hqa & Hc). cbn [snd] in Hc. rewrite U2 in Hqa.
apply in_app_iff in Hqa as [Hqa|[Hqa|Hqa]]; [| injection Hqa as <- <-; exact (proj1 (Forall_forall _ _) NC3 c Hc) |].
all: destruct (OLDU q a ltac:(apply in_app_iff; auto)) as [HqaA Hqg].
all: pose proof (proj1 (used_metas_usedX A q a HW) HqaA) as Huq.
all: assert (HcA : In c (tail_cells A)) by (unfold tail_cells; apply in_flat_map; exists (q, a); auto).
all: pose proof (proj1 (Forall_forall _ _) (mc_tail _ _ _ _ _ M) c HcA) as Hcm.
all: destruct (tail_cell_region A HW c HcA) as (q0 & rg2 & Eloc & Hr2 & Hk2 & Hl2 & Ho2 & Hw2).
all: destruct (tail_cell_prid a c Hc) as (q1 & Eloc1 & Ep1); rewrite Eloc in Eloc1; injection Eloc1 as <-.
all: assert (Hkr : prid q0 <> r) by (intros Xr; apply Hqg; rewrite Ep1 in Xr; exact (direct_region_unique A g am fr q a HW Hu H63 Hfr (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 shape)))))))))) Huq Xr)).
all: apply (KEEPC c (LMem (SP (prid q0) 0), rg_len rg2) (or_intror HcA) Hcm (footprint_region_In A _ _ Hr2 Hk2 Hl2));
[unfold oentry; intros X; injection X as Xr _; exact (Hkr Xr)
| unfold range_incl, cell_range, crange; rewrite Eloc; cbn [fst snd]; rewrite (loc_addr_LMem L q0); cbn [loc_addr]; lia |].
all: intros j Hj GX; rewrite Eloc in GX; rewrite (loc_addr_LMem L q0) in GX.
all: destruct g_home as (a0 & k0 & rr & o & rg0 & _ & Hk0 & _ & _ & Hrr & Hlrr & Hkdrr & Ho & Hsz & EG & _).
all: assert (Hne2 : prid q0 <> rr) by (intros E; rewrite E in Hr2; rewrite Hrr in Hr2; injection Hr2 as <-; exact (Hkdrr Hk2)).
all: pose proof (reg_lo_le rg0) as RLO; assert (RL2 : reg_lo rg2 = 0) by (unfold reg_lo; rewrite Hk2; reflexivity);
pose proof (lx_regs _ _ _ LX (prid q0) rr rg2 rg0 Hne2 Hr2 Hrr Hl2 Hlrr ltac:(rewrite RL2; lia) ltac:(unfold PGSZ in *; lia)) as D;
unfold ranges_disjoint in D; rewrite RL2 in D; cbn [fst snd] in D;
unfold METAS_PER_AREA, AREA_HDR, META_SIZE, PGSZ in *; clear - D GX EG Ho Hsz Hk0 Ho2 Hw2 Hj RLO; lia.
-   apply Forall_forall. intros e He. apply In_footprint_A' in He as [[HeA Hne']| ->].
+ pose proof (proj1 (Forall_forall _ _) (mc_foot _ _ _ _ _ M) e HeA) as F. unfold foot_ok in F |- *.
assert (CR : loc_addr L' (fst e) = loc_addr L (fst e)) by (pose proof (crange_L'_old e HeA) as CR0; unfold crange in CR0; exact (f_equal fst CR0)).
rewrite CR. destruct e as [[o|q] len]; cbn [fst snd] in F, CR, Hne', HeA |- *; [exact I|].
intros x Hx. destruct (Z_lt_le_dec x (G + 16)) as [C1|C1]; [|destruct (Z_lt_le_dec x (G + 40)) as [C2|C2]; [apply PRESG; lia|]].
all: destruct (F x Hx) as [b Hb]; exists b; rewrite <- Hb; apply kept; [exists (LMem q, len); cbn [fst snd]; auto | lia].
+ unfold foot_ok, nentry. cbn [fst snd loc_addr]. rewrite L'_new, Z.add_0_r. exact PRES.
Qed.
Lemma statics_A' : statics_ok B mem'.
Proof.
apply (YO2a.statics_ok_ext B mem mem' (mc_statics _ _ _ _ _ M)). intros a Ha.
pose proof (mc_syms _ _ _ _ _ M) as SY. pose proof (so_statics_img _ SY a Ha) as Hi. pose proof (so_img_hi _ SY a Hi) as Hlo.
pose proof placed as (_ & _ & _ & P4 & _). destruct g_home as (a0 & k0 & rr & o & rg0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GI).
pose proof (proj1 YN05.alloc_ceiling_val). apply same_views. apply FRAME; [lia | intros X; exact (NIMG a X Hi) | intros X; exact (P4 a X Hi) | intros X; exact (GI a ltac:(lia) Hi) |].
intros HS. destruct (SCR_hi a HS) as [?|(_ & Hns & _)]; [lia | exact (Hns Ha)].
Qed.
Theorem MRx_A' : MRx B L' A' mem' md'.
Proof.
pose proof vm'_facts as (_ & _ & _ & _ & _ & _ & VH & VLZ & VMT). destruct Hmd as (H1 & _).
apply MRx_intro; [| exact ledger_x_A' | exact rsv_ok_A' | exact ama_ok_A' | exact span_ok_A'].
apply (MRc_intro B L' A' mem' md' (mc_syms _ _ _ _ _ M) WF_A' bounded_A' layout_ok_A').
- unfold L'. cbn. exact (mc_ctx _ _ _ _ _ M).
- unfold L'. cbn. exact (mc_sec _ _ _ _ _ M).
- exact memrep_A'.
- exact tail_geom_A'.
- exact statics_A'.
- exact ledger_ok_A'.
- rewrite VH. exact H1.
- exact VLZ.
- exact VMT.
Qed.
Lemma blocks_addr_A' q k : In (q, k) (user_blocks A) -> ptr_addr L' q = ptr_addr L q.
Proof.
intros Hq. destruct (block_region A q k HW Hq) as (kk & o & rg & -> & Hr & _). unfold ptr_addr. apply loc_addr_L'. cbn. exact (region_of_lt _ _ _ Hr).
Qed.
Lemma frame_A' x : (alloc_ceiling <= x < 2 ^ 64 \/ in_img B x) -> ~ SCR x ->
mbyte (ms_segs B) mem' x = mbyte (ms_segs B) mem x /\ (writable_at (ms_segs B) mem x <-> writable_at (ms_segs B) mem' x).
Proof.
intros Hx HS. pose proof (mc_syms _ _ _ _ _ M) as SY. pose proof placed as (_ & _ & P3 & P4 & _). pose proof (proj1 YN05.alloc_ceiling_val).
destruct g_home as (a0 & k0 & rr & o & rg0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GC & GI).
apply same_views. destruct Hx as [Hx|Hi].
- apply FRAME; [lia | lia | lia | lia | exact HS].
- pose proof (so_img_hi _ SY x Hi). apply FRAME; [lia | intros X; exact (NIMG x X Hi) | intros X; exact (P4 x X Hi) | intros X; exact (GI x ltac:(lia) Hi) | exact HS].
Qed.
Lemma blocks_kept_A' q k i : In (q, k) (user_blocks A) -> In (q, k) (user_blocks A') -> 0 <= i < k ->
mbyte (ms_segs B) mem' (ptr_addr L q + i) = mbyte (ms_segs B) mem (ptr_addr L q + i).
Proof.
intros HqA Hq' Hi. destruct used_metas_A' as (u1 & u2 & U1 & U2).
destruct (in_user_blocks_inv A' (q, k) Hq') as (q2 & a2 & j & f & Hqa & Hj & Hf & Hkf & Eb). rewrite U2 in Hqa.
apply in_app_iff in Hqa as [Hqa|[Hqa|Hqa]].
2:{
exfalso. injection Hqa as <- <-. injection Eb as Eq _.
destruct (block_region A q k HW HqA) as (kk & o & rg & Eqq & Hr & _).
rewrite Eqq in Eq. apply (f_equal prid) in Eq. unfold frame_ptr, slot_start in Eq. rewrite !prid_padd in Eq. cbn in Eq.
pose proof (region_of_lt _ _ _ Hr). unfold r' in Eq. lia. }
all: assert (HqaA : In (q2, a2) (used_metas A)) by (rewrite U1; apply in_app_iff; first [left; exact Hqa | right; right; exact Hqa]).
all: assert (Hqg : q2 <> g) by (intros ->; pose proof (NoDup_used_metas_keys A ND) as NDu; rewrite U1, map_app in NDu; cbn [map fst] in NDu;
apply NoDup_remove_2 in NDu; apply NDu; apply in_app_iff; first [left; apply in_map_iff; exists (g, a2); split; [reflexivity | exact Hqa] | right; apply in_map_iff; exists (g, a2); split; [reflexivity | exact Hqa]]).
all: pose proof (proj1 (used_metas_usedX A q2 a2 HW) HqaA) as Huq.
all: destruct (block_region A q k HW HqA) as (kk & o & rg & Eq & Hr & Hk2 & Hl2 & Ho & Hk0 & Hfit & _).
all: assert (Ekk : kk = prid (am_mem a2)) by (injection Eb as Eq' _; rewrite Eq in Eq'; unfold frame_ptr, slot_start in Eq'; apply (f_equal prid) in Eq'; rewrite !prid_padd in Eq'; exact Eq').
all: assert (Hkr : kk <> r) by (intros Xr; apply Hqg; rewrite Ekk in Xr; exact (direct_region_unique A g am fr q2 a2 HW Hu H63 Hfr (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 shape)))))))))) Huq Xr)).
all: apply same_views; rewrite Eq; unfold ptr_addr; cbn [loc_addr]; apply kept;
[ exists (LMem (SP kk 0), rg_len rg); split; [apply footprint_region_In; assumption|]; split; [unfold oentry; intros X; injection X as Xr _; exact (Hkr Xr)|]; cbn [fst snd loc_addr]; lia
| apply (map_byte_off_meta kk rg); auto; lia ].
Qed.
Lemma p_ok_addr : ptr_addr L' (p_ok A am fr n) = RET + 16 + 16 * OFF /\ RET + 16 + 16 * OFF <> 0.
Proof.
destruct shape as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ho & _).
unfold p_ok. rewrite am_ok_eq. fold am'. unfold am'. rewrite (nc_slot_start am fr n r' (NEEDED / 4096) (proj2 ml')).
unfold ptr_addr. cbn. rewrite Nat.eqb_refl. unfold OFF, UNIT in *. lia.
Qed.
Lemma contents_A' i : 0 <= i < NOLD -> mbyte (ms_segs B) mem' (RET + 16 + 16 * OFF + i) = mbyte (ms_segs B) mem (P + i).
Proof.
intros Hi. destruct shape as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ho & Hno & Hfit).
pose proof (old_present (P + i) ltac:(unfold P; lia)) as [b Hb].
unfold mbyte, P in *. replace (RET + 16 + 16 * OFF + i) with (RET + (16 + 16 * OFF + i)) by lia. unfold w64 in COPY.
rewrite (COPY (16 + 16 * OFF + i)) by lia. replace (MEM + (16 + 16 * OFF + i)) with (MEM + 16 + 16 * OFF + i) by lia. rewrite Hb. reflexivity.
Qed.
Lemma blocks_A' : exists l1 l2 m1 m2, user_blocks A = l1 ++ (frame_ptr am 0 fr, NOLD) :: l2 /\ m1 ++ m2 = l1 ++ l2 /\
user_blocks A' = m1 ++ (p_ok A am fr n, n) :: m2.
Proof.
pose proof (realloc_blocks A _ NOLD n _ _ _ HW Hin ltac:(unfold NOLD, MMAP_THRESHOLD, PGSZ in *; lia) ltac:(lia) yields_ok) as HB.
cbn [fst snd] in HB. destruct HB as (l1 & l2 & m1 & m2 & E1 & E12 & E2 & _ & _). exists l1, l2, m1, m2. auto.
Qed.
End b0.
End OK.
Section EQ.
Hypothesis Heq : OLDLEN = NEEDED.
Definition Ae : astate := A_eq A g am fr n.
Definition ame : ameta := newam am fr n r (am_maplen am).
Definition ENDe : Z := MEM + OLDLEN - 4.
Definition RSVe : Z := OLDLEN - 20 - 16 * OFF - n.
Definition RCe : Z := if 5 <=? RSVe then 5 else RSVe.
Definition TW (x : Z) : Prop := (0 < RSVe /\ x = P + n) \/ (5 <= RSVe /\ ENDe - 5 <= x <= ENDe) \/ x = ENDe.
Lemma am_eq_eq : am_eq am fr n = ame.
Proof.
destruct shape as (Hl & Hml & Hav & Hfd & Hai & Hp & Hnx & Hsl & Hst & Hk & Em & _).
unfold ame, newam, am_eq, upd_slot, am_set_slots. rewrite Hsl. cbn [lupd Z.to_nat].
rewrite Hp, Hnx, Em, Hav, Hfd, Hl, H63, Hai, Hst. unfold OLDLEN. reflexivity.
Qed.
Lemma Ae_fields : Ae = upd_meta g (MUsed ame) A /\ st_regions Ae = st_regions A /\ st_areas Ae = st_areas A /\
footprint Ae = footprint A /\ ctx_cells Ae = ctx_cells A.
Proof.
unfold Ae, A_eq. rewrite am_eq_eq. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [apply footprint_upd_meta | reflexivity].
Qed.
Lemma used_metas_Ae : exists u1 u2, used_metas A = u1 ++ (g, am) :: u2 /\ used_metas Ae = u1 ++ (g, ame) :: u2.
Proof.
destruct (used_metas_upd A g am Mg) as (u1 & u2 & E1 & E2). exists u1, u2. split; [exact E1|].
destruct Ae_fields as (-> & _). apply E2.
Qed.
Lemma MT_Ae q : MT Ae q = if sptr_eqb q g then Some (MUsed ame) else MT A q.
Proof. destruct Ae_fields as (-> & _). apply MT_upd. Qed.
Lemma yields_eq : yields (realloc (Some (frame_ptr am 0 fr)) n A) [] (Some (frame_ptr am 0 fr), Ae).
Proof.
destruct shape as (Hl & _).
pose proof (realloc_tree A g am fr n HW Hu Hfr H63 Hl ltac:(unfold MMAP_THRESHOLD, PGSZ in *; lia) ltac:(lia)) as T.
change (YO30.p am fr) with (frame_ptr am 0 fr) in T. rewrite T.
change (old_len am) with OLDLEN. change (needed fr n) with NEEDED.
replace (OLDLEN =? NEEDED) with true by (symmetry; apply Z.eqb_eq; exact Heq). reflexivity.
Qed.
Lemma WF_Ae : WF Ae.
Proof. exact (realloc_wf A _ NOLD n _ _ _ HW Hin ltac:(unfold NOLD, MMAP_THRESHOLD, PGSZ in *; lia) ltac:(lia) yields_eq). Qed.
Lemma layout_ok_Ae : layout_ok L Ae.
Proof. destruct Ae_fields as (_ & ER & _ & EF & _). exact (layout_ok_same L A Ae HL ER EF). Qed.
Lemma ledger_ok_Ae : ledger_ok B L Ae md.
Proof. destruct Ae_fields as (-> & _). apply ledger_ok_upd_meta. exact LG. Qed.
Lemma ledger_x_Ae : ledger_x L Ae md.
Proof. destruct Ae_fields as (_ & ER & _). exact (ledger_x_same_regions L A Ae md md LX ER eq_refl eq_refl). Qed.
Lemma tail_geom_Ae : tail_geom L Ae.
Proof. exact (tail_geom_of_WF Ae L WF_Ae layout_ok_Ae). Qed.
Lemma bounded_Ae : bounded Ae.
Proof.
pose proof WF_Ae as W. destruct Ae_fields as (EA & _). rewrite EA in W |- *. pose proof (mc_bounded _ _ _ _ _ M) as (_ & B2 & B3).
apply (bounded_of_WF _ W); cbn; assumption.
Qed.
Lemma span_ok_Ae : span_ok Ae.
Proof.
destruct Ae_fields as (-> & _). destruct shape as (Hl & _ & _ & _ & Hai & _).
apply (span_ok_upd_same3 A g am); [exact (MRx_span _ _ _ _ _ MX) | exact Mg | | |]; unfold ame, newam; cbn; symmetry; assumption || exact (eq_sym H63).
Qed.
Lemma ama_ok_Ae : ama_ok Ae.
Proof. destruct Ae_fields as (-> & _). exact (MRx_ama _ _ _ _ _ MX). Qed.
Lemma rsv_ok_Ae : rsv_ok Ae.
Proof.
intros q a i f Hf Hkf. pose proof needed_facts' as (N1 & N2 & N3 & N4). destruct shape as (_ & Hml & _).
unfold frames in Hf. apply in_flat_map in Hf as ([q' a'] & Hqa & Hf).
destruct used_metas_Ae as (u1 & u2 & U1 & U2). rewrite U2 in Hqa.
assert (CASE : (q', a') = (g, ame) \/ In (q', a') (used_metas A)).
{ apply in_app_iff in Hqa as [H|[H|H]]; [right | left; symmetry; exact H | right]; rewrite U1; apply in_app_iff; [left | right; right]; exact H. }
destruct CASE as [E | Hold].
- injection E as -> ->. apply in_flat_map in Hf as (j & Hj & Hf).
change (am_last ame) with 0 in Hj. change (zseq 0 (0 + 1)) with [0] in Hj. destruct Hj as [<-|[]].
unfold ame in Hf. rewrite (nc_slot0 am fr n r (am_maplen am)) in Hf. unfold resize_slot in Hf. cbn [ss_fr In] in Hf. destruct Hf as [E|[]]. injection E as <- <- <- <-.
unfold reserved_of. rewrite (nc_stride am fr n r (am_maplen am) Hml). cbn [fr_off fr_n]. unfold UNIT, IB. fold OFF. fold OLDLEN. lia.
- apply (MRx_rsv _ _ _ _ _ MX q a i f); [| exact Hkf]. unfold frames. apply in_flat_map. exists (q', a'). auto.
Qed.
Section c0.
Variable mem' : word -> option byte.
Variable SCR : Z -> Prop.
Hypothesis SCR_hi : forall x, SCR x -> alloc_ceiling <= x \/ (in_img B x /\ ~ static_owned B x /\ ~ (ms_ctx B <= x < ms_ctx B + CTX_SIZE)).
Hypothesis Wp4 : bytes_at B mem' (P - 4) 1 0.
Hypothesis Wp3 : bytes_at B mem' (P - 3) 1 (32 * RCe).
Hypothesis Wp2 : bytes_at B mem' (P - 2) 2 OFF.
Hypothesis Wg16 : bytes_at B mem' (G + 16) 8 MEM.
Hypothesis Wg24 : bytes_at B mem' (G + 24) 4 0.
Hypothesis Wg28 : bytes_at B mem' (G + 28) 4 0.
Hypothesis Wg32 : bytes_at B mem' (G + 32) 8 (4064 + OLDLEN).
Hypothesis Wend : bytes_at B mem' ENDe 1 0.
Hypothesis Wpn : 0 < RSVe -> bytes_at B mem' (P + n) 1 0.
Hypothesis We45 : 5 <= RSVe -> bytes_at B mem' (ENDe - 4) 4 RSVe /\ bytes_at B mem' (ENDe - 5) 1 0.
Hypothesis PRESW : forall x, (P - 4 <= x < P) \/ (G + 16 <= x < G + 40) \/ TW x -> present mem' x.
Hypothesis FRAME : forall x, 0 <= x < 2 ^ 64 -> ~ (P - 4 <= x < P) -> ~ (G + 16 <= x < G + 40) -> ~ TW x -> ~ SCR x ->
mem' (w64 x) = mem (w64 x).
Lemma kept_e x : 0 <= x < 2 ^ 64 -> ~ (MEM <= x < MEM + OLDLEN) -> ~ (G + 16 <= x < G + 40) -> ~ SCR x -> mem' (w64 x) = mem (w64 x).
Proof.
intros H1 H2 H3 H4. destruct shape as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ho & Hno & Hfit). pose proof needed_facts' as (N1 & _).
pose proof placed as (_ & _ & _ & _ & P5).
apply FRAME; [exact H1 | unfold P; lia | exact H3 | | exact H4].
clear - H2 Ho Hno Hfit N1 P5 Heq Hn. unfold TW, ENDe, RSVe, P, NOLD, OFF, PGSZ in *. lia.
Qed.
Lemma kept_old x : (exists e, In e (footprint A) /\ e <> oentry /\ loc_addr L (fst e) <= x < loc_addr L (fst e) + snd e) ->
~ (G + 16 <= x < G + 40) -> mem' (w64 x) = mem (w64 x).
Proof.
intros (e & He & Hne' & Hx) HG. pose proof (footprint_low B L A mem md e x M He Hx) as LOW. pose proof alloc_ceiling_lt.
assert (D0 : ranges_disjoint (crange L e) (crange L oentry)).
{ pose proof (proj1 (proj2 (proj2 HL))) as PD.
destruct (pairwise_map_In ranges_disjoint (crange L) (footprint A) e oentry PD He oentry_in Hne') as [D|D]; [exact D | apply ranges_disjoint_sym; exact D]. }
apply kept_e; [lia | | exact HG |].
- unfold ranges_disjoint, crange, oentry in D0; cbn [fst snd loc_addr] in D0. unfold MEM. intros X. lia.
- intros HS. destruct (SCR_hi x HS) as [Hhi | (Himg & Hns & Hnc)]; [lia|].
destruct (In_footprint_inv A e He) as [-> | [(ar & Har & ->) | (k & rr & Hr & Hk & Hl & ->)]]; cbn [fst snd loc_addr] in Hx.
+ apply Hnc. rewrite <- (mc_ctx _ _ _ _ _ M). lia.
+ destruct (inv_areas HW) as (_ & Hareas & _). destruct (Hareas ar Har) as (k & o & rr & -> & Hom & Ho & Hr & Hl & Hsz & _). cbn [loc_addr] in Hx.
apply (proj2 (proj2 (proj2 (lg_placed _ _ _ _ LG k rr Hr Hl))) x); [unfold PGSZ in *; lia | exact Himg].
+ apply (proj2 (proj2 (proj2 (lg_placed _ _ _ _ LG k rr Hr Hl))) x); [lia | exact Himg].
Qed.
Lemma G_home' : exists e, In e (footprint A) /\ e <> oentry /\ loc_addr L (fst e) <= G /\ G + 40 <= loc_addr L (fst e) + snd e.
Proof.
destruct g_home as (a & k & rr & o & rg & Ha & Hk & Eg & Ea & Hr & Hl & Hkd & Ho & Hsz & EG & _).
exists (LMem a, PGSZ). split; [right; apply in_app_iff; left; apply in_map_iff; exists a; auto|].
split; [unfold oentry; rewrite Ea; intros X; injection X as _ Xo; unfold PGSZ in *; lia|].
rewrite Ea. cbn [fst snd loc_addr]. unfold METAS_PER_AREA, AREA_HDR, META_SIZE, PGSZ in *. lia.
Qed.
Lemma kept_r x : MEM <= x < MEM + OLDLEN -> ~ (P - 4 <= x < P) -> ~ TW x -> mem' (w64 x) = mem (w64 x).
Proof.
intros H1 H2 H3. pose proof placed as (_ & P2 & P3 & P4 & P5). pose proof alloc_ceiling_lt as ACL.
destruct reg as (rg & Hr & Hk & Hl & Hlen).
apply FRAME; [lia | exact H2 | | exact H3 |].
- apply (map_byte_off_meta r rg x Hr Hk Hl). rewrite Hlen. exact H1.
- intros HS. destruct (SCR_hi x HS) as [Hhi | (Himg & _)]; [lia | exact (P4 x H1 Himg)].
Qed.
Lemma new_cells_e :
Forall (cell_mem B L mem') (group_cells g ame) /\ Forall (cell_mem B L mem') (meta_slot_cells g (Some (MUsed ame))) /\
Forall (cell_mem B L mem') (group_tail_cells ame).
Proof.
destruct old_bytes as (h3 & h16 & Hh & H16 & O1 & O2 & O3 & O45 & O6 & O8).
destruct shape as (_ & Hml & _ & _ & _ & Hp & Hnx & _ & _ & _ & _ & Ho & Hno & Hfit). pose proof needed_facts' as (N1 & _ & _ & N4).
pose proof placed as (_ & P2 & P3 & P4 & P5). pose proof alloc_ceiling_lt as ACL.
assert (KR : forall i w v, bytes_at B mem (MEM + i) w v -> 0 <= i -> i + Z.of_nat w <= 12 + 16 * OFF -> bytes_at B mem' (MEM + i) w v).
{ intros i w v Hb Hi Hw j Hj. rewrite <- (Hb j Hj). apply same_views. apply kept_r; [lia | unfold P; lia |].
clear - Hi Hw Hj Ho Hno Hfit N1 P5 Heq Hn. unfold TW, ENDe, RSVe, P, NOLD, OFF, PGSZ in *. lia. }
assert (EML : am_maplen am * 4096 = OLDLEN) by reflexivity.
assert (ERC : (if 5 <=? am_maplen am * 4096 - 20 - 16 * fr_off fr - n then 5 else am_maplen am * 4096 - 20 - 16 * fr_off fr - n) = RCe) by reflexivity.
destruct G_home' as (eG & HeG & HneG & G1 & G2).
split; [|split].
- apply (nc_group_cells B L mem' g am fr n r (am_maplen am) h3 h16 Hh Hml H16); fold MEM OFF; rewrite ?EML, ?ERC.
+ change (loc_addr L (LMem g)) with G. replace MEM with (MEM + 0) by lia. apply (KR 0 8%nat G); [rewrite Z.add_0_r; exact O1 | lia | cbn; lia].
+ apply (KR 8 4%nat 0 O2); cbn; lia.
+ destruct (Z.eq_dec OFF 0) as [E0|E0].
* unfold P in Wp4. rewrite E0 in Wp4. replace (MEM + 16 + 16 * 0 - 4) with (MEM + 12) in Wp4 by lia. exact Wp4.
* apply (KR 12 1%nat 0 O3); cbn; lia.
+ intros Hoff. destruct (O45 Hoff) as [O4 O5]. fold OFF in Hoff. split; [apply (KR 13 1%nat h3 O4) | apply (KR 14 2%nat h16 O5)]; cbn; lia.
+ exact Wp4.
+ exact Wp3.
+ exact Wp2.
-
assert (OLDM : forall c, In c (meta_slot_cells g (Some (MUsed am))) -> cell_mem B L mem c).
{ intros c Hc. apply old_cell. exact (meta_cells_in_image A g am c HW Hu Hc). }
unfold meta_slot_cells in OLDM. rewrite Hp, Hnx in OLDM. cbn [optr] in OLDM.
assert (K : forall i, 0 <= i < 16 -> mem' (w64 (G + i)) = mem (w64 (G + i))).
{ intros i Hi. apply kept_old; [exists eG; split; [exact HeG|]; split; [exact HneG|]; lia | lia]. }
apply (nc_meta_cells B L mem' g am fr n r (am_maplen am)); change (loc_addr L (LMem g)) with G; fold MEM; rewrite ?EML.
+ pose proof (OLDM _ ltac:(left; reflexivity)) as C0. unfold cell_mem in C0. cbn [mc_loc mc_w mc_val sval_num] in C0. rewrite loc_addr_padd in C0.
change (loc_addr L (LMem g)) with G in C0. unfold META_prev in C0. intros j Hj. rewrite <- (C0 j Hj).
replace (G + 0 + Z.of_nat j) with (G + Z.of_nat j) by lia.
exact (proj1 (same_views (ms_segs B) mem mem' (G + Z.of_nat j) (K (Z.of_nat j) ltac:(lia)))).
+ pose proof (OLDM _ ltac:(right; left; reflexivity)) as C0. unfold cell_mem in C0. cbn [mc_loc mc_w mc_val sval_num] in C0. rewrite loc_addr_padd in C0.
change (loc_addr L (LMem g)) with G in C0. unfold META_next in C0. intros j Hj. rewrite <- (C0 j Hj).
replace (G + 8 + Z.of_nat j) with (G + (8 + Z.of_nat j)) by lia.
exact (proj1 (same_views (ms_segs B) mem mem' (G + (8 + Z.of_nat j)) (K (8 + Z.of_nat j) ltac:(lia)))).
+ exact Wg16.
+ exact Wg24.
+ exact Wg28.
+ exact Wg32.
- apply (nc_tail_cells B L mem' g am fr n r (am_maplen am) Hml); fold MEM OFF; rewrite ?EML, ?ERC.
+ exact Wp3.
+ exact Wpn.
+ exact We45.
+ exact Wend.
Qed.
Definition NEWe : list mcell := group_cells g ame ++ meta_slot_cells g (Some (MUsed ame)).
Lemma NEWe_in_image c : In c NEWe -> In c (image Ae).
Proof.
intros Hc. unfold NEWe in Hc. apply in_app_iff in Hc as [Hc|Hc].
- apply (In_image_group Ae g ame); [| exact Hc]. destruct used_metas_Ae as (u1 & u2 & _ & ->). apply in_app_iff. right. left. reflexivity.
- apply (meta_cells_in_image Ae g ame c WF_Ae); [| exact Hc]. apply usedX_intro; [reflexivity|]. rewrite MT_Ae, sptr_eqb_refl. reflexivity.
Qed.
Lemma not_new_off_meta_e c j : In c (image Ae) -> ~ In c NEWe -> (j < mc_w c)%nat ->
~ (G + 16 <= loc_addr L (mc_loc c) + Z.of_nat j < G + 40).
Proof.
intros Hc HnN Hj Hx. pose proof (image_cells_disjoint Ae L WF_Ae layout_ok_Ae) as PD.
assert (K : forall c', In c' (meta_slot_cells g (Some (MUsed ame))) -> ranges_disjoint (cell_range L c) (cell_range L c')).
{ intros c' Hc'. assert (Hc'N : In c' NEWe) by (unfold NEWe; apply in_app_iff; right; exact Hc').
destruct (pairwise_map_In ranges_disjoint (cell_range L) (image Ae) c c' PD Hc (NEWe_in_image c' Hc'N) ltac:(intros ->; exact (HnN Hc'N))) as [D|D];
[exact D | apply ranges_disjoint_sym; exact D]. }
unfold meta_slot_cells in K. unfold META_prev, META_next, META_mem, META_avail, META_freed, META_bits in K.
pose proof (K _ ltac:(do 3 right; left; reflexivity)) as D3.
pose proof (K _ ltac:(do 4 right; left; reflexivity)) as D4. pose proof (K _ ltac:(do 5 right; left; reflexivity)) as D5.
pose proof (K _ ltac:(do 2 right; left; reflexivity)) as D2'.
unfold ranges_disjoint, cell_range in D2', D3, D4, D5. cbn [fst snd mc_loc mc_w] in D2', D3, D4, D5.
rewrite loc_addr_padd in D2', D3, D4, D5. change (loc_addr L (LMem g)) with G in D2', D3, D4, D5. clear - D2' D3 D4 D5 Hj Hx. lia.
Qed.
Lemma memrep_Ae : memrep B L Ae mem'.
Proof.
destruct new_cells_e as (NC1 & NC2 & NC3). destruct used_metas_Ae as (u1 & u2 & U1 & U2).
destruct Ae_fields as (EA & ER & EAR & EF & ECTX).
assert (NDK : ~ In g (map fst (u1 ++ u2))).
{ pose proof (NoDup_used_metas_keys A ND) as NDu. rewrite U1, map_app in NDu. cbn [map fst] in NDu. apply NoDup_remove_2 in NDu. rewrite map_app. exact NDu. }
assert (OLDU : forall q a, In (q, a) (u1 ++ u2) -> In (q, a) (used_metas A) /\ q <> g).
{ intros q a Hqa. split; [rewrite U1; apply in_app_iff in Hqa as [?|?]; apply in_app_iff; [left | right; right]; assumption|].
intros ->. apply NDK. apply in_map_iff. exists (g, a). auto. }
assert (KEEPC : forall c e, cell_mem B L mem c -> In e (footprint A) -> e <> oentry ->
range_incl (cell_range L c) (crange L e) ->
(forall j, (j < mc_w c)%nat -> ~ (G + 16 <= loc_addr L (mc_loc c) + Z.of_nat j < G + 40)) ->
cell_mem B L mem' c).
{ intros c e Hcm He Hne' Hincl Hoff. apply (cell_keep B L mem mem' c Hcm). intros j Hj. apply kept_old; [| exact (Hoff j Hj)].
exists e. split; [exact He|]. split; [exact Hne'|]. unfold range_incl, cell_range, crange in Hincl. cbn [fst snd] in Hincl. lia. }
split; [|split].
-   apply Forall_forall. intros c Hc.
destruct (In_dec mcell_eq_dec c NEWe) as [HN|HN].
{ unfold NEWe in HN. apply in_app_iff in HN as [HN|HN]; [exact (proj1 (Forall_forall _ _) NC1 c HN) | exact (proj1 (Forall_forall _ _) NC2 c HN)]. }
pose proof (fun j Hj => not_new_off_meta_e c j Hc HN Hj) as OFFM.
unfold image in Hc. apply in_app_iff in Hc as [Hc|Hc]; [|apply in_app_iff in Hc as [Hc|Hc]].
+ rewrite ECTX in Hc. assert (HcA : In c (image A)) by (unfold image; apply in_app_iff; left; exact Hc).
destruct (ctx_cell_home L A c Hc) as [He Hincl].
exact (KEEPC c (LCtx 0, CTX_SIZE) (old_cell c HcA) He ltac:(unfold oentry; discriminate) Hincl OFFM).
+ rewrite EAR, EA in Hc. apply areas_cells_upd in Hc as [Hc|Hc]; [| exfalso; apply HN; unfold NEWe; apply in_app_iff; right; exact Hc].
assert (HcA : In c (image A)) by (unfold image; apply in_app_iff; right; apply in_app_iff; left; exact Hc).
destruct (In_areas_cells A _ c Hc) as (a & next & Ha & Hca). destruct (area_cell_home L A a next c Ha Hca) as [He Hincl].
apply (KEEPC c (LMem a, PGSZ) (old_cell c HcA) He); [| exact Hincl | exact OFFM].
destruct (inv_areas HW) as (_ & Hareas & _). destruct (Hareas a Ha) as (k & o & rr & -> & Hom & Ho & _).
unfold oentry. intros X. injection X as _ Xo. unfold PGSZ in *. lia.
+ apply in_flat_map in Hc as ([q a] & Hqa & Hc). cbn [fst snd] in Hc. rewrite U2 in Hqa.
apply in_app_iff in Hqa as [Hqa|[Hqa|Hqa]]; [| injection Hqa as <- <-; exfalso; apply HN; unfold NEWe; apply in_app_iff; left; exact Hc |].
all: destruct (OLDU q a ltac:(apply in_app_iff; auto)) as [HqaA Hqg].
all: assert (HcA : In c (image A)) by (apply (In_image_group A q a); assumption).
all: pose proof (proj1 (used_metas_usedX A q a HW) HqaA) as Huq.
all: destruct (group_cell_home L A q a c HW Huq Hc) as (rg2 & Hr2 & Hk2 & Hl2 & He & Hincl).
all: apply (KEEPC c _ (old_cell c HcA) He); [| exact Hincl | exact OFFM].
all: unfold oentry; intros X; injection X as Xr _; apply Hqg;
exact (direct_region_unique A g am fr q a HW Hu H63 Hfr (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 shape)))))))))) Huq Xr).
-   apply Forall_forall. intros c Hc.
unfold tail_cells in Hc. apply in_flat_map in Hc as ([q a] & Hqa & Hc). cbn [snd] in Hc. rewrite U2 in Hqa.
apply in_app_iff in Hqa as [Hqa|[Hqa|Hqa]]; [| injection Hqa as <- <-; exact (proj1 (Forall_forall _ _) NC3 c Hc) |].
all: destruct (OLDU q a ltac:(apply in_app_iff; auto)) as [HqaA Hqg].
all: pose proof (proj1 (used_metas_usedX A q a HW) HqaA) as Huq.
all: assert (HcA : In c (tail_cells A)) by (unfold tail_cells; apply in_flat_map; exists (q, a); auto).
all: pose proof (proj1 (Forall_forall _ _) (mc_tail _ _ _ _ _ M) c HcA) as Hcm.
all: destruct (tail_cell_region A HW c HcA) as (q0 & rg2 & Eloc & Hr2 & Hk2 & Hl2 & Ho2 & Hw2).
all: destruct (tail_cell_prid a c Hc) as (q1 & Eloc1 & Ep1); rewrite Eloc in Eloc1; injection Eloc1 as <-.
all: assert (Hkr : prid q0 <> r) by (intros Xr; apply Hqg; rewrite Ep1 in Xr; exact (direct_region_unique A g am fr q a HW Hu H63 Hfr (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 shape)))))))))) Huq Xr)).
all: apply (KEEPC c (LMem (SP (prid q0) 0), rg_len rg2) Hcm (footprint_region_In A _ _ Hr2 Hk2 Hl2));
[unfold oentry; intros X; injection X as Xr _; exact (Hkr Xr)
| unfold range_incl, cell_range, crange; rewrite Eloc; cbn [fst snd]; rewrite (loc_addr_LMem L q0); cbn [loc_addr]; lia |].
all: intros j Hj; rewrite Eloc, (loc_addr_LMem L q0); apply (map_byte_off_meta (prid q0) rg2); auto; lia.
-   rewrite EF. apply Forall_forall. intros e He.
pose proof (proj1 (Forall_forall _ _) (mc_foot _ _ _ _ _ M) e He) as F. unfold foot_ok in F |- *.
assert (TW_dec : forall x, TW x \/ ~ TW x).
{ intros x. unfold TW. destruct (Z_lt_le_dec 0 RSVe); destruct (Z_lt_le_dec RSVe 5); destruct (Z.eq_dec x (P + n)); destruct (Z.eq_dec x ENDe);
destruct (Z_lt_le_dec x (ENDe - 5)); destruct (Z_lt_le_dec ENDe x); first [left; lia | right; lia]. }
assert (OTHER : e <> oentry -> match fst e with LCtx _ => True | LMem _ =>
forall x, loc_addr L (fst e) <= x < loc_addr L (fst e) + snd e -> present mem' x end).
{ intros Hne'. destruct e as [[o|q] len]; cbn [fst snd] in F |- *; [exact I|]. intros x Hx. destruct (F x Hx) as [b Hb].
destruct (Z_lt_le_dec x (G + 16)) as [C1|C1]; [|destruct (Z_lt_le_dec x (G + 40)) as [C2|C2]; [apply PRESW; right; left; lia|]].
all: exists b; rewrite <- Hb; apply kept_old; [exists (LMem q, len); cbn [fst snd]; auto | lia]. }
destruct (In_footprint_inv A e He) as [-> | [(ar & Har & ->) | (k & rr & Hrr & Hkk & Hlk & ->)]].
+ exact I.
+ apply OTHER. destruct (inv_areas HW) as (_ & Hareas & _). destruct (Hareas ar Har) as (k & o & rr & -> & Hom & Ho & _).
unfold oentry. intros X. injection X as _ Xo. unfold PGSZ in *. lia.
+ destruct (Nat.eq_dec k r) as [->|Hkr].
* destruct reg as (rg & Hr & Hk & Hl & Hlen). rewrite Hr in Hrr. injection Hrr as <-. rewrite Hlen. cbn [fst snd loc_addr]. fold MEM.
intros x Hx. rewrite Z.add_0_r in Hx. cbn [fst snd loc_addr] in F. rewrite Hlen in F. fold MEM in F. destruct (F x ltac:(lia)) as [b Hb].
destruct (Z_lt_le_dec x (P - 4)) as [D1|D1]; [|destruct (Z_lt_le_dec x P) as [D2|D2]; [apply PRESW; left; lia|]].
all: destruct (TW_dec x) as [T|T]; [apply PRESW; right; right; exact T|].
all: exists b; rewrite <- Hb; apply kept_r; [exact Hx | lia | exact T].
* apply OTHER. unfold oentry. intros X. injection X as Xr _. exact (Hkr Xr).
Qed.
Lemma statics_Ae : statics_ok B mem'.
Proof.
apply (YO2a.statics_ok_ext B mem mem' (mc_statics _ _ _ _ _ M)). intros a Ha.
pose proof (mc_syms _ _ _ _ _ M) as SY. pose proof (so_statics_img _ SY a Ha) as Hi. pose proof (so_img_hi _ SY a Hi) as Hlo.
pose proof placed as (_ & _ & _ & P4 & _). destruct g_home as (a0 & k0 & rr & o & rg0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GI).
pose proof (proj1 YN05.alloc_ceiling_val). apply same_views. apply kept_e; [lia | intros X; exact (P4 a X Hi) | intros X; exact (GI a ltac:(lia) Hi) |].
intros HS. destruct (SCR_hi a HS) as [?|(_ & Hns & _)]; [lia | exact (Hns Ha)].
Qed.
Theorem MRx_Ae : MRx B L Ae mem' md.
Proof.
destruct Hmd0 as (H1 & H2 & H3).
apply MRx_intro; [| exact ledger_x_Ae | exact rsv_ok_Ae | exact ama_ok_Ae | exact span_ok_Ae].
apply (MRc_intro B L Ae mem' md (mc_syms _ _ _ _ _ M) WF_Ae bounded_Ae layout_ok_Ae (mc_ctx _ _ _ _ _ M) (mc_sec _ _ _ _ _ M)
memrep_Ae tail_geom_Ae statics_Ae ledger_ok_Ae H1 H2 H3).
Qed.
Lemma frame_Ae x : (alloc_ceiling <= x < 2 ^ 64 \/ in_img B x) -> ~ SCR x ->
mbyte (ms_segs B) mem' x = mbyte (ms_segs B) mem x /\ (writable_at (ms_segs B) mem x <-> writable_at (ms_segs B) mem' x).
Proof.
intros Hx HS. pose proof (mc_syms _ _ _ _ _ M) as SY. pose proof placed as (_ & _ & P3 & P4 & _). pose proof (proj1 YN05.alloc_ceiling_val).
destruct g_home as (a0 & k0 & rr & o & rg0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GC & GI).
apply same_views. destruct Hx as [Hx|Hi].
- apply kept_e; [lia | lia | lia | exact HS].
- pose proof (so_img_hi _ SY x Hi). apply kept_e; [lia | intros X; exact (P4 x X Hi) | intros X; exact (GI x ltac:(lia) Hi) | exact HS].
Qed.
Lemma blocks_kept_Ae q k i : In (q, k) (user_blocks A) -> In (q, k) (user_blocks Ae) -> 0 <= i < k ->
mbyte (ms_segs B) mem' (ptr_addr L q + i) = mbyte (ms_segs B) mem (ptr_addr L q + i).
Proof.
intros HqA Hq' Hi. destruct used_metas_Ae as (u1 & u2 & U1 & U2). destruct shape as (Hl & Hml & _ & _ & _ & _ & _ & _ & _ & Hkf0 & Em & _).
destruct (in_user_blocks_inv Ae (q, k) Hq') as (q2 & a2 & j & f & Hqa & Hj & Hf & Hkf & Eb). rewrite U2 in Hqa.
apply in_app_iff in Hqa as [Hqa|[Hqa|Hqa]].
2:{
exfalso. injection Hqa as <- <-. injection Eb as Eq Ek.
change (am_last ame) with 0 in Hj. assert (j = 0) as -> by lia.
unfold ame in Hf, Eq. rewrite (nc_slot0 am fr n r (am_maplen am)) in Hf. unfold resize_slot in Hf. cbn [ss_fr] in Hf. injection Hf as <-.
cbn [fr_n] in Ek. unfold frame_ptr in Eq. rewrite (nc_slot_start am fr n r (am_maplen am) Hml) in Eq. cbn [fr_off padd] in Eq.
assert (HinP : In (frame_ptr am 0 fr, NOLD) (user_blocks A)) by exact Hin.
unfold frame_ptr, slot_start in HinP. rewrite Em in HinP. cbn [padd] in HinP.
assert (Eqp : q = SP r (0 + (UNIT + stride_of am * 0) + UNIT * fr_off fr)) by (rewrite Eq; f_equal; unfold UNIT; lia).
pose proof (user_block_ptrs_NoDup A HW) as NDp.
destruct (in_split _ _ HqA) as (b1 & b2 & EB). rewrite EB in NDp, HinP. rewrite map_app in NDp. cbn [map fst] in NDp.
apply in_app_iff in HinP as [H|[H|H]].
- apply NoDup_remove_2 in NDp. apply NDp. apply in_app_iff. left. apply in_map_iff. exists (SP r (0 + (UNIT + stride_of am * 0) + UNIT * fr_off fr), NOLD). rewrite Eqp. auto.
- injection H as _ HK. unfold NOLD in HK. unfold PGSZ in Hn. lia.
- apply NoDup_remove_2 in NDp. apply NDp. apply in_app_iff. right. apply in_map_iff. exists (SP r (0 + (UNIT + stride_of am * 0) + UNIT * fr_off fr), NOLD). rewrite Eqp. auto. }
all: assert (HqaA : In (q2, a2) (used_metas A)) by (rewrite U1; apply in_app_iff; first [left; exact Hqa | right; right; exact Hqa]).
all: assert (Hqg : q2 <> g) by (intros ->; pose proof (NoDup_used_metas_keys A ND) as NDu; rewrite U1, map_app in NDu; cbn [map fst] in NDu;
apply NoDup_remove_2 in NDu; apply NDu; apply in_app_iff; first [left; apply in_map_iff; exists (g, a2); split; [reflexivity | exact Hqa] | right; apply in_map_iff; exists (g, a2); split; [reflexivity | exact Hqa]]).
all: pose proof (proj1 (used_metas_usedX A q2 a2 HW) HqaA) as Huq.
all: destruct (block_region A q k HW HqA) as (kk & o & rg & Eq & Hr & Hk2 & Hl2 & Ho & Hk0 & Hfit & _).
all: assert (Ekk : kk = prid (am_mem a2)) by (injection Eb as Eq' _; rewrite Eq in Eq'; unfold frame_ptr, slot_start in Eq'; apply (f_equal prid) in Eq'; rewrite !prid_padd in Eq'; exact Eq').
all: assert (Hkr : kk <> r) by (intros Xr; apply Hqg; rewrite Ekk in Xr; exact (direct_region_unique A g am fr q2 a2 HW Hu H63 Hfr Hkf0 Huq Xr)).
all: apply same_views; rewrite Eq; unfold ptr_addr; cbn [loc_addr]; apply kept_old;
[ exists (LMem (SP kk 0), rg_len rg); split; [apply footprint_region_In; assumption|]; split; [unfold oentry; intros X; injection X as Xr _; exact (Hkr Xr)|]; cbn [fst snd loc_addr]; lia
| apply (map_byte_off_meta kk rg); auto; lia ].
Qed.
Lemma p_addr : ptr_addr L (frame_ptr am 0 fr) = P /\ P <> 0.
Proof.
destruct shape as (_ & _ & _ & _ & _ & _ & _ & _ & Hst & _ & Em & Ho & _). pose proof placed as (_ & P2 & _).
unfold frame_ptr, slot_start, ptr_addr. rewrite Em. cbn. fold MEM. unfold P, OFF, UNIT in *. lia.
Qed.
Lemma contents_Ae i : 0 <= i < NOLD -> mbyte (ms_segs B) mem' (P + i) = mbyte (ms_segs B) mem (P + i).
Proof.
intros Hi. destruct shape as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ho & Hno & Hfit). pose proof needed_facts' as (N1 & _). pose proof placed as (_ & _ & _ & _ & P5).
apply same_views. apply kept_r; [unfold P; lia | lia |].
clear - Hi Ho Hno Hfit N1 P5 Heq Hn. unfold TW, ENDe, RSVe, P, NOLD, OFF, PGSZ in *. lia.
Qed.
Lemma blocks_Ae : exists l1 l2 m1 m2, user_blocks A = l1 ++ (frame_ptr am 0 fr, NOLD) :: l2 /\ m1 ++ m2 = l1 ++ l2 /\
user_blocks Ae = m1 ++ (frame_ptr am 0 fr, n) :: m2.
Proof.
pose proof (realloc_blocks A _ NOLD n _ _ _ HW Hin ltac:(unfold NOLD, MMAP_THRESHOLD, PGSZ in *; lia) ltac:(lia) yields_eq) as HB.
cbn [fst snd] in HB. destruct HB as (l1 & l2 & m1 & m2 & E1 & E12 & E2 & _ & _). exists l1, l2, m1, m2. auto.
Qed.
End c0.
End EQ.
End RD.
Record realloc_gctx (B : malloc_syms) (L : layout) (A : astate) (mem : word -> option byte) (md : Model)
(g : sptr) (am : ameta) (fr : frame) (n : Z) : Prop := RGC {
gc_MX : MRx B L A mem md;
gc_used : usedX [] A g am;
gc_fr : ss_fr (nth_slot am 0) = Some fr;
gc_63 : am_sc am = 63;
gc_big : MMAP_THRESHOLD < fr_n fr;
gc_n : fr_n fr + PGSZ <= n < 2 ^ 62;
gc_in : In (frame_ptr am 0 fr, fr_n fr) (user_blocks A) }.
Record ok_memspec (B : malloc_syms) (L : layout) (A : astate) (mem : word -> option byte) (g : sptr) (am : ameta) (fr : frame) (n : Z)
(RET : Z) (mem' : word -> option byte) (SCR : Z -> Prop) : Prop := OKM {
om_scr : forall x, SCR x -> alloc_ceiling <= x \/ (in_img B x /\ ~ static_owned B x /\ ~ (ms_ctx B <= x < ms_ctx B + CTX_SIZE));
om_copy : forall i, 0 <= i < 16 + 16 * OFF fr + NOLD fr -> i <> 16 * OFF fr + 13 -> mem' (w64 (RET + i)) = mem (w64 (MEM L am + i));
om_p3 : bytes_at B mem' (P' fr RET - 3) 1 (32 * RC' fr n);
om_g16 : bytes_at B mem' (G L g + 16) 8 RET;
om_g24 : bytes_at B mem' (G L g + 24) 4 0;
om_g28 : bytes_at B mem' (G L g + 28) 4 0;
om_g32 : bytes_at B mem' (G L g + 32) 8 (4064 + NEEDED fr n);
om_end : bytes_at B mem' (END' fr n RET) 1 0;
om_pn : 0 < RSV' fr n -> bytes_at B mem' (P' fr RET + n) 1 0;
om_e45 : 5 <= RSV' fr n -> bytes_at B mem' (END' fr n RET - 4) 4 (RSV' fr n) /\ bytes_at B mem' (END' fr n RET - 5) 1 0;
om_pres : forall x, RET <= x < RET + NEEDED fr n -> present mem' x;
om_frame : forall x, 0 <= x < 2 ^ 64 -> ~ (RET <= x < RET + NEEDED fr n) -> ~ (MEM L am <= x < MEM L am + OLDLEN am) ->
~ (G L g + 16 <= x < G L g + 40) -> ~ SCR x -> mem' (w64 x) = mem (w64 x);
om_presg : forall x, G L g + 16 <= x < G L g + 40 -> present mem' x }.
Theorem realloc_ok_leaf B L A mem md g am fr n RET mem' SCR :
realloc_gctx B L A mem md g am fr n ->
OLDLEN am <> NEEDED fr n -> RET mod PGSZ = 0 -> 0 < RET -> RET + NEEDED fr n <= alloc_ceiling ->
(forall e, In e (vm_maps (m_vmmaps md)) -> e <> (w64 (MEM L am), w64 (OLDLEN am)) -> ranges_disjoint (RET, NEEDED fr n) (iv_lo e, iv_len e)) ->
(forall x, RET <= x < RET + NEEDED fr n -> ~ in_img B x) ->
ok_memspec B L A mem g am fr n RET mem' SCR ->
MRx B (L' L A RET) (A' A g am fr n) mem' (md' L md am fr n RET) /\
WF (A' A g am fr n) /\ bounded (A' A g am fr n) /\ layout_le A L (L' L A RET) /\
(forall q k, In (q, k) (user_blocks A) -> ptr_addr (L' L A RET) q = ptr_addr L q) /\
(forall x, (alloc_ceiling <= x < 2 ^ 64 \/ in_img B x) -> ~ SCR x ->
mbyte (ms_segs B) mem' x = mbyte (ms_segs B) mem x /\ (writable_at (ms_segs B) mem x <-> writable_at (ms_segs B) mem' x)) /\
(forall q k i, In (q, k) (user_blocks A) -> In (q, k) (user_blocks (A' A g am fr n)) -> 0 <= i < k ->
mbyte (ms_segs B) mem' (ptr_addr L q + i) = mbyte (ms_segs B) mem (ptr_addr L q + i)) /\
(ptr_addr (L' L A RET) (p_ok A am fr n) = RET + 16 + 16 * OFF fr /\ RET + 16 + 16 * OFF fr <> 0) /\
(forall i, 0 <= i < NOLD fr -> mbyte (ms_segs B) mem' (RET + 16 + 16 * OFF fr + i) = mbyte (ms_segs B) mem (P L am fr + i)) /\
(exists l1 l2 m1 m2, user_blocks A = l1 ++ (frame_ptr am 0 fr, NOLD fr) :: l2 /\ m1 ++ m2 = l1 ++ l2 /\
user_blocks (A' A g am fr n) = m1 ++ (p_ok A am fr n, n) :: m2) /\
(m_vm_lazy md = [] /\ m_vm_materialized md = [] /\ m_halted md = None /\
md' L md am fr n RET = with_vmmaps (mremap_maps_next (m_vmmaps md) (w64 (MEM L am)) (w64 RET) (w64 (NEEDED fr n))) md).
Proof.
intros [MX Hu Hfr H63 Hbig Hn Hin] Hne RETal RETpos RETce DISJ NIMG [SCRhi COPY Wp3 Wg16 Wg24 Wg28 Wg32 Wend Wpn We45 PRES FRAME PRESG].
split; [eapply MRx_A'; eassumption|].
split; [eapply WF_A'; eassumption|].
split; [eapply bounded_A'; eassumption|].
split; [eapply layout_le_L'; eassumption|].
split; [intros q k Hq; eapply blocks_addr_A'; eassumption|].
split; [intros x Hx HS; eapply frame_A'; eassumption|].
split; [intros q k i Hq Hq' Hi; eapply blocks_kept_A'; eassumption|].
split; [eapply p_ok_addr; eassumption|].
split; [intros i Hi; eapply contents_A'; eassumption|].
split; [eapply blocks_A'; eassumption|].
destruct (mc_md _ _ _ _ _ (MRx_MRc _ _ _ _ _ MX)) as (H1 & H2 & H3). repeat split; try assumption.
Qed.
Record eq_memspec (B : malloc_syms) (L : layout) (A : astate) (mem : word -> option byte) (g : sptr) (am : ameta) (fr : frame) (n : Z)
(mem' : word -> option byte) (SCR : Z -> Prop) : Prop := EQM {
em_scr : forall x, SCR x -> alloc_ceiling <= x \/ (in_img B x /\ ~ static_owned B x /\ ~ (ms_ctx B <= x < ms_ctx B + CTX_SIZE));
em_p4 : bytes_at B mem' (P L am fr - 4) 1 0;
em_p3 : bytes_at B mem' (P L am fr - 3) 1 (32 * RCe am fr n);
em_p2 : bytes_at B mem' (P L am fr - 2) 2 (OFF fr);
em_g16 : bytes_at B mem' (G L g + 16) 8 (MEM L am);
em_g24 : bytes_at B mem' (G L g + 24) 4 0;
em_g28 : bytes_at B mem' (G L g + 28) 4 0;
em_g32 : bytes_at B mem' (G L g + 32) 8 (4064 + OLDLEN am);
em_end : bytes_at B mem' (ENDe L am) 1 0;
em_pn : 0 < RSVe am fr n -> bytes_at B mem' (P L am fr + n) 1 0;
em_e45 : 5 <= RSVe am fr n -> bytes_at B mem' (ENDe L am - 4) 4 (RSVe am fr n) /\ bytes_at B mem' (ENDe L am - 5) 1 0;
em_presw : forall x, (P L am fr - 4 <= x < P L am fr) \/ (G L g + 16 <= x < G L g + 40) \/ TW L am fr n x -> present mem' x;
em_frame : forall x, 0 <= x < 2 ^ 64 -> ~ (P L am fr - 4 <= x < P L am fr) -> ~ (G L g + 16 <= x < G L g + 40) -> ~ TW L am fr n x -> ~ SCR x ->
mem' (w64 x) = mem (w64 x) }.
Theorem realloc_eq_leaf B L A mem md g am fr n mem' SCR :
realloc_gctx B L A mem md g am fr n ->
OLDLEN am = NEEDED fr n ->
eq_memspec B L A mem g am fr n mem' SCR ->
MRx B L (Ae A g am fr n) mem' md /\
WF (Ae A g am fr n) /\ bounded (Ae A g am fr n) /\
(forall x, (alloc_ceiling <= x < 2 ^ 64 \/ in_img B x) -> ~ SCR x ->
mbyte (ms_segs B) mem' x = mbyte (ms_segs B) mem x /\ (writable_at (ms_segs B) mem x <-> writable_at (ms_segs B) mem' x)) /\
(forall q k i, In (q, k) (user_blocks A) -> In (q, k) (user_blocks (Ae A g am fr n)) -> 0 <= i < k ->
mbyte (ms_segs B) mem' (ptr_addr L q + i) = mbyte (ms_segs B) mem (ptr_addr L q + i)) /\
(ptr_addr L (frame_ptr am 0 fr) = P L am fr /\ P L am fr <> 0) /\
(forall i, 0 <= i < NOLD fr -> mbyte (ms_segs B) mem' (P L am fr + i) = mbyte (ms_segs B) mem (P L am fr + i)) /\
(exists l1 l2 m1 m2, user_blocks A = l1 ++ (frame_ptr am 0 fr, NOLD fr) :: l2 /\ m1 ++ m2 = l1 ++ l2 /\
user_blocks (Ae A g am fr n) = m1 ++ (frame_ptr am 0 fr, n) :: m2) /\
(m_vm_lazy md = [] /\ m_vm_materialized md = [] /\ m_halted md = None).
Proof.
intros [MX Hu Hfr H63 Hbig Hn Hin] Heq [SCRhi Wp4 Wp3 Wp2 Wg16 Wg24 Wg28 Wg32 Wend Wpn We45 PRESW FRAME].
split; [eapply MRx_Ae; eassumption|].
split; [eapply WF_Ae; eassumption|].
split; [eapply bounded_Ae; eassumption|].
split; [intros x Hx HS; eapply frame_Ae; eassumption|].
split; [intros q k i Hq Hq' Hi; eapply blocks_kept_Ae; eassumption|].
split; [eapply p_addr; eassumption|].
split; [intros i Hi; eapply contents_Ae; eassumption|].
split; [eapply blocks_Ae; eassumption|].
destruct (mc_md _ _ _ _ _ (MRx_MRc _ _ _ _ _ MX)) as (H1 & H2 & H3). repeat split; assumption.
Qed.
Lemma Ae_is A g am fr n : Ae A g am fr n = A_eq A g am fr n. Proof. reflexivity. Qed.
Lemma A'_is A g am fr n : A' A g am fr n = A_ok A g am fr n. Proof. reflexivity. Qed.
End h.
