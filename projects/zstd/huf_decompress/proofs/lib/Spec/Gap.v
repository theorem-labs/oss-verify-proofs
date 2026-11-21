(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the band walk gives Linux's placement (gap_band_intro_N, place_found_of_band); 18 recorded proofs replaced by written proofs (FLOOR_val, CEIL_val, CEIL_le_alloc_top and 15 more); adds walk_step_band, walk_band, gap_band_intro and 3 more; imports). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import MState.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import MmapComplete.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Placement.
(* LPS 75d69e00: Linux's placement, by qualified name only (no Import: its own
   [page_round_up_Z_aligned] would shadow). *)
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Placement.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_Gap () := "K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums8positive02I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1N02C4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3subC4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topK46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_loI46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01C4ELinuxProcessSemantics?LinuxProcessSem5State>stack_max_sizec59OSSVerify5KrLib4Spec3Gap4CEILC1?~~~~~~~~~~~~~~~I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4prod00c59OSSVerify5KrLib4Spec3Gap6sum_szC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State:live_bytesK47Corelib4Init9Datatypes4list02C56Stdlib6ZArith6BinInt1Z3addC47Corelib4Init5Logic8eq_ind_rK47Corelib4Init9Datatypes4prod01C47Corelib4Init9Datatypes3sndc59OSSVerify5KrLib4Spec3Gap3gszC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indC47Corelib4Init9Datatypes3appK46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega3Op201C45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z2ltC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeI47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K46Stdlib9micromega6VarMap1t01c59OSSVerify5KrLib4Spec3Gap:gsz_nonnegC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C46Stdlib5Lists4List6filterC47Corelib4Init9Datatypes6lengthI47Corelib4Init5Peano2le00C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith6BinInt1Z6of_natC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses5mkappI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib6ZArith4Znat5Nat2Z8inj_succc59OSSVerify5KrLib4Spec3Gap5aboveC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec3Gap9in_band_bC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec3Gap3ghiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes9andb_propC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z6ltb_ltK46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic3and01C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses9and_morphc59OSSVerify5KrLib4Spec3Gap=above_mono_ptC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indK46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes4bool02I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01C46Stdlib5Lists4List2InC47Corelib4Init3Nat3addC56Stdlib6ZArith6BinInt1Z6ltb_gec59OSSVerify5KrLib4Spec3GapAfilter_above_monoC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addI47Corelib4Init5Logic2or00C4ELinuxProcessSemantics?LinuxProcessSem5State;region_freeC47Corelib4Init9Datatypes3fstI47Corelib4Init5Logic2ex00C4ELinuxProcessSemantics?LinuxProcessSem5State:iv_overlapC47Corelib4Init9Datatypes4negbK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2ex01K47Corelib4Init5Logic2or02C56Stdlib6ZArith6BinInt1Z3divK46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C4ELinuxProcessSemantics?LinuxProcessSem5State?page_round_up_ZC4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizec59OSSVerify5KrLib4Spec3Gap>page_size_4096C1?~~~~~~~~~~~~~~~C46Stdlib6ZArith4Zdiv:Z_mod_multc59OSSVerify5KrLib4Spec3Gap5FLOORC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec3Gap9FLOOR_valC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List4findI47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01C46Stdlib5Lists4List9find_noneC47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic8eq_transc59OSSVerify5KrLib4Spec3Gap3potC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec3Gap=sum_sz_nonnegC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega=RingMicromega5Psatz03C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib3Lib9Placement<vm_find_baseC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec3Gap3gloC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib<MmapCompleteEvm_find_base_completeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec3GapEregion_free_false_invC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega5Tauto8GFormula03c59OSSVerify5KrLib4Spec3Gap8CEIL_valC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes:comparison00c59OSSVerify5KrLib4Spec3Gap9walk_stepC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9filter_Inc59OSSVerify5KrLib4Spec3GapFpage_round_up_Z_boundsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec3GapAfilter_above_dropC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec3GapHpage_round_up_Z_aligned'C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indC46Stdlib5Lists4List7existsbC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedC4ELinuxProcessSemantics?LinuxProcessSem5State7vm_mapsc59OSSVerify5KrLib4Spec3GapAsum_sz_live_bytesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec3Gap@sum_sz_filter_leC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1ZDmul_le_mono_nonneg_rK47Corelib4Init5Peano2le01C56Stdlib6ZArith6BinInt1Z7le_reflc59OSSVerify5KrLib4Spec3Gap4walkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib9Placement@vm_gap_availableC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec3Gap=FLOOR_alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1ZDmul_le_mono_nonneg_lc59OSSVerify5KrLib4Spec3GapFvm_gap_available_introC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

Definition FLOOR : Z := 0x2aaaaaaab000.
Definition CEIL : Z := 0x7fff7f800000.

Lemma FLOOR_val : FLOOR = 0x2aaaaaaab000.
Proof. reflexivity. Qed.
Lemma CEIL_val : CEIL = 0x7fff7f800000.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma CEIL_le_alloc_top : forall h,
  sp_window_lo <= bv_unsigned (vm_init_sp h) -> CEIL <= alloc_top h.
Proof. intros h Hs. unfold alloc_top, CEIL. unfold sp_window_lo, stack_max_size in *. lia. Qed.

Lemma page_size_4096 : page_size = 4096.
Proof. reflexivity. Qed.

Definition glo (e : word * word) : Z := bv_unsigned (fst e).
Definition gsz (e : word * word) : Z := bv_unsigned (snd e).
Definition ghi (e : word * word) : Z := glo e + gsz e.

(* [comment removed for export] *)
Definition in_band_b (e : word * word) : bool := (glo e <? CEIL) && (FLOOR <? ghi e).

Fixpoint sum_sz (l : list (word * word)) : Z :=
  match l with [] => 0 | e :: r => gsz e + sum_sz r end.

Lemma sum_sz_live_bytes : forall l, sum_sz l = live_bytes l.
Proof. induction l as [|[a n] l IH]; cbn; [reflexivity|]. unfold gsz. cbn. rewrite IH. reflexivity. Qed.

Lemma sum_sz_app : forall l1 l2, sum_sz (l1 ++ l2) = sum_sz l1 + sum_sz l2.
Proof. induction l1 as [|e l1 IH]; intros l2; cbn; [reflexivity| rewrite IH; lia]. Qed.

Lemma gsz_nonneg : forall e, 0 <= gsz e.
Proof. intros e. unfold gsz. apply bv_unsigned_in_range. Qed.

Lemma sum_sz_nonneg : forall l, 0 <= sum_sz l.
Proof. induction l as [|e l IH]; cbn; [lia|]. pose proof (gsz_nonneg e). lia. Qed.

Lemma sum_sz_filter_le : forall f l, sum_sz (List.filter f l) <= sum_sz l.
Proof. induction l as [|e l IH]; intros; cbn; [lia|]. pose proof (gsz_nonneg e). destruct (f e); cbn; lia. Qed.

Lemma length_filter_le {A} : forall (f : A -> bool) l, (length (List.filter f l) <= length l)%nat.
Proof. induction l as [|x l IH]; cbn; [lia|]. destruct (f x); cbn; lia. Qed.

(* [comment removed for export] *)
Definition above (c : Z) (e : word * word) : bool := in_band_b e && (c <? ghi e).
Definition pot (nZ c : Z) (maps : list (word * word)) : Z :=
  Z.of_nat (length (List.filter (above c) maps)) * (nZ + 4095) + sum_sz (List.filter (above c) maps).

Lemma above_mono_pt : forall c c' e, c <= c' -> above c' e = true -> above c e = true.
Proof.
  intros c c' e Hc H. unfold above in *. apply andb_prop in H as [H1 H2]. rewrite H1. cbn.
  apply Z.ltb_lt in H2. apply Z.ltb_lt. lia.
Qed.

Lemma filter_above_mono : forall c c' maps, c <= c' ->
  (length (List.filter (above c') maps) <= length (List.filter (above c) maps))%nat
  /\ sum_sz (List.filter (above c') maps) <= sum_sz (List.filter (above c) maps).
Proof.
  intros c c' maps Hc. induction maps as [|e l [IH1 IH2]]; cbn; [split; lia|].
  pose proof (gsz_nonneg e).
  destruct (above c' e) eqn:E1; destruct (above c e) eqn:E2; cbn; try lia.
  rewrite (above_mono_pt c c' e Hc E1) in E2. discriminate.
Qed.

(* [comment removed for export] *)
Lemma filter_above_drop : forall c c' maps e, c <= c' -> In e maps -> above c e = true -> ghi e <= c' ->
  (length (List.filter (above c') maps) + 1 <= length (List.filter (above c) maps))%nat
  /\ sum_sz (List.filter (above c') maps) + gsz e <= sum_sz (List.filter (above c) maps).
Proof.
  intros c c' maps e Hc Hin Ha Hhi. induction maps as [|x l IH]; [destruct Hin|].
  cbn. destruct Hin as [->|Hin].
  - rewrite Ha. assert (Hx : above c' e = false).
    { unfold above in *. apply andb_prop in Ha as [Hb _]. rewrite Hb. cbn. apply Z.ltb_ge. lia. }
    rewrite Hx. cbn. pose proof (filter_above_mono c c' l Hc) as [M1 M2]. lia.
  - specialize (IH Hin). destruct IH as [IH1 IH2]. pose proof (gsz_nonneg x).
    destruct (above c' x) eqn:E1; destruct (above c x) eqn:E2; cbn; try lia.
    rewrite (above_mono_pt c c' x Hc E1) in E2. discriminate.
Qed.

Lemma region_free_false_inv : forall maps lo n,
  region_free maps lo n = false -> exists e, In e maps /\ iv_overlap lo n (fst e) (snd e) = true.
Proof.
  induction maps as [|[a sz] l IH]; intros lo n H; cbn in H; [discriminate|].
  destruct (iv_overlap lo n a sz) eqn:E.
  - exists (a, sz). split; [left; reflexivity| exact E].
  - cbn in H. destruct (IH lo n H) as (e & Hin & He). exists e. split; [right; exact Hin| exact He].
Qed.

Lemma page_round_up_Z_bounds : forall z, z <= page_round_up_Z z <= z + 4095.
Proof.
  intros z. unfold page_round_up_Z. rewrite page_size_4096.
  pose proof (Z.div_mod (z + 4096 - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (z + 4096 - 1) 4096 ltac:(lia)). lia.
Qed.

Lemma page_round_up_Z_aligned' : forall z, page_round_up_Z z mod 4096 = 0.
Proof. intros z. unfold page_round_up_Z. rewrite page_size_4096. apply Z_mod_mult. Qed.

Lemma FLOOR_aligned : FLOOR mod 4096 = 0.
Proof. rewrite FLOOR_val. reflexivity. Qed.

Lemma find_some_of_In {A} : forall (f : A -> bool) l x, In x l -> f x = true -> exists y, List.find f l = Some y.
Proof.
  intros f l x Hin Hf. destruct (List.find f l) as [y|] eqn:E; [exists y; reflexivity|].
  exfalso. pose proof (List.find_none _ _ E x Hin). congruence.
Qed.

Section Walk.
Variable h : VmMaps.
Variable nZ : Z.
Let maps := vm_reserved h ++ vm_maps h.
Hypothesis HnZ : 0 < nZ.
Hypothesis Htop : CEIL <= alloc_top h.

(* [comment removed for export] *)
Lemma walk_step : forall c,
  c mod 4096 = 0 -> FLOOR <= c -> c + nZ + pot nZ c maps <= CEIL ->
  (exists a, vm_find_base h nZ = Some a)
  \/ (exists e, In e maps /\ above c e = true /\ glo e < c + nZ).
Proof.
  intros c Hal Hfl Hinv. pose proof FLOOR_val as FV. pose proof CEIL_val as CV.
  assert (Hpot : 0 <= pot nZ c maps) by (unfold pot; pose proof (sum_sz_nonneg (List.filter (above c) maps)); nia).
  assert (Hc64 : 0 <= c < 2^64) by (unfold FLOOR, CEIL in *; lia).
  assert (HnZ64 : 0 <= nZ < 2^64) by (unfold FLOOR, CEIL in *; lia).
  destruct (region_free maps (Z_to_bv 64 c) (Z_to_bv 64 nZ)) eqn:Hfree.
  - left. apply (MmapComplete.vm_find_base_complete h nZ (Z_to_bv 64 c)); rewrite ?unsigned_lit by exact Hc64.
    + lia.
    + rewrite page_size_4096. exact Hal.
    + lia.
    + unfold CEIL in *. lia.
    + exact Hfree.
  - right. destruct (region_free_false_inv _ _ _ Hfree) as (e & Hin & Hov). exists e.
    unfold iv_overlap in Hov. rewrite !unsigned_lit in Hov by assumption. apply andb_prop in Hov as [O1 O2].
    apply Z.ltb_lt in O1. apply Z.ltb_lt in O2.
    split; [exact Hin|]. split; [| unfold glo; lia].
    unfold above, in_band_b, ghi, glo, gsz. unfold CEIL, FLOOR in *.
    rewrite (proj2 (Z.ltb_lt (bv_unsigned (fst e)) _)) by lia.
    rewrite (proj2 (Z.ltb_lt 0x2aaaaaaab000 _)) by lia.
    rewrite (proj2 (Z.ltb_lt c _)) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma walk : forall k c,
  (length (List.filter (above c) maps) <= k)%nat ->
  c mod 4096 = 0 -> FLOOR <= c -> c + nZ + pot nZ c maps <= CEIL ->
  exists a, vm_find_base h nZ = Some a.
Proof.
  induction k as [|k IH]; intros c Hk Hal Hfl Hinv.
  - destruct (walk_step c Hal Hfl Hinv) as [Hok|(e & Hin & Hab & Hlo)]; [exact Hok|].
    exfalso. assert (HinF : In e (List.filter (above c) maps)) by (apply filter_In; auto).
    destruct (List.filter (above c) maps); [destruct HinF| cbn in Hk; lia].
  - destruct (walk_step c Hal Hfl Hinv) as [Hok|(e & Hin & Hab & Hlo)]; [exact Hok|].
    set (c' := page_round_up_Z (ghi e)).
    pose proof (page_round_up_Z_bounds (ghi e)) as [R1 R2]. fold c' in R1, R2.
    assert (Hhi : c < ghi e). { unfold above in Hab. apply andb_prop in Hab as [_ Hab]. apply Z.ltb_lt in Hab. exact Hab. }
    assert (Hcc : c <= c') by lia.
    destruct (filter_above_drop c c' maps e Hcc Hin Hab R1) as [D1 D2].
    apply (IH c').
    + lia.
    + apply page_round_up_Z_aligned'.
    + lia.
    + unfold pot in *. unfold ghi in *. pose proof (gsz_nonneg e).
      pose proof (sum_sz_nonneg (List.filter (above c') maps)). nia.
Qed.
(* LPS 75d69e00: a fresh grant goes where Linux puts it ([Placement.linux_place]), so the
   no-refusal argument needs the free base the walk finds, not only that some base exists.
   [walk_step_band] and [walk_band] are [walk_step] and [walk] returning that base: it lies in
   the band [[FLOOR, CEIL)]. *)
Lemma walk_step_band : forall c,
  c mod 4096 = 0 -> FLOOR <= c -> c + nZ + pot nZ c maps <= CEIL ->
  region_free maps (Z_to_bv 64 c) (Z_to_bv 64 nZ) = true
  \/ (exists e, In e maps /\ above c e = true /\ glo e < c + nZ).
Proof.
  intros c Hal Hfl Hinv. pose proof FLOOR_val as FV. pose proof CEIL_val as CV.
  assert (Hpot : 0 <= pot nZ c maps) by (unfold pot; pose proof (sum_sz_nonneg (List.filter (above c) maps)); nia).
  assert (Hc64 : 0 <= c < 2^64) by (unfold FLOOR, CEIL in *; lia).
  assert (HnZ64 : 0 <= nZ < 2^64) by (unfold FLOOR, CEIL in *; lia).
  destruct (region_free maps (Z_to_bv 64 c) (Z_to_bv 64 nZ)) eqn:Hfree; [left; reflexivity|].
  right. destruct (region_free_false_inv _ _ _ Hfree) as (e & Hin & Hov). exists e.
  unfold iv_overlap in Hov. rewrite !unsigned_lit in Hov by assumption. apply andb_prop in Hov as [O1 O2].
  apply Z.ltb_lt in O1. apply Z.ltb_lt in O2.
  split; [exact Hin|]. split; [| unfold glo; lia].
  unfold above, in_band_b, ghi, glo, gsz. unfold CEIL, FLOOR in *.
  rewrite (proj2 (Z.ltb_lt (bv_unsigned (fst e)) _)) by lia.
  rewrite (proj2 (Z.ltb_lt 0x2aaaaaaab000 _)) by lia.
  rewrite (proj2 (Z.ltb_lt c _)) by lia. reflexivity.
Qed.
Lemma walk_band : forall k c,
  (length (List.filter (above c) maps) <= k)%nat ->
  c mod 4096 = 0 -> FLOOR <= c -> c + nZ + pot nZ c maps <= CEIL ->
  exists g, g mod 4096 = 0 /\ FLOOR <= g /\ g + nZ <= CEIL
            /\ region_free maps (Z_to_bv 64 g) (Z_to_bv 64 nZ) = true.
Proof.
  induction k as [|k IH]; intros c Hk Hal Hfl Hinv;
    (assert (Hpot : 0 <= pot nZ c maps)
       by (unfold pot; pose proof (sum_sz_nonneg (List.filter (above c) maps)); nia)).
  - destruct (walk_step_band c Hal Hfl Hinv) as [Hfree|(e & Hin & Hab & Hlo)].
    + exists c. split; [exact Hal|]. split; [exact Hfl|]. split; [lia | exact Hfree].
    + exfalso. assert (HinF : In e (List.filter (above c) maps)) by (apply filter_In; auto).
      destruct (List.filter (above c) maps); [destruct HinF| cbn in Hk; lia].
  - destruct (walk_step_band c Hal Hfl Hinv) as [Hfree|(e & Hin & Hab & Hlo)].
    + exists c. split; [exact Hal|]. split; [exact Hfl|]. split; [lia | exact Hfree].
    + set (c' := page_round_up_Z (ghi e)).
      pose proof (page_round_up_Z_bounds (ghi e)) as [R1 R2]. fold c' in R1, R2.
      assert (Hhi : c < ghi e). { unfold above in Hab. apply andb_prop in Hab as [_ Hab]. apply Z.ltb_lt in Hab. exact Hab. }
      assert (Hcc : c <= c') by lia.
      destruct (filter_above_drop c c' maps e Hcc Hin Hab R1) as [D1 D2].
      apply (IH c').
      * lia.
      * apply page_round_up_Z_aligned'.
      * lia.
      * unfold pot in *. unfold ghi in *. pose proof (gsz_nonneg e).
        pose proof (sum_sz_nonneg (List.filter (above c') maps)). nia.
Qed.
End Walk.

(* [comment removed for export] *)
Theorem vm_gap_available_intro : forall h nZ,
  0 < nZ -> CEIL <= alloc_top h ->
  let maps := vm_reserved h ++ vm_maps h in
  (Z.of_nat (length (List.filter in_band_b maps)) + 1) * (nZ + 4095) + live_bytes maps <= CEIL - FLOOR ->
  vm_gap_available h nZ = true.
Proof.
  intros h nZ HnZ Htop maps Hb. unfold vm_gap_available.
  assert (Hinv : FLOOR + nZ + pot nZ FLOOR maps <= CEIL).
  { unfold pot. rewrite <- sum_sz_live_bytes in Hb.
    assert (L1 : (length (List.filter (above FLOOR) maps) <= length (List.filter in_band_b maps))%nat).
    { unfold above. clear. induction maps as [|e l IH]; cbn; [lia|]. destruct (in_band_b e); cbn; [destruct (_ <? _); cbn; lia| lia]. }
    pose proof (sum_sz_filter_le (above FLOOR) maps). pose proof (sum_sz_nonneg maps).
    assert (M : Z.of_nat (length (List.filter (above FLOOR) maps)) * (nZ + 4095)
                <= Z.of_nat (length (List.filter in_band_b maps)) * (nZ + 4095)) by (apply Z.mul_le_mono_nonneg_r; lia).
    lia. }
  destruct (walk h nZ HnZ Htop (length (List.filter (above FLOOR) maps)) FLOOR (le_n _) FLOOR_aligned (Z.le_refl _) Hinv) as [a ->].
  reflexivity.
Qed.

(* [comment removed for export] *)
Corollary vm_gap_available_intro_N : forall h nZ N R T,
  0 < nZ <= R -> CEIL <= alloc_top h ->
  let maps := vm_reserved h ++ vm_maps h in
  Z.of_nat (length (List.filter in_band_b maps)) <= N ->
  live_bytes maps <= T ->
  (N + 1) * (R + 4095) + T <= CEIL - FLOOR ->
  vm_gap_available h nZ = true.
Proof.
  intros h nZ N R T HnZ Htop maps HN HT HB. apply vm_gap_available_intro; [lia| exact Htop|]. fold maps.
  set (L := Z.of_nat (length (List.filter in_band_b maps))) in *.
  assert (M1 : (L + 1) * (nZ + 4095) <= (N + 1) * (nZ + 4095)) by (apply Z.mul_le_mono_nonneg_r; lia).
  assert (M2 : (N + 1) * (nZ + 4095) <= (N + 1) * (R + 4095)) by (apply Z.mul_le_mono_nonneg_l; subst L; lia).
  lia.
Qed.
(* LPS 75d69e00: [vm_gap_available_intro] and [_N] with the base they find: it lies in the band
   [[FLOOR, CEIL)]. *)
Theorem gap_band_intro : forall h nZ,
  0 < nZ -> CEIL <= alloc_top h ->
  let maps := vm_reserved h ++ vm_maps h in
  (Z.of_nat (length (List.filter in_band_b maps)) + 1) * (nZ + 4095) + live_bytes maps <= CEIL - FLOOR ->
  exists g, g mod 4096 = 0 /\ FLOOR <= g /\ g + nZ <= CEIL
            /\ region_free maps (Z_to_bv 64 g) (Z_to_bv 64 nZ) = true.
Proof.
  intros h nZ HnZ Htop maps Hb.
  assert (Hinv : FLOOR + nZ + pot nZ FLOOR maps <= CEIL).
  { unfold pot. rewrite <- sum_sz_live_bytes in Hb.
    assert (L1 : (length (List.filter (above FLOOR) maps) <= length (List.filter in_band_b maps))%nat).
    { unfold above. clear. induction maps as [|e l IH]; cbn; [lia|]. destruct (in_band_b e); cbn; [destruct (_ <? _); cbn; lia| lia]. }
    pose proof (sum_sz_filter_le (above FLOOR) maps). pose proof (sum_sz_nonneg maps).
    assert (M : Z.of_nat (length (List.filter (above FLOOR) maps)) * (nZ + 4095)
                <= Z.of_nat (length (List.filter in_band_b maps)) * (nZ + 4095)) by (apply Z.mul_le_mono_nonneg_r; lia).
    lia. }
  exact (walk_band h nZ HnZ Htop (length (List.filter (above FLOOR) maps)) FLOOR (le_n _) FLOOR_aligned (Z.le_refl _) Hinv).
Qed.
Corollary gap_band_intro_N : forall h nZ N R T,
  0 < nZ <= R -> CEIL <= alloc_top h ->
  let maps := vm_reserved h ++ vm_maps h in
  Z.of_nat (length (List.filter in_band_b maps)) <= N ->
  live_bytes maps <= T ->
  (N + 1) * (R + 4095) + T <= CEIL - FLOOR ->
  exists g, g mod 4096 = 0 /\ FLOOR <= g /\ g + nZ <= CEIL
            /\ region_free maps (Z_to_bv 64 g) (Z_to_bv 64 nZ) = true.
Proof.
  intros h nZ N R T HnZ Htop maps HN HT HB. apply gap_band_intro; [lia| exact Htop|]. fold maps.
  set (L := Z.of_nat (length (List.filter in_band_b maps))) in *.
  assert (M1 : (L + 1) * (nZ + 4095) <= (N + 1) * (nZ + 4095)) by (apply Z.mul_le_mono_nonneg_r; lia).
  assert (M2 : (N + 1) * (nZ + 4095) <= (N + 1) * (R + 4095)) by (apply Z.mul_le_mono_nonneg_l; subst L; lia).
  lia.
Qed.
(* LPS 75d69e00: a free base in the band is at or above [task_unmapped_base] (0x2aaaaab000) and
   below [alloc_top], so it fits Linux's bottom-up window and Linux places the request
   ([Placement.linux_place_exists], whatever the hint). *)
Lemma place_b_of_band : forall h thp hint nZ g,
  0 < nZ -> nZ mod page_size = 0 ->
  g mod 4096 = 0 -> FLOOR <= g -> g + nZ <= alloc_top h ->
  region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 g) (Z_to_bv 64 nZ) = true ->
  exists a, Placement.linux_place_b h thp hint nZ = Some a.
Proof.
  intros h thp hint nZ g HnP HnA Hal Hfl Hhi Hfree.
  assert (Hal' : g mod page_size = 0) by (rewrite page_size_4096; exact Hal).
  (* [task_unmapped_base] is 0x2aaaaab000 (727298f3 Sys/Mm/Mmap.v:1136); the term below states
     it by value and the window conjunct takes it by conversion. *)
  assert (Hlo : 0x2aaaaab000 <= g) by (unfold FLOOR in Hfl; lia).
  destruct (Placement.linux_place_exists h thp hint nZ HnP HnA
              (ex_intro _ g (or_intror (conj Hal' (conj Hlo (conj Hhi Hfree)))))) as [a Ha].
  exists a. exact (proj2 (proj1 (Placement.linux_place_b_spec h thp hint nZ HnP HnA) a) Ha).
Qed.
(* The edition's placement test ([mmap_place_found]) holds at a free base in the band. *)
Lemma place_found_of_band : forall m hint nZ g,
  0 < nZ -> nZ mod page_size = 0 -> g mod 4096 = 0 -> FLOOR <= g -> g + nZ <= alloc_top (m_vmmaps m) ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) (Z_to_bv 64 g) (Z_to_bv 64 nZ) = true ->
  mmap_place_found m hint nZ = true.
Proof.
  intros m hint nZ g HnP HnA Hal Hfl Hhi Hfree. unfold mmap_place_found.
  destruct (place_b_of_band (m_vmmaps m) (kb_thp (m_kernel m)) hint nZ g HnP HnA Hal Hfl Hhi Hfree) as [a ->].
  reflexivity.
Qed.
