(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec StoreOk HeapIface HeapIfaceA L5Defs L5Core L5DefsAB0 L5CoreAB0S9 L5StepARB0S9 HeapIfaceAEx.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayoutB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeCStaticsA PeCSpecsAb.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA PnLayout PeLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmStatics PmStaticsA PnStatics PnStaticsA PmSpecsA PeSpecsAb PmModelFactsA PeStepAB0 L5ADetailHRB0S9.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PEBHK.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation AD := PeCLayoutB.CADDR_B.
Abbreviation AAD := PeCLayoutB.CAADDR_B.
Abbreviation AN := PMB.AN.
Abbreviation EE := PeCLayoutB.EADDR_B.

Definition bcell (a : Z) : Prop := (65536 <= a < 0x13f000) \/ (0x69a1c0 <= a < 0x69a1c8) \/ (0x69a413 <= a < 0x69a414) \/ (0x69a4f0 <= a < 0x69a4f4).
Definition lcell (a : Z) : Prop := (0x6789b2 <= a < 0x6790f0) \/ (0x679818 <= a < 0x679870).
Definition scell (a : Z) : Prop := 0x6789b0 <= a < 0x6789b2.
Definition ecell (a : Z) : Prop := (0x678780 <= a < 0x678782) \/ (0x69a1d0 <= a < 0x69a3f0).

Section Keep.
Variables M M' : word -> option byte.
Lemma base_keep : (forall a, 0 <= a < 2 ^ 64 -> bcell a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> PMSTA.base_okA RSEGS AD M -> PMSTA.base_okA RSEGS AD M'.
Proof.
  intros AG BO. unfold PMSTA.base_okA, L5.img_clear in *. cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock PeCLayoutB.CADDR_B] in *.
  destruct BO as (RO0 & (can & Hcan & CAN) & NL & LL).
  split; [|split; [|split]].
  - intros i Hi. rewrite AG; [apply RO0; exact Hi| lia| left; lia].
  - exists can. split; [exact Hcan|]. apply (L5C.u64_at_agree RSEGS M M'); [intros i Hi; apply AG; [lia| right; left; lia]|lia|lia| exact CAN].
  - apply (L5C.u8_at_agree RSEGS M M'); [intros i Hi; apply AG; [lia| right; right; left; lia]|lia|lia| exact NL].
  - unfold L5.u32_at in *. rewrite (L5C.rdn_agree RSEGS M M' 4%nat 0x69a4f0); [exact LL|lia|cbn; lia|].
    intros i Hi. cbn in Hi. apply AG; [lia| right; right; right; lia].
Qed.
Lemma loc_keep b : (forall a, 0 <= a < 2 ^ 64 -> lcell a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> PMST.loc_ok RSEGS AD M b -> PMST.loc_ok RSEGS AD M' b.
Proof.
  intros AG LOC. unfold PMST.loc_ok in *. cbn [pa_glocale pa_classic_imp pa_loc_foot PeCLayoutB.CADDR_B] in *. destruct b.
  - destruct LOC as (G & P). split.
    + apply (L5C.u8_at_agree RSEGS M M'); [intros i Hi; apply AG; [lia| left; lia]|lia|lia| exact G].
    + apply (L5C.u64_at_agree RSEGS M M'); [intros i Hi; apply AG; [lia| left; lia]|lia|lia| exact P].
  - intros iv Hin. pose proof (LOC iv Hin) as X. intros i Hi. rewrite AG; [apply X; exact Hi| |].
    + destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hi; lia.
    + destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hi; unfold lcell; lia.
Qed.
Lemma sys_keep b : (forall a, 0 <= a < 2 ^ 64 -> scell a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> PMST.sys_ok RSEGS AD M b -> PMST.sys_ok RSEGS AD M' b.
Proof.
  intros AG SYS. unfold PMST.sys_ok in *. cbn [pa_syscat_guard PeCLayoutB.CADDR_B] in *. destruct b.
  - apply (L5C.u8_at_agree RSEGS M M'); [intros i Hi; apply AG; [lia| unfold scell; lia]|lia|lia| exact SYS].
  - intros i Hi. rewrite AG; [apply SYS; exact Hi| lia| unfold scell; lia].
Qed.
Lemma err_keep b : (forall a, 0 <= a < 2 ^ 64 -> ecell a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> PESTA.err_okA RSEGS AD AAD EE M b -> PESTA.err_okA RSEGS AD AAD EE M' b.
Proof.
  intros AG (ERG & ATX). unfold PESTA.err_okA. cbn [pa_errcat_guard PeCLayoutB.CADDR_B] in *.
  assert (U8 : forall a v, ecell a -> a < 2 ^ 47 -> L5.u8_at RSEGS M a v -> L5.u8_at RSEGS M' a v).
  { intros a v Ha Hr. apply (L5C.u8_at_agree RSEGS M M'); [intros i Hi; apply AG; [unfold ecell in Ha; lia| replace i with a by lia; exact Ha]| unfold ecell in Ha; lia| lia]. }
  assert (CLR : forall lo hi, (forall a, lo <= a < hi -> ecell a) -> 0 <= lo -> L5.img_clear M lo hi -> L5.img_clear M' lo hi).
  { intros lo hi He Hlo X i Hi. rewrite AG; [apply X; exact Hi| pose proof (He i Hi) as E; unfold ecell in E; lia| exact (He i Hi)]. }
  split.
  - destruct b.
    + apply U8; [unfold ecell; lia| lia| exact ERG].
    + apply CLR; [intros a Ha; unfold ecell; lia| lia| exact ERG].
  - apply (PESTA.atexit_stA_agree RSEGS AD AAD EE PECSB.addrs_wf_B M M' b); [|exact ATX].
    intros i Hi. cbn [pa_atexit PeCLayoutB.CADDR_B] in Hi. apply AG; [lia| unfold ecell; lia].
Qed.
End Keep.

Definition statc (a : Z) : Prop := bcell a \/ lcell a \/ scell a \/ ecell a.
Lemma statc_range a : statc a -> 65536 <= a < 0x69a4f4.
Proof. unfold statc, bcell, lcell, scell, ecell. lia. Qed.

Lemma ls_agree g (M M' : word -> option byte) : (forall a, 0 <= a < 2 ^ 64 -> statc a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  PESTA.ls_okA RSEGS AD AAD EE g M -> PESTA.ls_okA RSEGS AD AAD EE g M'.
Proof.
  intros AG (B & LO & SY & ER). split; [|split; [|split]].
  - apply (base_keep M M'); [intros a Ha X; apply AG; [exact Ha| left; exact X]| exact B].
  - apply (loc_keep M M'); [intros a Ha X; apply AG; [exact Ha| right; left; exact X]| exact LO].
  - apply (sys_keep M M'); [intros a Ha X; apply AG; [exact Ha| right; right; left; exact X]| exact SY].
  - apply (err_keep M M'); [intros a Ha X; apply AG; [exact Ha| right; right; right; exact X]| exact ER].
Qed.

Lemma ls_piece g (M M' : word -> option byte) (Wp : Z -> Prop) :
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> (forall a, Wp a -> a < 65536 \/ 0x69a4f4 <= a) ->
  PESTA.ls_okA RSEGS AD AAD EE g M -> PESTA.ls_okA RSEGS AD AAD EE g M'.
Proof. intros FR WP. apply ls_agree. intros a Ha X. apply FR; [exact Ha|]. intros Y. apply WP in Y. apply statc_range in X. lia. Qed.

Definition far (W : list L5.range) : Prop := forall r, In r W -> fst r + snd r <= 65536 \/ 0x69a4f4 <= fst r.
Lemma far_outside W a : far W -> statc a -> L5.outside W a.
Proof. intros FW X r Hr. apply statc_range in X. specialize (FW r Hr). unfold L5.in_rng. lia. Qed.
Lemma far_nil : far [].
Proof. intros r []. Qed.
Lemma far_cons r W : fst r + snd r <= 65536 \/ 0x69a4f4 <= fst r -> far W -> far (r :: W).
Proof. intros H FW r' [<-|Hr]; [exact H| exact (FW r' Hr)]. Qed.
Lemma far_app W1 W2 : far W1 -> far W2 -> far (W1 ++ W2).
Proof. intros F1 F2 r Hr. apply in_app_or in Hr. destruct Hr as [Hr|Hr]; [exact (F1 r Hr)| exact (F2 r Hr)]. Qed.

Section Client.
Variables (L : asan_layout) (C : asan_statics_cells).
Hypothesis LY : PMB.layout L C.
Let LYa := PMB.ly_as0 L C LY.

Lemma stat_client (ar : asan_run) {BS ST} LB FF sp scr a :
  (forall x, ST x -> hl_rt_static L x) -> (bcell a \/ lcell a \/ scell a \/ ecell a) -> aclient_g BS ST L ar LB FF sp scr a.
Proof.
  intros HST Ha. right; right; left. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split.
  - unfold bcell, lcell, scell, ecell in Ha. lia.
  - intros X. apply HST in X. destruct Ha as [[Y|Y]|Y].
    + pose proof (L5A.aly_static_lo L C LYa a X). lia.
    + refine (PMB.ly_static L C LY a _ X). apply PNST.dep_of_j. unfold PMST.dep. destruct Y as [Y|[Y|Y]].
      * right; left. cbn [pa_canary PMB.AD ADDR_B]. lia.
      * right; right. exists (0x69a413, 0x69a414). split; [cbn; tauto| cbn [fst snd]; lia].
      * right; right. exists (0x69a4f0, 0x69a4f4). split; [cbn; tauto| cbn [fst snd]; lia].
    + refine (PMB.ly_static L C LY a _ X). destruct Y as [[Y|Y]|[Y|Y]].
      * apply PNST.dep_of_j. apply (PMST.in_foot_loc PMB.AD (0x6789b2, 0x6790f0)); [cbn; tauto| cbn [fst snd]; lia].
      * apply PNST.dep_of_j. apply (PMST.in_foot_loc PMB.AD (0x679818, 0x679870)); [cbn; tauto| cbn [fst snd]; lia].
      * apply PNST.dep_of_j. apply PMST.in_foot_sysg. cbn [pa_syscat_guard PMB.AD ADDR_B]. unfold scell in Y. lia.
      * destruct Y as [Y|Y].
        -- apply PNST.dep_of_j. apply PMST.in_foot_errg. cbn [pa_errcat_guard PMB.AD ADDR_B]. lia.
        -- apply PNST.dep_of_j. apply PMST.in_foot_atexit. cbn [pa_atexit PMB.AD ADDR_B]. lia.
Qed.

Lemma ls_ahpres_g (P : Z -> Prop) (ar : asan_run) LB FF sp scr W (M M' : word -> option byte) :
  L5CA.ahpres L ar LB FF sp scr W M M' -> (forall a, P a -> statc a) -> (forall a, P a -> L5.outside W a) ->
  forall a, 0 <= a < 2 ^ 64 -> P a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Proof.
  intros (AK & _ & _) PS PO a Ha X. apply AK. split; [exact Ha|]. split; [| exact (PO a X)].
  apply (stat_client ar LB FF sp scr a (fun x X => X)). exact (PS a X).
Qed.
Lemma ls_ahpres g (ar : asan_run) LB FF sp scr W (M M' : word -> option byte) :
  L5CA.ahpres L ar LB FF sp scr W M M' -> far W -> PESTA.ls_okA RSEGS AD AAD EE g M -> PESTA.ls_okA RSEGS AD AAD EE g M'.
Proof.
  intros AH FW. apply ls_agree. apply (ls_ahpres_g statc ar LB FF sp scr W M M' AH (fun a X => X)). intros a X. exact (far_outside W a FW X).
Qed.

Lemma ls_ahpres_loc g (ar : asan_run) LB FF sp scr W (M M' : word -> option byte) :
  L5CA.ahpres L ar LB FF sp scr W M M' -> (forall a, (bcell a \/ scell a \/ ecell a) -> L5.outside W a) ->
  PESTA.ls_okA RSEGS AD AAD EE g M -> PMST.loc_ok RSEGS AD M' true -> PESTA.ls_okA RSEGS AD AAD EE (PMST.ST true (PMST.st_sys g) (PMST.st_err g)) M'.
Proof.
  intros AH FW (B & _ & SY & ER) LO'.
  pose proof (ls_ahpres_g (fun a => bcell a \/ scell a \/ ecell a) ar LB FF sp scr W M M' AH) as AG.
  specialize (AG ltac:(intros a [X|[X|X]]; unfold statc; tauto) FW).
  split; [|split; [|split]]; cbn [PMST.st_loc PMST.st_sys PMST.st_err].
  - apply (base_keep M M'); [intros a Ha X; apply AG; [exact Ha| left; exact X]| exact B].
  - exact LO'.
  - apply (sys_keep M M'); [intros a Ha X; apply AG; [exact Ha| right; left; exact X]| exact SY].
  - apply (err_keep M M'); [intros a Ha X; apply AG; [exact Ha| right; right; exact X]| exact ER].
Qed.
Lemma ls_ahpres_sys g (ar : asan_run) LB FF sp scr W (M M' : word -> option byte) :
  L5CA.ahpres L ar LB FF sp scr W M M' -> (forall a, (bcell a \/ lcell a \/ ecell a) -> L5.outside W a) ->
  PESTA.ls_okA RSEGS AD AAD EE g M -> PMST.sys_ok RSEGS AD M' true -> PESTA.ls_okA RSEGS AD AAD EE (PMST.ST (PMST.st_loc g) true (PMST.st_err g)) M'.
Proof.
  intros AH FW (B & LO & _ & ER) SY'.
  pose proof (ls_ahpres_g (fun a => bcell a \/ lcell a \/ ecell a) ar LB FF sp scr W M M' AH) as AG.
  specialize (AG ltac:(intros a [X|[X|X]]; unfold statc; tauto) FW).
  split; [|split; [|split]]; cbn [PMST.st_loc PMST.st_sys PMST.st_err].
  - apply (base_keep M M'); [intros a Ha X; apply AG; [exact Ha| left; exact X]| exact B].
  - apply (loc_keep M M'); [intros a Ha X; apply AG; [exact Ha| right; left; exact X]| exact LO].
  - exact SY'.
  - apply (err_keep M M'); [intros a Ha X; apply AG; [exact Ha| right; right; exact X]| exact ER].
Qed.
Lemma ls_ahpres_err g e' (ar : asan_run) LB FF sp scr W (M M' : word -> option byte) :
  L5CA.ahpres L ar LB FF sp scr W M M' -> (forall a, (bcell a \/ lcell a \/ scell a) -> L5.outside W a) ->
  PESTA.ls_okA RSEGS AD AAD EE g M -> PESTA.err_okA RSEGS AD AAD EE M' e' -> PESTA.ls_okA RSEGS AD AAD EE (PMST.ST (PMST.st_loc g) (PMST.st_sys g) e') M'.
Proof.
  intros AH FW (B & LO & SY & _) ER'.
  pose proof (ls_ahpres_g (fun a => bcell a \/ lcell a \/ scell a) ar LB FF sp scr W M M' AH) as AG.
  specialize (AG ltac:(intros a [X|[X|X]]; unfold statc; tauto) FW).
  split; [|split; [|split]]; cbn [PMST.st_loc PMST.st_sys PMST.st_err].
  - apply (base_keep M M'); [intros a Ha X; apply AG; [exact Ha| left; exact X]| exact B].
  - apply (loc_keep M M'); [intros a Ha X; apply AG; [exact Ha| right; left; exact X]| exact LO].
  - apply (sys_keep M M'); [intros a Ha X; apply AG; [exact Ha| right; right; exact X]| exact SY].
  - exact ER'.
Qed.
End Client.

Lemma agA_frame (M M' : word -> option byte) (Wp : Z -> Prop) o n :
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> 0 <= o -> o + n <= 2 ^ 47 ->
  (forall x, o <= x < o + n -> ~ Wp x /\ ~ Wp (HeapIfaceA.S x)) -> PMFA.agA M M' o n.
Proof.
  intros FR Ho Hn H. split.
  - intros i Hi. apply FR; [lia| exact (proj1 (H i Hi))].
  - intros x Hx. pose proof (PMKB.S_in_shadow x ltac:(lia)) as SX. apply FR; [unfold BIGSHADOW_LO, BIGSHADOW_HI in SX; lia| exact (proj2 (H x Hx))].
Qed.

Section Blk.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (scfg : SpuriousCfg) (HI : asan_iface).
Hypothesis HIok : HAJ.asan_iface_okR L ar C scfg HI.
Lemma blk_agA LBx FFx LKx crx Ax Mx Vx (p c F rs slo shi : Z) (Wp : Z -> Prop) (M1 M2 : word -> option byte) :
  ri_inv HI LBx FFx LKx crx Ax Mx Vx -> In (p, c) LBx -> In (F, 5, rs) (FFx ++ LKx) -> F mod 8 = 0 -> 0 <= F -> F + 2048 <= 2 ^ 47 ->
  (BIGSHADOW_HI <= F \/ F + 2048 <= BIGSHADOW_LO) -> ahl_ceil ar <= slo -> BIGSHADOW_HI <= slo ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  (forall a, Wp a -> (F <= a < F + 2048) \/ (F / 8 + HeapIfaceA.SB <= a < F / 8 + HeapIfaceA.SB + 256) \/ (slo <= a < shi)) ->
  PMFA.agA M1 M2 p c.
Proof.
  intros HH Hin HF F8 F0 F1 FBIG SL1 SL2 FR WP.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (D0 : 0 <= F / 8 /\ F / 8 + 256 <= 2 ^ 44) by lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
  pose proof (WB (p, c) Hin) as ((P0 & _ & P3 & P4 & P5 & P6) & _ & _ & _ & _ & PFA & _). cbn [fst snd] in *.
  pose proof (PFA (F, 5, rs) HF) as PF. cbn [ff_addr ff_class fst snd] in PF. change (ff_bytes 5) with 2048 in PF.
  unfold app_mem in P6.
  apply (agA_frame M1 M2 Wp p c FR); [lia| lia|]. intros x Hx. split.
  - intros X. apply WP in X. unfold HeapIfaceA.SB, BIGSHADOW_LO, BIGSHADOW_HI in *. lia.
  - intros X. apply WP in X. unfold HeapIfaceA.S, HeapIfaceA.SB, BIGSHADOW_LO, BIGSHADOW_HI in *.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (D1 : 0 <= x / 8 <= 2 ^ 44) by lia.
    assert (D2 : p + c <= F -> x / 8 < F / 8) by lia.
    assert (D3 : F + 2048 <= p -> F / 8 + 256 <= x / 8) by lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    lia.
Qed.
End Blk.

Lemma vis_agree (Hd : word -> bool) (M Mv : word -> option byte) a n :
  (forall w, Hd w = false -> M w = Mv w) -> L5A.avis Hd a n -> L5C.agree_on Mv M a n.
Proof. intros VV AV i Hi. apply VV. replace i with (a + (i - a)) by lia. apply AV. lia. Qed.
Lemma u32_agree (M M' : word -> option byte) a v : L5C.agree_on M M' a 4 -> 0 <= a -> a + 4 <= 2 ^ 64 -> L5.u32_at RSEGS M a v -> L5.u32_at RSEGS M' a v.
Proof. intros Hag Ha H4 Hu. unfold L5.u32_at in *. rewrite (L5C.rdn_agree RSEGS M M' 4%nat a Ha ltac:(cbn; lia)). exact Hu. intros i Hi; apply Hag; cbn in Hi; lia. Qed.
Lemma u64_vis (Hd : word -> bool) (M Mv : word -> option byte) a v :
  (forall w, Hd w = false -> M w = Mv w) -> L5A.avis Hd a 8 -> 0 <= a -> a + 8 <= 2 ^ 64 -> L5.u64_at RSEGS Mv a v -> L5.u64_at RSEGS M a v.
Proof. intros VV AV H0 H1. apply (L5C.u64_at_agree RSEGS Mv M a v (vis_agree Hd M Mv a 8 VV AV) H0 H1). Qed.
Lemma u32_vis (Hd : word -> bool) (M Mv : word -> option byte) a v :
  (forall w, Hd w = false -> M w = Mv w) -> L5A.avis Hd a 4 -> 0 <= a -> a + 4 <= 2 ^ 64 -> L5.u32_at RSEGS Mv a v -> L5.u32_at RSEGS M a v.
Proof. intros VV AV H0 H1. apply (u32_agree Mv M a v (vis_agree Hd M Mv a 4 VV AV) H0 H1). Qed.
Lemma avis_sub (Hd : word -> bool) a n a' n' : L5A.avis Hd a n -> a <= a' -> a' + n' <= a + n -> L5A.avis Hd a' n'.
Proof. intros AV H1 H2 i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply AV. lia. Qed.
Lemma shz_vis (Hd : word -> bool) (M Mv : word -> option byte) o g q :
  (forall w, Hd w = false -> M w = Mv w) -> L5A.avis Hd q g -> o / 8 + HeapIfaceA.SB = q -> 0x69c000 <= q -> q + g <= 2 ^ 64 ->
  (forall j, 0 <= j < g -> L5.u8_at RSEGS Mv (q + j) 0) -> shadow_zero M o g.
Proof.
  intros VV AV EQ Q0 Q1 U j Hj. unfold byte_at, HeapIfaceA.S. rewrite EQ. rewrite VV; [| apply AV; exact Hj].
  apply (L5ADHR.byte_of_u8 Mv _ 0 (U j Hj)); lia.
Qed.

Lemma agA_ahpres_ff (L : asan_layout) (ar : asan_run) LBc FFc spc scrc Wc (M M' : word -> option byte) f o n :
  L5CA.ahpres L ar LBc FFc spc scrc Wc M M' -> In f FFc -> ff_addr f + 32 <= o -> o + n <= ff_addr f + ff_bytes (ff_class f) - 8 -> 0 <= o -> o + n <= 2 ^ 47 ->
  (forall x, o <= x < o + n -> L5.outside Wc x /\ L5.outside Wc (HeapIfaceA.S x)) -> PMFA.agA M M' o n.
Proof.
  intros (AK & _ & _) Hf H1 H2 H3 H4 OUT. split.
  - intros i Hi. apply AK. split; [lia|]. split; [| exact (proj1 (OUT i Hi))]. right; right; right; left. exists f. split; [exact Hf| lia].
  - intros x Hx. pose proof (PMKB.S_in_shadow x ltac:(lia)) as SX. apply AK. split; [unfold BIGSHADOW_LO, BIGSHADOW_HI in SX; lia|]. split; [| exact (proj2 (OUT x Hx))].
    right; right; right; right; right; left. exists f. split; [exact Hf|]. unfold in_shadow_of. split; apply PMKB.S_mono; lia.
Qed.
Lemma agA_ahpres_blk (L : asan_layout) (ar : asan_run) LBc FFc spc scrc Wc (M M' : word -> option byte) p c :
  L5CA.ahpres L ar LBc FFc spc scrc Wc M M' -> In (p, c) LBc -> 0 <= p -> p + c <= 2 ^ 47 ->
  (forall x, p <= x < p + c -> L5.outside Wc x /\ L5.outside Wc (HeapIfaceA.S x)) -> PMFA.agA M M' p c.
Proof.
  intros (AK & _ & _) Hin H3 H4 OUT. split.
  - intros i Hi. apply AK. split; [lia|]. split; [| exact (proj1 (OUT i Hi))]. left. exists (p, c). split; [exact Hin| cbn [fst snd]; lia].
  - intros x Hx. pose proof (PMKB.S_in_shadow x ltac:(lia)) as SX. apply AK. split; [unfold BIGSHADOW_LO, BIGSHADOW_HI in SX; lia|]. split; [| exact (proj2 (OUT x Hx))].
    right; right; right; right; right; right. exists (p, c). split; [exact Hin|]. cbn [fst snd]. unfold in_shadow_of. split; apply PMKB.S_mono; lia.
Qed.

Lemma blk_facts (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (scfg : SpuriousCfg) (HI : asan_iface) (HIok : HAJ.asan_iface_okR L ar C scfg HI)
      LBx FFx LKx crx Ax Mx Vx p c :
  ri_inv HI LBx FFx LKx crx Ax Mx Vx -> In (p, c) LBx ->
  4096 <= p /\ p mod 16 = 0 /\ 0 < c /\ p + c <= ahl_ceil ar /\ (p + c <= BIGSHADOW_LO \/ BIGSHADOW_HI <= p) /\ p + c <= 2 ^ 47
  /\ (p + c <= hl_img_lo L \/ hl_img_hi L <= p) /\ fframes_apart p c (FFx ++ LKx).
Proof.
  intros HH Hin. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
  pose proof (WB (p, c) Hin) as ((P0 & P1 & P3 & P4 & P5 & P6) & _ & _ & _ & _ & PFA & _). cbn [fst snd] in *. unfold app_mem in P6.
  split; [lia|]. split; [exact P3|]. split; [exact P4|]. split; [exact P5|]. split; [tauto|]. split; [tauto|]. split; [exact P1| exact PFA].
Qed.
End PEBHK.
