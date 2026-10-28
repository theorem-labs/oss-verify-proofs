(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct AxSymExec3Sound HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b PmSpecsA_b PnSpecsAa_b PmModelFactsA_b PnStepA_b XIcptAs0_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import XIcptA_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMARZK.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).

(* [comment removed for export] *)
Lemma aacc_zero (M : word -> option byte) p n : 0 <= p -> 0 < n -> aacc M p n ->
  forall x, 0x7fff8000 + p / 8 <= x < 0x7fff8000 + (p + n - 1) / 8 -> byte_at M x 0.
Proof.
  intros Hp Hn AC x Hx. set (a := 8 * (x - 0x7fff8000) + 7).
  pose proof (Z.div_mod p 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound p 8 ltac:(lia)) as R1.
  pose proof (Z.div_mod (p + n - 1) 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)) as R2.
  assert (Ha : p <= a < p + n) by (unfold a; lia).
  assert (Sa : HeapIfaceA.S a = x).
  { unfold HeapIfaceA.S, HeapIfaceA.SB, a. replace (8 * (x - 2147450880) + 7) with (7 + (x - 2147450880) * 8) by ring. rewrite Z.div_add by lia. change (7 / 8) with 0. lia. }
  assert (Ma : a mod 8 = 7).
  { unfold a. replace (8 * (x - 2147450880) + 7) with (7 + (x - 2147450880) * 8) by ring. rewrite Z.mod_add by lia. reflexivity. }
  destruct (AC a Ha) as [Z0 | (v & Bv & Rv & Lv)]; [rewrite Sa in Z0; exact Z0 | lia].
Qed.
Lemma aacc_last (M : word -> option byte) p n : 0 < n -> aacc M p n ->
  exists k, byte_at M (0x7fff8000 + (p + n - 1) / 8) k /\ (k = 0 \/ (p + n - 1) mod 8 < k <= 7).
Proof.
  intros Hn AC. destruct (AC (p + n - 1) ltac:(lia)) as [Z0 | (v & Bv & Rv & Lv)]; unfold HeapIfaceA.S, HeapIfaceA.SB in *.
  - exists 0. split; [rewrite Z.add_comm; exact Z0 | left; reflexivity].
  - exists v. split; [rewrite Z.add_comm; exact Bv | right; lia].
Qed.
Lemma page_base_word x y : 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> x / 4096 = y / 4096 -> page_base (Z_to_bv 64 x) = page_base (Z_to_bv 64 y).
Proof.
  intros Hx Hy E. unfold page_base, page_base_of, page_size. rewrite !L5.unsigned_lit by lia. rewrite E. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma ahid_page (Aw : list (Z * Z)) (model : Model) x y : 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> x / 4096 = y / 4096 ->
  ahid Aw model (Z_to_bv 64 x) = ahid Aw model (Z_to_bv 64 y).
Proof. intros Hx Hy E. unfold ahid, mkH. rewrite (page_base_word x y Hx Hy E). reflexivity. Qed.

(* [comment removed for export] *)
Lemma shadow_okV (H0 : word -> bool) (M : word -> option byte) p n :
  (forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> x / 4096 = y / 4096 -> H0 (Z_to_bv 64 x) = H0 (Z_to_bv 64 y)) ->
  0 <= p -> 0 < n -> p + n <= 2 ^ 47 -> aacc M p n ->
  L5A.avis H0 (0x7fff8000 + p / 8) ((p + n - 1) / 8 - p / 8 + 1) ->
  (forall x, 8 * ((0x7fff8000 + p / 8) / 8) <= x < 8 * ((0x7fff8000 + (p + n - 1) / 8) / 8) + 8 -> M (Z_to_bv 64 x) <> None) ->
  XIA.shadow_ok (mrestrict H0 M) p n.
Proof.
  intros HP Hp Hn Hpn AC AV SD. unfold XIA.shadow_ok, XIA.SB.
  assert (Q1 : 0 <= p / 8). { apply Z.div_pos; lia. }
  assert (Q2 : (p + n - 1) / 8 < 2 ^ 44). { apply Z.div_lt_upper_bound; lia. }
  assert (Q3 : p / 8 <= (p + n - 1) / 8). { apply Z.div_le_mono; lia. }
  assert (VIS : forall x, 0x7fff8000 + p / 8 <= x <= 0x7fff8000 + (p + n - 1) / 8 -> H0 (Z_to_bv 64 x) = false).
  { intros x Hx. replace x with (0x7fff8000 + p / 8 + (x - (0x7fff8000 + p / 8))) by lia. apply AV. lia. }
  split; [|split].
  - intros x Hx. pose proof (bv_unsigned_in_range 64 x) as Rx. change (bv_modulus 64) with (2 ^ 64) in Rx.
    rewrite <- (Z_to_bv_bv_unsigned 64 x). rewrite (mrestrict_visible H0 M); [| apply VIS; lia].
    exact (aacc_zero M p n Hp Hn AC (bv_unsigned x) Hx).
  - destruct (aacc_last M p n Hn AC) as (k & Bk & Rk). exists k. split; [| exact Rk].
    rewrite (mrestrict_visible H0 M); [exact Bk| apply VIS; lia].
  - intros Hn64 x Hx. pose proof (bv_unsigned_in_range 64 x) as Rx. change (bv_modulus 64) with (2 ^ 64) in Rx.
    rewrite <- (Z_to_bv_bv_unsigned 64 x). set (u := bv_unsigned x) in *.
    assert (W1 : 8 * ((0x7fff8000 + p / 8) / 8) <= 0x7fff8000 + p / 8) by (pose proof (Z.mul_div_le (0x7fff8000 + p / 8) 8); lia).
    assert (W2 : 0x7fff8000 + (p + n - 1) / 8 < 8 * ((0x7fff8000 + (p + n - 1) / 8) / 8) + 8).
    { pose proof (Z.div_mod (0x7fff8000 + (p + n - 1) / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (0x7fff8000 + (p + n - 1) / 8) 8 ltac:(lia)). lia. }
    assert (HV : H0 (Z_to_bv 64 u) = false).
    { destruct (Z_lt_le_dec u (0x7fff8000 + p / 8)) as [LT|GE].
      - rewrite (HP u (0x7fff8000 + p / 8)); [apply VIS; lia| lia| lia|].
        assert (E1 : u / 8 = (0x7fff8000 + p / 8) / 8).
        { pose proof (Z.div_mod u 8 ltac:(lia)). pose proof (Z.mod_pos_bound u 8 ltac:(lia)).
          pose proof (Z.div_mod (0x7fff8000 + p / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (0x7fff8000 + p / 8) 8 ltac:(lia)). lia. }
        change 4096 with (8 * 512). rewrite <- !Z.div_div by lia. rewrite E1. reflexivity.
      - destruct (Z_le_gt_dec u (0x7fff8000 + (p + n - 1) / 8)) as [LE|GT]; [apply VIS; lia|].
        rewrite (HP u (0x7fff8000 + (p + n - 1) / 8)); [apply VIS; lia| lia| lia|].
        assert (E1 : u / 8 = (0x7fff8000 + (p + n - 1) / 8) / 8).
        { pose proof (Z.div_mod u 8 ltac:(lia)). pose proof (Z.mod_pos_bound u 8 ltac:(lia)).
          pose proof (Z.div_mod (0x7fff8000 + (p + n - 1) / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (0x7fff8000 + (p + n - 1) / 8) 8 ltac:(lia)). lia. }
        change 4096 with (8 * 512). rewrite <- !Z.div_div by lia. rewrite E1. reflexivity. }
    rewrite (mrestrict_visible H0 M _ HV). apply SD. exact Hx.
Qed.

(* [comment removed for export] *)
Lemma shadow_words_mapped (M : word -> option byte) p n :
  (forall x, (LOWSH_LO <= x < LOWSH_HI \/ HIGHSH_LO <= x < HIGHSH_HI) -> M (Z_to_bv 64 x) <> None) ->
  0 < n -> XIA.app8 p n ->
  forall x, 8 * ((0x7fff8000 + p / 8) / 8) <= x < 8 * ((0x7fff8000 + (p + n - 1) / 8) / 8) + 8 -> M (Z_to_bv 64 x) <> None.
Proof.
  intros SD Hn AP x Hx. apply SD. unfold XIA.app8, XIA.LOWEND, XIA.HIGHBEG, XIA.HIGHEND in AP. unfold LOWSH_LO, LOWSH_HI, HIGHSH_LO, HIGHSH_HI.
  assert (U1 : 8 * ((0x7fff8000 + (p + n - 1) / 8) / 8) + 8 <= 0x7fff8000 + (p + n - 1) / 8 + 8).
  { pose proof (Z.mul_div_le (0x7fff8000 + (p + n - 1) / 8) 8). lia. }
  destruct AP as [(A0 & A1) | (A0 & A1)].
  - left. assert (L1 : 0x7fff8000 <= 8 * ((0x7fff8000 + p / 8) / 8)).
    { assert (0x7fff8000 = 8 * (0x7fff8000 / 8)) by reflexivity. assert (0x7fff8000 / 8 <= (0x7fff8000 + p / 8) / 8) by (apply Z.div_le_mono; [lia| pose proof (Z.div_pos p 8); lia]). lia. }
    assert (L2 : (p + n - 1) / 8 <= (0x7fff7fff - 9) / 8) by (apply Z.div_le_mono; lia).
    assert (L3 : 8 * ((0x7fff8000 + (p + n - 1) / 8) / 8) <= 0x7fff8000 + (p + n - 1) / 8) by (apply Z.mul_div_le; lia).
    change ((0x7fff7fff - 9) / 8) with 268431358 in L2. lia.
  - right. assert (L1 : 0x2008fff7000 <= 8 * ((0x7fff8000 + p / 8) / 8)).
    { assert (0x2008fff7000 = 8 * (0x2008fff7000 / 8)) by reflexivity. assert (0x2008fff7000 / 8 <= (0x7fff8000 + p / 8) / 8).
      { apply Z.div_le_mono; [lia|]. assert (0x10007fff8000 / 8 <= p / 8) by (apply Z.div_le_mono; lia). change (0x10007fff8000 / 8) with 2199291686912 in *. lia. }
      lia. }
    assert (L2 : (p + n - 1) / 8 <= (0x7fffffffffff - 9) / 8) by (apply Z.div_le_mono; lia).
    assert (L3 : 8 * ((0x7fff8000 + (p + n - 1) / 8) / 8) <= 0x7fff8000 + (p + n - 1) / 8) by (apply Z.mul_div_le; lia).
    change ((0x7fffffffffff - 9) / 8) with 17592186044414 in L2. lia.
Qed.

(* [comment removed for export] *)
Lemma fill_msteps (fx : FPState) R (MV : word -> option byte) (pd m sp r : Z) :
  getr R (reg 1) = Z_to_bv 64 r -> L5.ra_ok r -> getr R (reg 2) = Z_to_bv 64 sp -> getr R (reg 10) = Z_to_bv 64 pd -> getr R (reg 12) = Z_to_bv 64 m ->
  1 <= m <= 2 ^ 40 -> XIA.app8 pd m -> 0x1000000 <= sp - 2560 -> sp < 2 ^ 64 -> 0x7fff8000 + (pd + m - 1) / 8 + 8 <= sp - 2560 ->
  (pd + m <= sp - 2560 \/ sp <= pd) ->
  L5.writable RSEGS MV (sp - 2560) 2560 -> L5.writable RSEGS MV pd m -> XIA.cells_ok RSEGS XIA.AS0_CELLS MV -> XIA.shadow_ok MV pd m ->
  exists R3 M3, msteps RSEGS (st fx R 0x77c88 MV) (st fx R3 r M3) /\ mem_grows MV M3
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (pd <= a < pd + m) -> ~ (sp - 2560 <= a < sp) -> M3 (Z_to_bv 64 a) = MV (Z_to_bv 64 a))
    /\ L5.defined M3 pd m
    /\ (forall i, In i L5K.CS -> getr R3 (reg i) = getr R (reg i)) /\ getr R3 (reg 10) = Z_to_bv 64 pd.
Proof.
  intros H1 RA H2 H10 H12 Hm AP S0 S1 S2 S3 WS WD CO SO.
  assert (P0 : 0 <= pd /\ pd + m + 8 <= 2 ^ 47) by (unfold XIA.app8, XIA.LOWEND, XIA.HIGHBEG, XIA.HIGHEND in AP; lia).
  destruct (as0_icpt_fill fx MV (getr R (reg 11)) pd m sp R (Z_to_bv 64 r) Hm AP S0 S1 S2 S3) as (R3 & Mj & MS & KO & A10 & FZ & MG).
  { replace (Z_to_bv 64 (sp - XIA.SCR)) with (Z_to_bv 64 (sp - 2560 + 0)) by (f_equal; unfold XIA.SCR; lia).
    replace (Z.to_nat XIA.SCR) with (Z.to_nat 2560) by reflexivity. apply WS; lia. }
  { replace (Z_to_bv 64 pd) with (Z_to_bv 64 (pd + 0)) by (f_equal; lia). apply WD; lia. }
  { exact CO. } { exact SO. } { exact (L5K.ret_ok_lit r RA). } { exact H1. } { exact H2. } { exact H10. } { reflexivity. } { exact H12. }
  set (bs := repeat (Z_to_bv 8 (bv_unsigned (getr R (reg 11)))) (Z.to_nat m)) in *.
  assert (LEN : length bs = Z.to_nat m) by (unfold bs; apply repeat_length).
  exists R3, (wbytes Mj (Z_to_bv 64 pd) bs). split; [exact MS|].
  split. { intros x Hx. apply (wbytes_grows bs Mj (Z_to_bv 64 pd)). apply MG. exact Hx. }
  split.
  { intros a Ha Hout Hsc. destruct (Z_lt_le_dec a pd) as [Lo|Hi].
    - rewrite wbytes_below by (rewrite !L5.unsigned_lit by lia; lia). apply FZ. rewrite L5.unsigned_lit by lia. unfold XIA.SCR. lia.
    - rewrite wbytes_above by (rewrite !L5.unsigned_lit by lia; rewrite LEN, Z2Nat.id by lia; lia). apply FZ. rewrite L5.unsigned_lit by lia. unfold XIA.SCR. lia. }
  split.
  { intros i Hi. replace (pd + i) with (bv_unsigned (Z_to_bv 64 pd) + Z.of_nat (Z.to_nat i)) by (rewrite L5.unsigned_lit by lia; lia).
    rewrite AX2S.wbytes_nth; [discriminate| rewrite L5.unsigned_lit by lia; lia| rewrite LEN; lia]. }
  split; [intros i Hi; apply (L5K.kept_ok_index R R3 i KO Hi)| exact A10].
Qed.

(* [comment removed for export] *)
Lemma agsh_frame (M M1 : word -> option byte) (P : Z -> Prop) a n :
  (forall x, 0 <= x < 2 ^ 64 -> ~ P x -> M1 (Z_to_bv 64 x) = M (Z_to_bv 64 x)) ->
  (forall x, P x -> x < BIGSHADOW_LO \/ BIGSHADOW_HI <= x) -> 0 <= a -> a + n <= 2 ^ 47 -> PMFA.agsh M M1 a n.
Proof.
  intros FR PX H0 H1 x Hx. pose proof (PMKA.S_in_shadow x ltac:(lia)) as SX. unfold BIGSHADOW_LO, BIGSHADOW_HI in SX.
  apply FR; [unfold HeapIfaceA.S, HeapIfaceA.SB in *; lia|]. intros X. specialize (PX _ X). unfold BIGSHADOW_LO, BIGSHADOW_HI in PX. lia.
Qed.

Section Kit.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.

Lemma in3_of_existsb (c : Z * Z * Z) (l : list (Z * Z * Z)) :
  existsb (fun d => (Z.eqb (fst (fst d)) (fst (fst c)) && Z.eqb (snd (fst d)) (snd (fst c)) && Z.eqb (snd d) (snd c))%bool) l = true -> In c l.
Proof.
  intros E. apply existsb_exists in E as (d & Hd & E). destruct c as [[a w] v], d as [[a' w'] v']. cbn in E.
  apply andb_true_iff in E as [E E3]. apply andb_true_iff in E as [E1 E2]. apply Z.eqb_eq in E1, E2, E3. subst. exact Hd.
Qed.

(* [comment removed for export] *)
Lemma cells_okV LB FF LK cr Aw M model : ri_inv HI LB FF LK cr Aw M (vml_of model) -> XIA.cells_ok RSEGS XIA.AS0_CELLS (mrestrict (ahid Aw model) M).
Proof.
  intros HH. pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M model HH) as (_ & _ & VIMG & _).
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & CS). rewrite (L5A.aly_segs L C LYa) in CS. rewrite Forall_forall in CS.
  unfold XIA.cells_ok. rewrite Forall_forall. intros [[a w] v] Hin.
  assert (D4 : In (a, Z.of_nat w, v) L5A.AS0_ALY_CELLS_D4 /\ 0 <= a /\ a + Z.of_nat w <= 0x696000).
  { cbn [XIA.AS0_CELLS] in Hin. unfold XIA.SB, XIA.HIGHEND in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E; intros <- <- <-; split; [apply in3_of_existsb; vm_compute; reflexivity| cbn; lia]|]). destruct Hin. }
  destruct D4 as (D4 & Ha & Hw).
  pose proof (CS (a, Z.of_nat w, v) (L5A.aly_cells L C LYa _ D4)) as X. cbn [fst snd] in X. unfold cell_is in X. rewrite Nat2Z.id in X.
  rewrite (rdn_mrestrict_eq RSEGS (ahid Aw model) w M _); [exact X|].
  apply L5A.range_avoids_of_avis; [apply VIMG; lia| lia| lia].
Qed.
(* [comment removed for export] *)
Lemma agsh_ahpres LB' FF sp scr W M M1 q A :
  L5CA.ahpres L ar LB' FF sp scr W M M1 -> In (q, A) LB' -> PMKA.wapp W -> 0 <= q -> q + A <= 2 ^ 47 -> PMFA.agsh M M1 q A.
Proof.
  intros (P & _ & _) Hin WA H0 H1 x Hx. pose proof (PMKA.S_in_shadow x ltac:(lia)) as SX.
  apply P. split; [unfold BIGSHADOW_LO, BIGSHADOW_HI in SX; unfold HeapIfaceA.S, HeapIfaceA.SB in *; lia|]. split.
  - unfold aclient, aclient_g. do 6 right. exists (q, A). split; [exact Hin|]. cbn [fst snd]. unfold in_shadow_of. split; apply PMKA.S_mono; lia.
  - apply PMKA.wapp_outside_shadow; [exact WA| exact SX].
Qed.

(* [comment removed for export] *)
Lemma in_shadow_sub a n a' n' x : a <= a' -> a' + n' <= a + n -> 0 < n' -> in_shadow_of a' n' x -> in_shadow_of a n x.
Proof. intros H1 H2 H3 [X1 X2]. unfold in_shadow_of. split; eapply Z.le_trans; [| exact X1| exact X2|]; apply PMKA.S_mono; lia. Qed.

(* [comment removed for export] *)
Lemma fill_stage_pre LB' FF LK cr Aw M model (fx0 fx : FPState) R0 (pc0 : Z) R (pd m sp r : Z) K :
  ri_inv HI LB' FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model ->
  msteps RSEGS (st fx0 R0 pc0 (mrestrict (ahid Aw model) M)) (st fx R 0x77c88 (mrestrict (ahid Aw model) M)) ->
  (forall x, (LOWSH_LO <= x < LOWSH_HI \/ HIGHSH_LO <= x < HIGHSH_HI) -> M (Z_to_bv 64 x) <> None) ->
  getr R (reg 1) = Z_to_bv 64 r -> L5.ra_ok r -> getr R (reg 2) = Z_to_bv 64 sp -> getr R (reg 10) = Z_to_bv 64 pd -> getr R (reg 12) = Z_to_bv 64 m ->
  1 <= m <= 2 ^ 27 ->
  ahl_ceil ar + 4096 <= sp - 2560 -> sp <= ar_sptop ar -> L5.defined M (sp - 2560) 2560 ->
  ((exists q A0, In (q, A0) LB' /\ q <= pd /\ pd + m <= q + A0) \/ (exists o' sz', L5CA.aobj FF o' sz' /\ 0 < sz' /\ sz' mod 8 = 0 /\ o' <= pd /\ pd + m <= o' + sz')) ->
  L5.defined M pd m -> aacc M pd m ->
  (forall (R1 : bvmap 5 word) M1 model1, ri_inv HI LB' FF LK cr Aw M1 (vml_of model1) -> L5CA.amodel_ok Aw model1 -> model_rt model model1 -> ahid Aw model1 = ahid Aw model ->
     mem_grows M M1 -> (forall a, 0 <= a < 2 ^ 64 -> ~ (pd <= a < pd + m) -> ~ (sp - 2560 <= a < sp) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
     L5.defined M1 pd m -> (forall i, In i L5K.CS -> getr R1 (reg i) = getr R (reg i)) -> getr R1 (reg 10) = Z_to_bv 64 pd ->
     srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R1 r M1 model1) K) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx0 R0 pc0 M model) K.
Proof.
  intros HH AM PRE SDEF H1 RA H2 H10 H12 Hm SC1 SC2 SCD CONT DD ACC KONT.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & FSSH & STSH & _ & SPB & TOP & _).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB' FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  set (H0 := ahid Aw model) in *. set (MV := mrestrict H0 M) in *.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in FSIMG.
  unfold app_mem, FS_BYTES, BIGSHADOW_LO, BIGSHADOW_HI in FSAPP, FSCEIL, FSIMG.
  destruct SPB as (_ & _ & TOP1 & _).
  (* [comment removed for export] *)
  assert (DST : (0 <= pd /\ (pd + m <= 0x7fff7000 \/ 0x10007fff8000 <= pd) /\ pd + m <= ahl_ceil ar /\ (pd + m <= 0x10000 \/ 0x696000 <= pd))
                /\ L5A.avis H0 pd m /\ L5A.avis H0 (0x7fff8000 + pd / 8) ((pd + m - 1) / 8 - pd / 8 + 1)
                /\ (forall i, 0 <= i < m -> aclientw L ar LB' FF 0 0 (pd + i))).
  { destruct CONT as [(q & A0 & Hin & X1 & X2)|(o' & sz' & AO & Hsz & Hsz8 & X1 & X2)].
    - destruct (WB (q, A0) Hin) as ((B0 & B1 & B2 & B3 & B4 & B5) & _ & _ & SA & _). cbn [fst snd] in *.
      rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in B1. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in B5.
      split; [lia|]. split; [apply (VBLK q A0); [exact Hin| lia| lia]|]. split.
      + apply (VBSH q A0 _ _ Hin). intros i Hi. unfold in_shadow_of, HeapIfaceA.S, HeapIfaceA.SB.
        assert (q / 8 <= pd / 8) by (apply Z.div_le_mono; lia). assert ((pd + m - 1) / 8 <= (q + A0 - 1) / 8) by (apply Z.div_le_mono; lia). lia.
      + intros i Hi. apply (L5SAR.block_client L ar LB' FF 0 0 q A0); [exact Hin| lia].
    - pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB' FF LK cr Aw M model o' sz' 0 0 HH AO Hsz Hsz8) as ((O1 & O2 & O3 & O4 & O5) & OBIG & _ & OVIS & _ & _ & _).
      destruct AO as (f & Hf & F1 & F2 & F3). destruct (WF f Hf) as (Y1 & Y2 & _). unfold FS_BYTES in Y2.
      split; [lia|]. split; [eapply L5A.avis_sub; [exact OVIS| lia| lia]|]. split.
      + apply VFSSH. intros i Hi. unfold in_shadow_of, HeapIfaceA.S, HeapIfaceA.SB, FS_BYTES.
        assert (ar_fs ar / 8 <= pd / 8) by (apply Z.div_le_mono; lia). assert ((pd + m - 1) / 8 <= (ar_fs ar + 11571200 - 1) / 8) by (apply Z.div_le_mono; lia). lia.
      + intros i Hi. apply (L5SAR.obj_client L ar LB' FF 0 0 o' sz'); [exists f; split; [exact Hf| lia]| lia]. }
  destruct DST as ((D0 & D1 & D2 & D3) & DVIS & DSVIS & DCW).
  assert (AP : XIA.app8 pd m) by (unfold XIA.app8, XIA.LOWEND, XIA.HIGHBEG, XIA.HIGHEND; lia).
  assert (SVIS : L5A.avis H0 (sp - 2560) 2560) by (apply VIS; lia).
  assert (WSV : L5.writable RSEGS MV (sp - 2560) 2560).
  { apply (proj2 (L5A.writable_vis H0 M (sp - 2560) 2560 SVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS); [exact SCD| lia| lia]. }
  assert (WDV : L5.writable RSEGS MV pd m).
  { apply (proj2 (L5A.writable_vis H0 M pd m DVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS); [exact DD| lia| lia]. }
  assert (CO : XIA.cells_ok RSEGS XIA.AS0_CELLS MV) by exact (cells_okV LB' FF LK cr Aw M model HH).
  assert (SO : XIA.shadow_ok MV pd m).
  { apply shadow_okV; [intros x y Hx Hy E; exact (ahid_page Aw model x y Hx Hy E)| lia| lia| lia| exact ACC| exact DSVIS|].
    apply (shadow_words_mapped M pd m SDEF ltac:(lia) AP). }
  assert (Q1 : 0x7fff8000 + (pd + m - 1) / 8 + 8 <= sp - 2560).
  { assert ((pd + m - 1) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia. }
  destruct (fill_msteps fx R MV pd m sp r H1 RA H2 H10 H12 ltac:(lia) AP ltac:(lia) ltac:(lia) Q1 ltac:(lia) WSV WDV CO SO)
    as (R3 & M3v & MS & MG & FZ & DEF3 & KS & A10).
  set (W := fun a => (pd <= a < pd + m) \/ (sp - 2560 <= a < sp)).
  apply (L5SAR.apiece L ar C HI LYa HIok LB' FF LK cr Aw M model fx0 fx R0 pc0 R3 r M3v W K HH AM (msteps_trans _ _ _ _ PRE MS) MG).
  { intros a Ha NW. apply FZ; [exact Ha| intros X; apply NW; left; exact X| intros X; apply NW; right; exact X]. }
  { intros a Ha [Wa|Wa].
    - split; [replace a with (pd + (a - pd)) by lia; apply DCW; lia| lia].
    - split; [|lia]. apply (L5SAR.stack_client L ar LB' FF 0 0 a); lia. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
  apply (KONT R3 M1 model1 HH1 AM1 MRT1 HID1 MGM1).
  - intros a Ha N1 N2. apply FR1; [exact Ha| intros [X|X]; [exact (N1 X)| exact (N2 X)]].
  - rewrite <- VIS1 in DEF3. exact (proj1 (L5A.defined_vis H0 M1 pd m DVIS) DEF3).
  - exact KS.
  - exact A10.
Qed.
Lemma fill_stage LB' FF LK cr Aw M model (fx : FPState) R (pd m sp r : Z) K :
  ri_inv HI LB' FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model ->
  (forall x, (LOWSH_LO <= x < LOWSH_HI \/ HIGHSH_LO <= x < HIGHSH_HI) -> M (Z_to_bv 64 x) <> None) ->
  getr R (reg 1) = Z_to_bv 64 r -> L5.ra_ok r -> getr R (reg 2) = Z_to_bv 64 sp -> getr R (reg 10) = Z_to_bv 64 pd -> getr R (reg 12) = Z_to_bv 64 m ->
  1 <= m <= 2 ^ 27 ->
  ahl_ceil ar + 4096 <= sp - 2560 -> sp <= ar_sptop ar -> L5.defined M (sp - 2560) 2560 ->
  ((exists q A0, In (q, A0) LB' /\ q <= pd /\ pd + m <= q + A0) \/ (exists o' sz', L5CA.aobj FF o' sz' /\ 0 < sz' /\ sz' mod 8 = 0 /\ o' <= pd /\ pd + m <= o' + sz')) ->
  L5.defined M pd m -> aacc M pd m ->
  (forall (R1 : bvmap 5 word) M1 model1, ri_inv HI LB' FF LK cr Aw M1 (vml_of model1) -> L5CA.amodel_ok Aw model1 -> model_rt model model1 -> ahid Aw model1 = ahid Aw model ->
     mem_grows M M1 -> (forall a, 0 <= a < 2 ^ 64 -> ~ (pd <= a < pd + m) -> ~ (sp - 2560 <= a < sp) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
     L5.defined M1 pd m -> (forall i, In i L5K.CS -> getr R1 (reg i) = getr R (reg i)) -> getr R1 (reg 10) = Z_to_bv 64 pd ->
     srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R1 r M1 model1) K) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0x77c88 M model) K.
Proof. intros HH AM. apply (fill_stage_pre LB' FF LK cr Aw M model fx fx R 0x77c88 R pd m sp r K HH AM (mst_refl _ _)). Qed.
(* [comment removed for export] *)
Lemma move_stage_pre (IL : icpt_layout) (ICok : aicpt_ok L ar IL SCFG HI) (ILY : as0_icpt_layout IL)
      LB' FF LK cr Aw M model (fx0 fx : FPState) R0 (pc0 : Z) R (dst src len sp r : Z) K :
  ri_inv HI LB' FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
  msteps RSEGS (st fx0 R0 pc0 (mrestrict (ahid Aw model) M)) (st fx R 0x77c8c (mrestrict (ahid Aw model) M)) ->
  getr R (reg 1) = Z_to_bv 64 r -> L5.ra_ok r -> getr R (reg 2) = Z_to_bv 64 sp -> getr R (reg 4) = Z_to_bv 64 (hl_tp L) ->
  getr R (reg 10) = Z_to_bv 64 dst -> getr R (reg 11) = Z_to_bv 64 src -> getr R (reg 12) = Z_to_bv 64 len ->
  0 <= len <= 2 ^ 27 -> L5CA.astk ar M sp 2560 ->
  (exists q A0, In (q, A0) LB' /\ q <= dst /\ dst + len <= q + A0) -> L5.defined M dst len -> aacc M dst len ->
  ((exists q A0, In (q, A0) LB' /\ q <= src /\ src + len <= q + A0) \/ (exists o' sz', L5CA.aobj FF o' sz' /\ o' <= src /\ src + len <= o' + sz')) ->
  L5.defined M src len -> aacc M src len ->
  (dst + len <= src \/ src + len <= dst) ->
  (forall (R1 : bvmap 5 word) M1 model1, regs_preserved R R1 -> getr R1 (reg 10) = Z_to_bv 64 dst ->
     (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB' FF sp 2560 a -> ~ (dst <= a < dst + len) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
     (forall a, sp - 2560 <= a < sp -> M1 (Z_to_bv 64 a) <> None) -> L5.defined M1 dst len ->
     model_rt model model1 -> L5CA.amodel_ok Aw model1 -> ri_inv HI LB' FF LK cr Aw M1 (vml_of model1) ->
     srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R1 r M1 model1) K) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx0 R0 pc0 M model) K.
Proof.
  intros HH AM K0 PRE H1 RA H2 H4 H10 H11 H12 Hlen STK DC DD DA SC SD SA OVL KONT.
  pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _).
  destruct DC as (qd & Ad & Hind & D1 & D2).
  destruct (WB (qd, Ad) Hind) as ((Q0 & Q1 & Q2 & Q3 & Q4 & Q5) & _). cbn [fst snd] in *. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Q5.
  assert (SRCB : 0 <= src /\ src + len <= ahl_ceil ar /\ app_rng ar src len /\ (forall i, 0 <= i < len -> aclient L ar LB' FF sp 2560 (src + i))).
  { destruct SC as [(qs & As & Hins & X1 & X2)|(o' & sz' & AO & X1 & X2)].
    - destruct (WB (qs, As) Hins) as ((P0 & P1 & P2 & P3 & P4 & P5) & _). cbn [fst snd] in *.
      split; [lia|]. split; [lia|]. split; [apply (L5SAR.app_rng_block L ar C HI HIok LB' FF LK cr Aw M _ qs As src len HH Hins X1 X2)|].
      intros i Hi. apply (L5SAR.block_client L ar LB' FF sp 2560 qs As); [exact Hins| lia].
    - pose proof AO as (f & Hf & F1 & F2 & F3). destruct (WF f Hf) as (Y1 & Y2 & _). unfold app_mem, FS_BYTES in FSAPP, Y2. unfold FS_BYTES in FSCEIL.
      split; [lia|]. split; [lia|]. split; [apply (L5SAR.app_rng_aobj L ar C HI HIok LB' FF LK cr Aw M _ o' sz' src len HH AO X1 X2)|].
      intros i Hi. apply (L5SAR.obj_client L ar LB' FF sp 2560 o' sz'); [exact AO| lia]. }
  destruct SRCB as (S0 & S1 & SAR & SCL).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok LB' FF LK cr Aw M model fx0 fx R0 pc0 R 0x77c8c _ K HH AM PRE (fun x X => X) (fun a _ => eq_refl)).
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
  assert (EM : M1 = M).
  { apply functional_extensionality. intros x. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply FR1. pose proof (bv_unsigned_in_range 64 x) as X.
    change (bv_modulus 64) with (2 ^ 64) in X. exact X. }
  subst M1. pose proof AM1 as (Mh1 & MI1).
  pose proof (aic_memmove_libc _ _ _ _ _ ICok) as MMV. unfold amemmove_libc_spec, amemcpy_spec_at, amem_pre, amem_post in MMV.
  rewrite (aicl_memmove IL ILY), (L5A.aly_segs L C LYa), (L5A.aly_scr_mem L C LYa) in MMV.
  destruct (AX2S.rdn_defined RSEGS M (Z.to_nat len) (Z_to_bv 64 src)) as (bs & RDN & LEN).
  { rewrite L5.unsigned_lit by lia. lia. }
  { intros j Hj. unfold AX2S.rd1. rewrite L5.unsigned_lit by lia. specialize (SD (Z.of_nat j) ltac:(lia)). destruct (M _); [discriminate| exfalso; exact (SD eq_refl)]. }
  assert (U2 : bv_unsigned (getr R 2%bv) = sp).
  { rewrite L5K.rl2, H2. apply L5.unsigned_lit. lia. }
  apply (MMV fx R M model1 LB' FF LK cr Aw dst src len bs K); clear MMV.
  - split; [exact HH1|]. split; [exact Mh1|]. split; [exact MI1|].
    split; [rewrite L5K.rl10; exact H10|]. split; [rewrite L5K.rl12; exact H12|]. split; [lia|].
    split; [rewrite L5K.rl4; exact H4|].
    split; [rewrite L5K.rl1, H1; apply L5K.ret_ok_lit; exact RA|].
    split; [rewrite U2; pose proof (L5SAR.astack_ok_of_astk L ar C LYa M M sp 2560 0 2560 STK (fun x X => X) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite Z.sub_0_r; exact A16)) as AS0;
            rewrite Z.sub_0_r in AS0; exact AS0|].
    split; [exact DA|].
    split; [intros i Hi; rewrite U2; apply (L5SAR.block_client L ar LB' FF sp 2560 qd Ad); [exact Hind| lia]|].
    split; [intros i m Hi Hm; apply (L5C.writable_of_defined RSEGS M dst len DD); lia|].
    split; [exact K0|]. apply (L5SAR.app_rng_block L ar C HI HIok LB' FF LK cr Aw M _ qd Ad dst len HH Hind D1 D2).
  - rewrite L5K.rl11. exact H11.
  - exact SA.
  - lia.
  - exact SAR.
  - intros i Hi. right. rewrite U2. apply SCL. exact Hi.
  - exact RDN.
  - intros _. exact OVL.
  - intros R' M' model' R10' RP BYTES PRES SDEF' RT MI' HH'. rewrite U2 in PRES, SDEF'. rewrite <- L5K.rl1 in H1. rewrite H1.
    apply (KONT R' M' model' RP ltac:(rewrite <- L5K.rl10; exact R10') PRES SDEF').
    + intros i Hi. destruct (BYTES i Hi) as (v & _ & Bv). unfold byte_at in Bv. rewrite Bv. discriminate.
    + exact (L5LZ.model_rt_trans model model1 model' MRT1 RT).
    + split; [rewrite (L5LZ.model_rt_halted _ _ RT); exact Mh1| exact MI'].
    + exact HH'.
Qed.
End Kit.
End PMARZK.
