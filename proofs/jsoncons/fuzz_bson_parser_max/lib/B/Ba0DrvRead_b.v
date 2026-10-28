(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanAcct.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StreamSim ShapeAlg SpinAlg Hoare MemSplit AsanAcctShape FileSim SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4
  RefNodes RefMemcpyLib HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import DrvKitA DrvNodesLazyK As0DrvKitA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0DrvEntry_b Ba0Drv_defs_b Ba0DrvLib_b
  Ba0RegionPoisoned_b Ba0AsanMemcpy_b Ba0ReadIcpt_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition RD_CELLS : list (Z * Z * Z) :=
  [(0x140918, 1, 1); (0x139318, 8, 0x130304);
   (0x1374c0, 8, 0x13fc38); (0x13fc38, 8, 0x7fff8000); (0x1374c8, 8, 0x140928); (0x140928, 8, 0); (0x1374d0, 8, 0x140930); (0x140930, 8, 0);
   (0x1374d8, 8, 0x140920); (0x140920, 8, 0x7fffffffffff)].

Definition STAGE : Z := 0x662290.
(* [comment removed for export] *)
Definition IMG_NOSTAGE : list (Z * Z) :=
  [(0x10000, 0x139000); (0x13bbe0, 0x13c580); (0x672290, 0x673ca8); (0x673cb0, 0x673cf8); (0x673d14, 0x673d28); (0x673d30, 0x6951b8);
   (0x6951c0, 0x696000)].
Definition keep_readA (so : Z) (bls : list (nat * Z)) (vbnd : list (nat * Z)) (kn : list kentry) : list kentry :=
  kn_keep 0 so 2200 bls vbnd [] IMG_NOSTAGE IMG_RW_A kn.

Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section ReadMem.
  (* [comment removed for export] *)
  Variable H : word -> bool.
  Variable M : word -> option byte.
  Variables (s : Z) (raw : word) (R : bvmap 5 word) (bs : list byte).
  Hypothesis Hs : 0x1000000 <= s - 2200 /\ s < 2 ^ 64.
  Hypothesis Hbs : Z.of_nat (length bs) <= 65536.
  Hypothesis Hvis_fr : forall x : word, s - 2200 <= bv_unsigned x < s -> H x = false.
  Hypothesis Hvis_st : forall x : word, STAGE <= bv_unsigned x < STAGE + 65536 -> H x = false.
  Hypothesis Hfar : STAGE + 65536 <= s - 2200.

  Let MV := mrestrict H M.
  Let Ma := RDA MV raw s R.
  Let M1 := munrestrict H M Ma.
  Let M2 := wbytes M1 (Z_to_bv 64 STAGE) bs.
  Let MV2 := mrestrict H M2.

  Definition rd_M1 := M1. Definition rd_M2 := M2. Definition rd_MV2 := MV2.

  Lemma rd_M1_restrict : mrestrict H M1 = Ma.
  Proof.
    apply mrestrict_munrestrict. intros a Ha. unfold Ma.
    destruct (Z_lt_le_dec (bv_unsigned a) (s - 2144)) as [L1|L1]; [rewrite (RDA_out MV raw s Hs R a) by lia; unfold MV, mrestrict; rewrite Ha; reflexivity|].
    destruct (Z_lt_le_dec (bv_unsigned a) s) as [L2|L2]; [rewrite (Hvis_fr a) in Ha by lia; discriminate|].
    rewrite (RDA_out MV raw s Hs R a) by lia. unfold MV, mrestrict. rewrite Ha. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma rd_M2_out : forall x : word, ~ (s - 2200 <= bv_unsigned x < s) -> ~ (STAGE <= bv_unsigned x < STAGE + 65536) -> M2 x = M x.
  Proof.
    intros x N1 N2. unfold M2. unfold STAGE in *.
    rewrite wbytes_out by (rewrite u_small by lia; lia).
    unfold M1, munrestrict. destruct (H x) eqn:Hx; [reflexivity|].
    unfold Ma. rewrite (RDA_out MV raw s Hs R x) by lia. unfold MV, mrestrict. rewrite Hx. reflexivity.
  Qed.
  Lemma rd_M2_grows : forall x : word, M x <> None -> M2 x <> None.
  Proof.
    intros x Hd. unfold M2. apply wbytes_grows. unfold M1, munrestrict. destruct (H x) eqn:Hx; [exact Hd|].
    unfold Ma. apply RDA_grows. unfold MV, mrestrict. rewrite Hx. exact Hd.
  Qed.
  Lemma rd_MV2_grows : mem_grows MV MV2.
  Proof.
    intros x Hd. unfold MV2, mrestrict. unfold MV, mrestrict in Hd. destruct (H x) eqn:Hx; [exact Hd|]. apply rd_M2_grows. exact Hd.
  Qed.
  (* [comment removed for export] *)
  Lemma rd_MV2_frames : forall x : word, s - 2200 <= bv_unsigned x < s -> MV2 x = Ma x.
  Proof.
    intros x Hx. unfold MV2, mrestrict. rewrite (Hvis_fr x Hx). unfold M2, STAGE in *.
    rewrite wbytes_out by (rewrite u_small by lia; lia).
    unfold M1, munrestrict. rewrite (Hvis_fr x Hx). reflexivity.
  Qed.
  Lemma rd_MV2_slot : forall k, 8 <= k <= 2200 -> rdn ASEGS MV2 (Z_to_bv 64 (s - k)) 8 = rdn ASEGS Ma (Z_to_bv 64 (s - k)) 8.
  Proof.
    intros k Hk. apply rdn_ext; [rewrite u_small by lia; cbn; lia|]. intros x Hx. rewrite u_small in Hx by lia. cbn in Hx.
    apply rd_MV2_frames. lia.
  Qed.
  Lemma rd_stage_bytes : rdn ASEGS M2 (Z_to_bv 64 STAGE) (length bs) = Some bs.
  Proof. unfold M2. apply rdn_wbytes_hit. unfold STAGE. rewrite u_small by lia. lia. Qed.
End ReadMem.

Section DrvRead.
  Variable L : asan_layout.
  Variable ar : asan_run.
  Variable C : asan_statics_cells.
  Variable IL : icpt_layout.
  Variable HI : asan_iface.
  Hypothesis HIok : asan_iface_okB L ar C scfg HI.
  Hypothesis ICok : aicpt_ok L ar IL scfg HI.
  Hypothesis ILY : as0_icpt_layout IL.
  Variable sp0 : word.
  Hypothesis Hsp : 0x7fff80000000 <= bv_unsigned sp0 <= 2 ^ 47.
  Hypothesis Hal : bv_unsigned sp0 mod 16 = 0.
  Hypothesis DL : drv_layoutA L ar IL sp0.
  Hypothesis Hcells : incl RD_CELLS (asc_cells C).
  Variable M0 : word -> option byte.
  Hypothesis M0_def : defined M0 (bv_unsigned sp0) (ar_stack_top ar - bv_unsigned sp0).

  #[local] Notation dinvA := (dinv ar HI sp0 M0).

  Lemma rd_cell : forall LB FF LK cr A M V a n v, ri_inv HI LB FF LK cr A M V -> In (a, n, v) RD_CELLS ->
    cell_is ASEGS M a (Z.to_nat n) v.
  Proof.
    intros LB FF LK cr A M V a n v HH Hin.
    destruct (aiob_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & CS). rewrite (dla_segs _ _ _ _ DL) in CS.
    exact (proj1 (Forall_forall _ _) CS (a, n, v) (Hcells _ Hin)).
  Qed.

  (* [comment removed for export] *)
  Lemma avoid_img : forall LB FF LK cr A M (model : Model) a (n : nat),
    ri_inv HI LB FF LK cr A M (vml_of model) -> 0 <= a -> a + Z.of_nat n <= 0x696000 ->
    range_avoids (ahid A model) (Z_to_bv 64 a) n.
  Proof.
    intros LB FF LK cr A M model a n HH Ha Hn k Hk. unfold woff. rewrite (u_small a) by lia.
    apply (vis_of_inv scfg L ar C IL HI HIok sp0 DL _ _ _ _ _ _ _ (a + Z.of_nat k) HH); lia.
  Qed.

  (* [comment removed for export] *)
  Lemma vis_of_allowed : forall A (model : Model) a n x, shadow_allowed A a n -> in_shadow_of a n x -> ahid A model (Z_to_bv 64 x) = false.
  Proof.
    intros A model a n x SA Hx. unfold ahid, mkH. rewrite (SA x Hx). apply andb_false_r.
  Qed.

  (* [comment removed for export] *)
  Lemma stage_shadow : forall LB FF LK cr A M (model : Model), ri_inv HI LB FF LK cr A M (vml_of model) ->
    forall x, in_shadow_of 0x662280 0x10050 x -> byte_at M x 0 /\ ahid A model (Z_to_bv 64 x) = false.
  Proof.
    intros LB FF LK cr A M model HH x Hx.
    destruct (aic_img_shadow _ _ _ _ _ ICok _ _ _ _ _ _ _ HH 0x662280 0x10050) as (Z0 & SA).
    - rewrite (dla_img_lo _ _ _ _ DL). lia.
    - rewrite (dla_img_hi _ _ _ _ DL). lia.
    - lia.
    - rewrite (aicl_poison IL ILY). repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
    - split; [exact (Z0 x Hx) | exact (vis_of_allowed A model _ _ x SA Hx)].
  Qed.

  Lemma w_lit : forall z (w : word), bv_unsigned w = z -> Z_to_bv 64 z = w.
  Proof. intros z w <-. apply Z_to_bv_bv_unsigned. Qed.

  (* [comment removed for export] *)
  Lemma rd_post : forall LB FF LK cr A M (model : Model) (s : Z) (raw : word) R R2 bs,
    let H := ahid A model in
    let MV2 := rd_MV2 H M s raw R bs in
    let n := Z.of_nat (length bs) in
    ri_inv HI LB FF LK cr A M (vml_of model) ->
    n <= 65536 -> bv_unsigned sp0 - 4194304 - 4096 <= s <= bv_unsigned sp0 ->
    store_ok ASEGS (mrestrict H M) (Z_to_bv 64 (s - 2200)) 2200 = true ->
    ret_ok raw ->
    getr R2 10 = Z_to_bv 64 n -> getr R2 2 = Z_to_bv 64 (s - 2144) -> getr R2 1 = (0x13032c%bv : word) ->
    getr R2 8 = Z_to_bv 64 s -> getr R2 9 = Z_to_bv 64 0x662290 -> getr R2 20 = Z_to_bv 64 1 ->
    exists R3 M3',
      msteps ASEGS (mkst R2 (0x12a8dc%bv : word) MV2 (seg_rom ASEGS)) (mkst R3 raw M3' (seg_rom ASEGS))
      /\ getr R3 10 = Z_to_bv 64 n /\ getr R3 2 = Z_to_bv 64 s /\ getr R3 1 = raw
      /\ getr R3 8 = getr R 8 /\ getr R3 9 = getr R 9 /\ getr R3 18 = getr R 18 /\ getr R3 19 = getr R 19 /\ getr R3 20 = getr R 20
      /\ keeps_but Ba0ReadIcpt_b.RIPL R2 R3
      /\ (forall x : word, ~ (s - 2200 <= bv_unsigned x < s) -> M3' x = MV2 x)
      /\ mem_grows MV2 M3'.
  Proof.
    intros LB FF LK cr A M model s raw R R2 bs H MV2 n HH Hn Hsr WOK Hret Q10 Q2 Q1 Q8 Q9 Q20.
    pose proof Hsp as Hsp'.
    assert (Hs : 0x1000000 <= s - 2200 /\ s < 2 ^ 64) by lia.
    assert (Hbs : Z.of_nat (length bs) <= 65536) by exact Hn.
    assert (VFR : forall x : word, s - 2200 <= bv_unsigned x < s -> H x = false).
    { intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply (vis_of_inv scfg L ar C IL HI HIok sp0 DL _ _ _ _ _ _ _ (bv_unsigned x) HH); lia. }
    assert (VST : forall x : word, STAGE <= bv_unsigned x < STAGE + 65536 -> H x = false).
    { intros x Hx. unfold STAGE in Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply (vis_of_inv scfg L ar C IL HI HIok sp0 DL _ _ _ _ _ _ _ (bv_unsigned x) HH); lia. }
    assert (Hfar : STAGE + 65536 <= s - 2200) by (unfold STAGE; lia).
    pose proof (RDA_slots (mrestrict H M) raw s Hs R) as (SL1 & SL2 & SL3 & SL4 & SL5 & SL6 & SL7).
    assert (T1 : rdn ASEGS MV2 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 raw)) by (unfold MV2, rd_MV2; rewrite (rd_MV2_slot H M s raw R bs Hs Hbs VFR 8) by lia; exact SL1).
    assert (T2 : rdn ASEGS MV2 (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr R 8))) by (unfold MV2, rd_MV2; rewrite (rd_MV2_slot H M s raw R bs Hs Hbs VFR 16) by lia; exact SL2).
    assert (T3 : rdn ASEGS MV2 (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr R 9))) by (unfold MV2, rd_MV2; rewrite (rd_MV2_slot H M s raw R bs Hs Hbs VFR 24) by lia; exact SL3).
    assert (T4 : rdn ASEGS MV2 (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (getr R 18))) by (unfold MV2, rd_MV2; rewrite (rd_MV2_slot H M s raw R bs Hs Hbs VFR 32) by lia; exact SL4).
    assert (T5 : rdn ASEGS MV2 (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (getr R 19))) by (unfold MV2, rd_MV2; rewrite (rd_MV2_slot H M s raw R bs Hs Hbs VFR 40) by lia; exact SL5).
    assert (T6 : rdn ASEGS MV2 (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 (getr R 20))) by (unfold MV2, rd_MV2; rewrite (rd_MV2_slot H M s raw R bs Hs Hbs VFR 48) by lia; exact SL6).
    assert (T7 : rdn ASEGS MV2 (Z_to_bv 64 (s - 2136)) 8 = Some (word_to_le_bytes 8 (0x655bc%bv : word))) by (unfold MV2, rd_MV2; rewrite (rd_MV2_slot H M s raw R bs Hs Hbs VFR 2136) by lia; exact SL7).
    destruct (Z.eq_dec n 0) as [Hn0|Hnz].
    - (* [comment removed for export] *)
      rewrite Hn0 in Q10.
      destruct (read_icpt_post0_run (seg_rom ASEGS) raw s Hs Hret R R2 MV2 Q10 Q2 Q1 Q8 Q20 T7 T1 T2 T3 T4 T5 T6)
        as (R3 & RUN & O10 & O2 & O1 & O8 & O9 & O18 & O19 & O20 & KB).
      exists R3, MV2. rewrite Hn0. repeat (split; [assumption|]). split; [intros x _; reflexivity | intros x Hx; exact Hx].
    - assert (Hnp : 0 < n) by lia.
      assert (XO : forall x : word, H x = false -> ~ (s - 2200 <= bv_unsigned x < s) -> ~ (STAGE <= bv_unsigned x < STAGE + 65536) -> MV2 x = M x).
      { intros x Hx N1 N2. unfold MV2, rd_MV2, mrestrict. rewrite Hx. exact (rd_M2_out H M s raw R bs Hs Hbs x N1 N2). }
      assert (CV2 : forall a v, In (a, 8, v) RD_CELLS -> rdn ASEGS MV2 (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 v))).
      { intros a v Hin. rewrite <- (rd_cell _ _ _ _ _ _ _ a 8 v HH Hin).
        assert (RA : 0x131000 <= a /\ a + 8 <= 0x141480).
        { unfold RD_CELLS in Hin. cbn [In] in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin; intros; subst; try lia|]); try destruct Hin.
          all: try discriminate. }
        apply rdn_ext; [rewrite u_small by lia; cbn; lia|]. intros x Hx. rewrite u_small in Hx by lia. cbn in Hx.
        apply XO; [| lia | unfold STAGE; lia].
        rewrite <- (Z_to_bv_bv_unsigned 64 x). apply (vis_of_inv scfg L ar C IL HI HIok sp0 DL _ _ _ _ _ _ _ (bv_unsigned x) HH); lia. }
      assert (SHZ : forall x, 0x7fff8000 + 0xcc450 <= x <= 0x7fff8000 + 0xce459 -> MV2 (Z_to_bv 64 x) = Some (Z_to_bv 8 0)).
      { intros x Hx. destruct (stage_shadow _ _ _ _ _ _ model HH x) as (BZ & VZ).
        - unfold in_shadow_of, HeapIfaceA.S, HeapIfaceA.SB. change (0x662280 / 8) with 0xcc450. change ((0x662280 + 0x10050 - 1) / 8) with 0xce459. lia.
        - rewrite XO; [exact BZ | exact VZ | rewrite u_small by lia; lia | rewrite u_small by lia; unfold STAGE; lia]. }
      assert (DV : (0x662290 + n - 1) / 8 <= 0xce451).
      { change 0xce451 with ((0x662290 + 65536 - 1) / 8). apply Z.div_le_mono; lia. }
      assert (DL0 : 0xcc452 <= (0x662290 + n - 1) / 8).
      { change 0xcc452 with (0x662290 / 8). apply Z.div_le_mono; lia. }
      destruct (read_icpt_post_run MV2 (seg_rom ASEGS) raw 0x662290 n s 0 _ _ _ _ eq_refl eq_refl eq_refl eq_refl) with (regs0 := R) (regs := R2) (M := MV2)
        as (R3 & M3' & RUN & O10 & O2 & O1 & O8 & O9 & O18 & O19 & O20 & KB & (OA & GR & _)).
      1: lia.
      1: { left. unfold LOWEND. lia. }
      1: exact Hs.
      1: { unfold Ba0RegionPoisoned_b.SB. lia. }
      1: { apply (store_ok_mono ASEGS _ (mrestrict H M) MV2); [exact (rd_MV2_grows H M s raw R bs) | exact WOK]. }
      1: exact Hret.
      1: { unfold rt_layout_globs.
           rewrite <- (w_lit 0x1374c0 (0x1374c0%bv : word) eq_refl), <- (w_lit 0x13fc38 (0x13fc38%bv : word) eq_refl),
                   <- (w_lit 0x1374c8 (0x1374c8%bv : word) eq_refl), <- (w_lit 0x140928 (0x140928%bv : word) eq_refl),
                   <- (w_lit 0x1374d0 (0x1374d0%bv : word) eq_refl), <- (w_lit 0x140930 (0x140930%bv : word) eq_refl),
                   <- (w_lit 0x1374d8 (0x1374d8%bv : word) eq_refl), <- (w_lit 0x140920 (0x140920%bv : word) eq_refl).
           repeat split; apply CV2; unfold RD_CELLS; cbn [In]; tauto. }
      1: { intros _ x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply SHZ. unfold Ba0RegionPoisoned_b.SB in Hx. change (6693520 / 8) with 0xcc452 in Hx. lia. }
      1: { intros _. apply SHZ. unfold Ba0RegionPoisoned_b.SB. lia. }
      1: { left. reflexivity. }
      1: { intros Hn64. unfold Ba0RegionPoisoned_b.SB.
           set (fS := 2147450880 + 6693520 / 8). set (lS := 2147450880 + (6693520 + n - 1) / 8).
           assert (FA : fS - fS mod 8 = 0x7fff8000 + 0xcc450) by reflexivity.
           assert (LA : 0x7fff8000 + 0xcc450 <= lS - lS mod 8 /\ lS - lS mod 8 + 8 <= 0x7fff8000 + 0xce459).
           { assert (D1 : (6693520 + n - 1) / 8 <= 0xcc459) by (change 0xcc459 with ((6693520 + 64 - 1) / 8); apply Z.div_le_mono; lia).
             pose proof (Z.mod_pos_bound lS 8 ltac:(lia)) as MB. pose proof (Z.div_mod lS 8 ltac:(lia)) as DM.
             assert (L0 : 0x7fff8000 + 0xcc452 <= lS) by (unfold lS; lia).
             assert (L1 : lS <= 0x7fff8000 + 0xcc459) by (unfold lS; lia).
             assert (Q : 0x1001888a <= lS / 8) by (change 0x1001888a with ((0x7fff8000 + 0xcc452) / 8); apply Z.div_le_mono; lia).
             lia. }
           exists (repeat (Z_to_bv 8 0) 8), (repeat (Z_to_bv 8 0) 8). split.
           - apply (rdn_of_bytes_at sp0 Hsp); [reflexivity | rewrite u_small by lia; cbn; lia |].
             intros j Hj. rewrite u_small by lia. rewrite FA.
             replace (nth j (repeat (Z_to_bv 8 0) 8) (Z_to_bv 8 0)) with (Z_to_bv 8 0) by (symmetry; apply nth_repeat).
             apply SHZ. lia.
           - apply (rdn_of_bytes_at sp0 Hsp); [reflexivity | rewrite u_small by lia; cbn; lia |].
             intros j Hj. rewrite u_small by lia.
             replace (nth j (repeat (Z_to_bv 8 0) 8) (Z_to_bv 8 0)) with (Z_to_bv 8 0) by (symmetry; apply nth_repeat).
             apply SHZ. lia. }
      1: { unfold c2_pre. repeat split; assumption. }
      1: { unfold FR. split; [intros x _; reflexivity|]. split; [intros x Hx; exact Hx|]. unfold slots_ok. repeat split; assumption. }
      1: exact T7.
      exists R3, M3'. repeat (split; [assumption|]). split; [|exact GR].
      intros x Nx. apply OA. lia.
  Qed.

  Lemma aread_site : forall vals ebs sr kn R M (model : Model) LB LK cr A (cnt : Z) pth off data so bls vbnd (ra : Z) K,
    let E := Env (vals_ev vals) ebs in
    regs_ok E sr R -> know_ok ASEGS E (mrestrict (ahid A model) M) kn ->
    sr_vars_lt (length vals) sr = true -> kn_vars_lt (length vals) kn = true ->
    (1 <= length vals)%nat -> vals_ev vals 0 = sp0 -> has_window kn = true ->
    getr R 2 = Z_to_bv 64 (bv_unsigned sp0 + so) -> - 2 ^ 22 <= so <= 0 -> so mod 16 = 0 ->
    getr R 10 = Z_to_bv 64 3 -> getr R 11 = Z_to_bv 64 STAGE -> getr R 12 = Z_to_bv 64 cnt -> 1 <= cnt <= 65536 ->
    getr R 1 = Z_to_bv 64 ra -> 0 <= ra < 2 ^ 64 -> ra mod 2 = 0 ->
    dinvA LB LK cr A M model ->
    fd_lookup (m_fds model) (Z_to_bv 64 3) = Some (FdFile pth off) -> fs_lookup (m_fs model) pth = Some data ->
    (forall i nb, find_nz i bls = Some nb -> (i < length vals)%nat /\ sub_blockA L ar LB (bv_unsigned (vals_ev vals i)) nb) ->
    (forall v b, find_nz v vbnd = Some b -> (v < length vals)%nat /\ bv_unsigned (vals_ev vals v) <= b) ->
    (forall R' M' (model' : Model),
       let bs := file_read data off (Z_to_bv 64 cnt) in
       let vals' := vals ++ junk_vals R' in
       let E' := Env (vals_ev vals') ebs in
       length vals' = (length vals + 32)%nat ->
       vals_ev vals' (length vals + 10) = len_word bs ->
       regs_ok E' (sr_after_call_j sr (map ridx c_kept) (length vals)) R' ->
       know_ok ASEGS E' (mrestrict (ahid A model') M') (keep_readA so bls vbnd kn) ->
       dinvA LB LK cr A M' model' ->
       m_fds model' = fd_insert (m_fds model) (Z_to_bv 64 3) (FdFile pth (off + len_word bs)) -> m_fs model' = m_fs model ->
       rdn ASEGS M' (Z_to_bv 64 STAGE) (length bs) = Some bs ->
       (forall a, 0 <= a < 2 ^ 64 -> ~ (bv_unsigned sp0 + so - 2200 <= a < bv_unsigned sp0 + so) -> ~ (STAGE <= a < STAGE + 65536) ->
                  M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
       srealizes ASEGS scfg (mkCfg (mkst R' (Z_to_bv 64 ra) M' (seg_rom ASEGS)) model') K) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x63390) M (seg_rom ASEGS)) model) K.
  Proof.
    intros vals ebs sr kn R M model LB LK cr A cnt pth off data so bls vbnd ra K E HR HK Hsv Hkv HL1 P0 Hiw
           R2 Hso Hsoal R10 R11 R12 Hcnt R1 Hra Hra2 DI Hfd Hfsl Hbl Hvb CONT.
    pose proof Hsp as Hsp'. unfold STAGE in *.
    set (s := bv_unsigned sp0 + so) in *. set (H := ahid A model) in *. set (MV := mrestrict H M) in *.
    pose proof (di_inv _ _ _ _ _ _ _ _ _ _ DI) as HH. pose proof (di_halt _ _ _ _ _ _ _ _ _ _ DI) as Hh. pose proof (di_minv _ _ _ _ _ _ _ _ _ _ DI) as HMI.
    destruct (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ DI) as (HOFF & HLC & HAWF & _ & _). fold H in HOFF, HLC.
    assert (Hs : 0x1000000 <= s - 2200 /\ s < 2 ^ 64) by (unfold s; lia).
    assert (WOK : store_ok ASEGS MV (Z_to_bv 64 (s - 2200)) 2200 = true).
    { replace (s - 2200) with (bv_unsigned sp0 + (so - 2200)) by (unfold s; ring).
      apply (window_store_ok sp0 vals ebs MV kn (so - 2200) 2200 HK Hiw P0); lia. }
    assert (VFR : forall x : word, s - 2200 <= bv_unsigned x < s -> H x = false).
    { intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply (vis_of_inv scfg L ar C IL HI HIok sp0 DL _ _ _ _ _ _ _ (bv_unsigned x) HH); unfold s in Hx; lia. }
    assert (VST : forall x : word, 0x662290 <= bv_unsigned x < 0x662290 + 65536 -> H x = false).
    { intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply (vis_of_inv scfg L ar C IL HI HIok sp0 DL _ _ _ _ _ _ _ (bv_unsigned x) HH); lia. }
    assert (CV : forall a n v, In (a, n, v) RD_CELLS ->
                 rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v))).
    { intros a n v Hin. unfold MV, H. rewrite rdn_mrestrict_eq; [exact (rd_cell _ _ _ _ _ _ _ a n v HH Hin)|].
      apply (avoid_img _ _ _ _ _ _ _ a (Z.to_nat n) HH);
        unfold RD_CELLS in Hin; cbn [In] in Hin; repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <- <-; cbn; lia|]); destruct Hin. }
    (* [comment removed for export] *)
    destruct (wrap_read_pre_run MV (seg_rom ASEGS) (Z_to_bv 64 s) (Z_to_bv 64 ra) s 3 0x662290 cnt
                ltac:(apply u_small; lia) Hs WOK ltac:(lia) ltac:(lia) ltac:(lia)) with (regs := R)
      as (Ra & RUN1 & A17 & A10 & A11 & A12 & _ & _ & _ & _ & A2 & A1 & A8 & A9 & A18 & A19 & A20 & KB1).
    1: { rewrite <- (w_lit 0x140918 (0x140918%bv : word) eq_refl). exact (CV 0x140918 1 1 ltac:(unfold RD_CELLS; cbn [In]; tauto)). }
    1: { rewrite <- (w_lit 0x139318 (0x139318%bv : word) eq_refl). exact (CV 0x139318 8 0x130304 ltac:(unfold RD_CELLS; cbn [In]; tauto)). }
    1: exact R10. 1: exact R11. 1: exact R12. 1: exact R2. 1: exact R1.
    rewrite (w_lit 0x63390 (0x63390%bv : word) eq_refl).
    apply (rz_msteps_lz ASEGS scfg H A R _ M Ra _ _ model K HOFF asegs_wx HLC HAWF HMI Hh RUN1).
    intros model1 MI1 SBM1 EQV1.
    destruct (sbm_fds _ _ SBM1) as (F1 & F2).
    (* [comment removed for export] *)
    eapply (rz_read_file_lz ASEGS scfg Ra _ _ model1 ECALLW (Z_to_bv 64 3) pth off data cnt K); try apply is_ecall_ECALLW.
    - vm_compute. reflexivity.
    - rewrite (sbm_halted_eq _ _ SBM1). exact Hh.
    - exact A17.
    - exact A10.
    - rewrite u_small by lia. lia.
    - rewrite F1. exact Hfd.
    - rewrite F2. exact Hfsl.
    - exact A12.
    - lia.
    - lia.
    - lia.
    - rewrite A11.
      apply (store_ok_window ASEGS _ (Z_to_bv 64 0x662290) (Z_to_bv 64 0x662290) 65536%nat (Z.to_nat cnt) 0x662290 0x672290);
        first [exact wseg_stage | reflexivity | lia | (rewrite u_small by lia; lia)].
    - rewrite A11, u_small by lia. unfold TASK_SIZE. lia.
    - rewrite A11, (sbm_lazy_eq _ _ SBM1).
      apply (nolazy_of_inv scfg L ar C IL HI HIok sp0 Hsp DL _ _ _ _ _ _ model _ _ HH); [rewrite u_small by lia; lia|].
      intros k Hk. left. rewrite u_small by lia. lia.
    - cbv zeta. rewrite A11, A12.
      set (bs := file_read data off (Z_to_bv 64 cnt)).
      set (n := Z.of_nat (length bs)).
      assert (Hn : 0 <= n <= 65536).
      { unfold n, bs. rewrite length_file_read. unfold word_to_nat. rewrite (u_small cnt) by lia. lia. }
      replace (v_addi (0x12a8d8%bv : word) 4) with (0x12a8dc%bv : word) by (apply bv_eq; reflexivity).
      set (raw := Z_to_bv 64 ra) in *.
      set (M2 := wbytes (munrestrict H M (RDA MV raw s R)) (Z_to_bv 64 6693520) bs).
      set (R2' := regupd Ra 10 (len_word bs)).
      set (model2 := with_fds (fd_insert (m_fds model1) (Z_to_bv 64 3) (FdFile pth (off + len_word bs))) model1).
      assert (EL2 : m_vm_lazy model2 = m_vm_lazy model) by (unfold model2; rewrite with_fds_vm_lazy; exact (sbm_lazy_eq _ _ SBM1)).
      assert (EH2 : ahid A model2 = H) by (unfold H; apply ahid_same_lazy; exact EL2).
      assert (Hh2 : m_halted model2 = None) by (unfold model2; rewrite with_fds_halted'; rewrite (sbm_halted_eq _ _ SBM1); exact Hh).
      assert (MI2 : MInv A model2) by (apply (minv_same_vm A model1 model2); [unfold model2; apply with_fds_vm | exact MI1]).
      assert (Hbs : Z.of_nat (length bs) <= 65536) by (fold n; lia).
      (* [comment removed for export] *)
      destruct (rd_post LB [] LK cr A M model s raw R R2' bs HH Hbs ltac:(unfold s; lia) WOK ltac:(apply ret_ok_even; unfold raw; rewrite u_small by lia; exact Hra2))
        as (R3 & M3' & RUN3 & O10 & O2 & O1 & O8 & O9 & O18 & O19 & O20 & KB3 & OUT3 & GR3).
      1: { unfold R2'. rewrite getr_same by discriminate. reflexivity. }
      1: { unfold R2'. rewrite getr_other by discriminate. exact A2. }
      1: { unfold R2'. rewrite getr_other by discriminate. exact A1. }
      1: { unfold R2'. rewrite getr_other by discriminate. exact A8. }
      1: { unfold R2'. rewrite getr_other by discriminate. exact A9. }
      1: { unfold R2'. rewrite getr_other by discriminate. exact A20. }
      unfold rd_MV2 in RUN3, OUT3, GR3. fold H in RUN3, OUT3, GR3. fold MV in RUN3, OUT3, GR3. unfold STAGE in RUN3, OUT3, GR3. fold M2 in RUN3, OUT3, GR3.
      apply (rz_msteps_lz ASEGS scfg H A R2' _ M2 R3 _ M3' model2 K HOFF asegs_wx ltac:(rewrite EL2; exact HLC) HAWF MI2 Hh2 RUN3).
      intros model3 MI3 SBM3 EQV3.
      set (M3 := munrestrict H M2 M3') in *.
      (* [comment removed for export] *)
      assert (FRM : forall a, 0 <= a < 2 ^ 64 -> ~ (s - 2200 <= a < s) -> ~ (0x662290 <= a < 0x662290 + 65536) -> M3 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
      { intros a Ha N1 N2. unfold M3, munrestrict.
        assert (E2 : M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
        { unfold M2, MV. apply (rd_M2_out H M s raw R bs Hs Hbs); rewrite u_small by lia; unfold STAGE; lia. }
        destruct (H (Z_to_bv 64 a)) eqn:Hx; [exact E2|].
        rewrite OUT3 by (rewrite u_small by lia; lia). unfold mrestrict. rewrite Hx. exact E2. }
      assert (GRW : forall x : word, M x <> None -> M3 x <> None).
      { intros x Hd. unfold M3, munrestrict.
        assert (E2 : M2 x <> None) by (unfold M2, MV; apply (rd_M2_grows H M s raw R bs); exact Hd).
        destruct (H x) eqn:Hx; [exact E2|]. apply GR3. unfold mrestrict. rewrite Hx. exact E2. }
      assert (EV3 : vml_of model3 = vml_of model).
      { rewrite (sbm_vml _ _ SBM3). unfold model2. rewrite (vml_same_vm model1 _ (with_fds_vm _ model1)). exact (sbm_vml _ _ SBM1). }
      assert (Hh3 : m_halted model3 = None) by (rewrite (sbm_halted_eq _ _ SBM3); exact Hh2).
      assert (EH3 : ahid A model3 = H) by (rewrite (ahid_sbm A model2 model3 SBM3); exact EH2).
      assert (DI3 : dinvA LB LK cr A M3 model3).
      { apply (dinv_frame scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M M3 model model3 DI); [ | exact GRW | exact EV3 | exact MI3 | exact Hh3].
        intros a Ha NC. apply FRM; [exact Ha | |]; intros Hr; apply NC; unfold CWA.
        - right. left. unfold s in Hr. lia.
        - right. right. exists 0x662290, 0x673ca8. split; [unfold IMG_W_A; cbn [In]; tauto | lia]. }
      assert (HL' : length (vals ++ junk_vals R3) = (length vals + 32)%nat) by (rewrite length_app, junk_vals_length; reflexivity).
      assert (P0' : vals_ev (vals ++ junk_vals R3) 0 = sp0) by (rewrite vals_ev_app_l by lia; exact P0).
      assert (KEPT : forall r : reg, In r c_kept -> getr R3 r = getr R r).
      { assert (KK : forall r : reg, In r callee_saved -> ~ In r Ba0ReadIcpt_b.RIPL -> getr R3 r = getr R r).
        { intros r Hr Hn'. rewrite (KB3 r Hr Hn'). unfold R2'. rewrite getr_other; [exact (KB1 r Hr Hn')|].
          intros ->. clear - Hr. cbv in Hr. intuition discriminate. }
        intros r Hr. unfold c_kept in Hr. cbn [In] in Hr.
        destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]].
        - rewrite O2, R2. reflexivity.
        - apply KK; cbv; intuition discriminate.
        - apply KK; cbv; intuition discriminate.
        - exact O8.
        - exact O9.
        - exact O18.
        - exact O19.
        - exact O20.
        - apply KK; cbv; intuition discriminate.
        - apply KK; cbv; intuition discriminate.
        - apply KK; cbv; intuition discriminate.
        - apply KK; cbv; intuition discriminate.
        - apply KK; cbv; intuition discriminate.
        - apply KK; cbv; intuition discriminate.
        - apply KK; cbv; intuition discriminate. }
      apply (CONT R3 M3 model3 HL').
      + rewrite (vals_ev_junkA vals R3 10) by lia. exact O10.
      + exact (regs_after_keeps vals ebs sr R R3 c_kept Hsv HR KEPT c_kept_no0A).
      + (* [comment removed for export] *) rewrite EH3. unfold keep_readA.
        pose proof (env_app_know ASEGS vals (junk_vals R3) ebs _ kn Hkv HK) as HK1.
        refine (know_keep_sound ASEGS 0 so 2200 bls vbnd [] IMG_NOSTAGE IMG_RW_A
                  (Env (vals_ev (vals ++ junk_vals R3)) ebs)
                  (fun a => H (Z_to_bv 64 a) = false /\ ~ (s - 2200 <= a < s) /\ ~ (0x662290 <= a < 0x662290 + 65536))
                  (fun a => s - 2200 <= a < s)
                  _ MV (mrestrict H M3) _ _ kn HK1).
        * assert (VIS : forall a, 0 <= a < 2 ^ 64 -> (a < 0x696000 \/ bv_unsigned sp0 - 8388608 <= a \/ in_block LB a) -> H (Z_to_bv 64 a) = false)
            by (intros a Ha Hc; exact (vis_of_inv scfg L ar C IL HI HIok sp0 DL _ _ _ _ _ _ _ a HH Ha Hc)).
          constructor; cbn [ev]; rewrite ?P0'.
          -- lia.
          -- lia.
          -- intros z Hz Hnot. split; [apply VIS; lia|]. unfold s. split; lia.
          -- intros z Hz. right. unfold s. lia.
          -- intros i nb Hf. destruct (Hbl i nb Hf) as (Hi32 & SBk). rewrite vals_ev_app_l by exact Hi32.
             pose proof (sub_blockA_hz L ar IL sp0 DL _ _ _ SBk) as (Z1 & Z2 & Z3).
             destruct SBk as (cap & Hnb & Hin & HB).
             split; [lia|]. intros z Hz. split; [|unfold s; split; lia].
             apply VIS; [lia|]. right. right. exists (bv_unsigned (vals_ev vals i), cap). split; [exact Hin | cbn [fst snd]; lia].
          -- intros v b Hf. destruct (Hvb v b Hf) as [Hv H1]. rewrite vals_ev_app_l by exact Hv. exact H1.
          -- intros i [].
          -- intros lo hi Hin. unfold IMG_NOSTAGE in Hin. cbn [In] in Hin.
             repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; (split; [lia|]); (split; [lia|]); intros a Ha; (split; [apply VIS; lia | unfold s; split; lia])|]).
             destruct Hin.
          -- intros lo hi Hin. unfold IMG_RW_A in Hin. destruct Hin as [E1|[]]. injection E1 as <- <-. split; [lia|]. split; [lia|].
             intros Mx d m Hd Hm.
             apply (store_ok_window ASEGS Mx (Z_to_bv 64 0x662290) (Z_to_bv 64 d) 65536%nat m 0x662290 0x672290);
               first [exact wseg_stage | reflexivity | lia | (rewrite u_small by lia; lia)].
        * intros a Ha (V1 & N1 & N2). unfold MV, mrestrict. rewrite V1. apply FRM; assumption.
        * intros a Ha. unfold mrestrict. rewrite (VFR (Z_to_bv 64 a)) by (rewrite u_small by (unfold s in Ha; lia); exact Ha).
          apply GRW. apply (window_defined sp0 Hsp vals ebs H M kn HK Hiw P0). unfold s in Ha. lia.
      + exact DI3.
      + rewrite (proj1 (sbm_fds _ _ SBM3)). unfold model2. rewrite with_fds_fds, F1. reflexivity.
      + rewrite (proj2 (sbm_fds _ _ SBM3)). unfold model2. rewrite with_fds_fs. exact F2.
      + fold bs. rewrite <- (rd_stage_bytes H M s raw R bs Hbs). unfold STAGE. fold MV. fold M2.
        apply rdn_ext; [rewrite u_small by lia; lia|]. intros x Hx. rewrite u_small in Hx by lia.
        unfold M3, munrestrict. rewrite (VST x) by lia. rewrite OUT3 by lia. unfold mrestrict. rewrite (VST x) by lia. reflexivity.
      + exact FRM.
  Qed.
End DrvRead.
End FPX_1.
