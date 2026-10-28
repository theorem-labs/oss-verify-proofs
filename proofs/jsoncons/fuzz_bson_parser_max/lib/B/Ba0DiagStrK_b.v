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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StreamSim ShapeAlg ShapeLaws SpinAlg Hoare AgentLib Spec AsanAcctShape SymExec2 SymExec2Sound SymRun SymDrive SymDriveX
  HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import DrvKitA DrvNodesLazyK As0DrvKitA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0DrvEntry_b Ba0Drv_defs_b Ba0DrvLib_b Ba0DrvRead_b Ba0DrvPiece_b Ba0DiagLoopK_b Ba0DrvStdio_b Ba0DrvPrintfK_b Ba0DrvPrintf1_b Ba0DrvExit_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require L5Defs L5KnA ArtMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require BatFsInv_b BatWrapMallocX_b Ba0RegionPoisoned_b Ba0AsanMemcpy_b Ba0DiagStrnlen_b Ba0DiagKit_b Ba0DiagGlue_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Import SX2. Import SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma rdn_of_defined : forall (Mx : word -> option byte) (n : nat) a, 0 <= a -> a + Z.of_nat n <= 2 ^ 63 ->
  (forall i, 0 <= i < Z.of_nat n -> Mx (Z_to_bv 64 (a + i)) <> None) -> exists bs, rdn ASEGS Mx (Z_to_bv 64 a) n = Some bs /\ length bs = n.
Proof.
  intros Mx n. induction n as [|n IH]; intros a Ha Hn Hd.
  - exists []. split; reflexivity.
  - destruct (Mx (Z_to_bv 64 a)) as [b|] eqn:Eb; [|exfalso; apply (Hd 0 ltac:(lia)); rewrite Z.add_0_r; exact Eb].
    destruct (IH (a + 1) ltac:(lia) ltac:(lia)) as (bs & Hr & Hl).
    { intros i Hi. replace (a + 1 + i) with (a + (1 + i)) by lia. apply Hd. lia. }
    exists (b :: bs). split; [|cbn [length]; lia].
    apply (rdn_cons1 Mx a b n bs Ha); [cbn [rdn]; rewrite Eb; reflexivity | exact Hr].
Qed.

Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section StrK.
  Variable L : asan_layout.
  Variable ar : asan_run.
  Variable C : asan_statics_cells.
  Variable IL : icpt_layout.
  Variable HI : asan_iface.
  Hypothesis HIok : asan_iface_okB L ar C scfg HI.
  Variable sp0 : word.
  Hypothesis Hsp : 0x7fff80000000 <= bv_unsigned sp0 <= 2 ^ 47.
  Hypothesis DL : drv_layoutA L ar IL sp0.
  Hypothesis Hdg : incl DG_CELLS (asc_cells C).
  Hypothesis Hdgs : incl DGS_CELLS (asc_cells C).
  Variable M0 : word -> option byte.
  #[local] Notation dinvA := (dinv ar HI sp0 M0).
  #[local] Notation usp := (bv_unsigned sp0).

  (* [comment removed for export] *)
  #[using="scfg L C IL HIok Hsp DL"] Lemma str_cstr : forall LB LK cr A M (model : Model) (p : word) (path : list byte),
    dinvA LB LK cr A M model ->
    usp <= bv_unsigned p -> bv_unsigned p + Z.of_nat (length path) + 1 + 16 <= 2 ^ 47 ->
    rdn ASEGS M0 p (length path + 1) = Some (path ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) path ->
    defined M0 (bv_unsigned p) (Z.of_nat (length path) + 1 + 16) ->
    exists t8, Ba0DiagStrnlen_b.DSN.cstr (mrestrict (ahid A model) M) (bv_unsigned p) path t8.
  Proof.
    intros LB LK cr A M model p path D Hlo Hhi STR NONUL PDEF. pose proof Hsp as Hsp'.
    set (pz := bv_unsigned p) in *. set (n := length path) in *.
    destruct (rdn_of_defined M0 8 (pz + Z.of_nat n + 1) ltac:(lia) ltac:(lia)) as (t8 & R8 & L8).
    { intros i Hi. replace (pz + Z.of_nat n + 1 + i) with (pz + (Z.of_nat n + 1 + i)) by lia. apply PDEF. lia. }
    assert (RD0 : rdn ASEGS M0 (Z_to_bv 64 pz) (n + 9) = Some (path ++ Z_to_bv 8 0 :: t8)).
    { replace (n + 9)%nat with ((n + 1) + 8)%nat by lia. replace (path ++ Z_to_bv 8 0 :: t8) with ((path ++ [Z_to_bv 8 0]) ++ t8) by (rewrite <- app_assoc; reflexivity).
      unfold pz at 1. rewrite Z_to_bv_bv_unsigned. apply (SeqExec.rdn_app ASEGS M0 (n + 1) 8 p _ _ STR).
      replace (p + nat_to_word (n + 1))%bv with (Z_to_bv 64 (pz + Z.of_nat n + 1)); [exact R8|].
      apply bv_eq. unfold nat_to_word, pz. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_r. f_equal. lia. }
    exists t8. constructor.
    - apply (rdn_tr M0 _ pz (n + 9) _ RD0); [lia | lia|].
      intros i Hi. unfold mrestrict.
      rewrite (vis_stk scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ i D) by lia.
      apply (di_above _ _ _ _ _ _ _ _ _ _ D). lia.
    - exact L8.
    - intros j Hj Hz. apply NONUL.
      replace (Z_to_bv 8 0) with (nth j path (Z_to_bv 8 0)); [apply nth_In; exact Hj|].
      apply bv_eq. rewrite Hz. reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="L IL Hsp DL"] Lemma str_hull : forall LB LK cr A M (model : Model) (pz n : Z),
    dinvA LB LK cr A M model -> shadow_allowed A (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) ->
    usp <= pz -> 0 <= n ->
    forall x : word, Ba0RegionPoisoned_b.SB + pz / 8 - 7 <= bv_unsigned x < Z.min (Ba0RegionPoisoned_b.SB + (pz + n) / 8 + 8) (Ba0RegionPoisoned_b.SB + 2 ^ 44) ->
      mrestrict (ahid A model) M x = Some (Z_to_bv 8 0).
  Proof.
    intros LB LK cr A M model pz n D SAH Hlo Hn x Hx. pose proof Hsp as Hsp'.
    rewrite <- (Z_to_bv_bv_unsigned 64 x).
    apply (hi_sh0 L ar IL HI sp0 Hsp DL M0 _ _ _ _ _ _ (bv_unsigned x) D SAH).
    unfold Ba0RegionPoisoned_b.SB in Hx.
    assert (Q1 : (usp - 8388608) / 8 + 1048576 <= pz / 8).
    { replace (usp - 8388608) with (usp + (-1048576) * 8) by lia. rewrite Z.div_add by lia. pose proof (Z.div_le_mono usp pz 8 ltac:(lia) Hlo). lia. }
    change ((2 ^ 47 - 1) / 8) with (2 ^ 44 - 1). lia.
  Qed.

  (* [comment removed for export] *)
  #[using="scfg L C IL HIok DL Hdg Hdgs"] Lemma dgs_cell_vis : forall LB LK cr A M (model : Model) a n v, dinvA LB LK cr A M model -> In (a, n, v) (DG_CELLS ++ DGS_CELLS) ->
    rdn ASEGS (mrestrict (ahid A model) M) (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)).
  Proof.
    intros LB LK cr A M model a n v D Hin. pose proof (di_inv _ _ _ _ _ _ _ _ _ _ D) as HH.
    destruct (aiob_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & CS). rewrite (dla_segs _ _ _ _ DL) in CS.
    assert (Hin' : In (a, n, v) (asc_cells C)) by (apply in_app_or in Hin as [X|X]; [exact (Hdg _ X) | exact (Hdgs _ X)]).
    pose proof (proj1 (Forall_forall _ _) CS (a, n, v) Hin') as X. unfold cell_is in X. cbn [fst snd] in X.
    rewrite rdn_mrestrict_eq; [exact X|].
    intros k Hk. unfold woff.
    assert (B : 0 <= a /\ a + Z.of_nat (Z.to_nat n) <= 0x696000).
    { unfold DG_CELLS, DGS_CELLS in Hin. cbn [In app] in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <- <-; cbn; lia|]). destruct Hin. }
    rewrite (u64_lit a) by lia. apply (vis_low scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ _ D). lia.
  Qed.

  #[using="scfg L C IL HIok Hsp DL Hdg Hdgs"] Lemma str_statics : forall LB LK cr A M (model : Model),
    dinvA LB LK cr A M model -> (forall i, 65536 <= i < 1282048 -> mrestrict (ahid A model) M (Z_to_bv 64 i) = None) ->
    Ba0DiagStrnlen_b.DSN.sn_cells (mrestrict (ahid A model) M) /\ Ba0AsanMemcpy_b.mc_icpt_globs (mrestrict (ahid A model) M).
  Proof.
    intros LB LK cr A M model D IMG. set (MV := mrestrict (ahid A model) M) in *.
    assert (STC : forall a n v, In (a, n, v) (DG_CELLS ++ DGS_CELLS) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros a n v Hin; exact (dgs_cell_vis _ _ _ _ _ _ a n v D Hin)).
    assert (STC1 : forall a v, In (a, 1, v) (DG_CELLS ++ DGS_CELLS) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros a v Hin Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (STC a 1 v Hin). }
    assert (IC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (65536 <=? a) && (a + Z.of_nat n <=? 1282048) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hc. apply andb_prop in Hc as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply IMG. lia. }
    assert (RT : Ba0RegionPoisoned_b.rt_layout_globs MV).
    { unfold Ba0RegionPoisoned_b.rt_layout_globs.
      rewrite <- (w_lit 0x1374c0 (0x1374c0%bv : word) eq_refl), <- (w_lit 0x13fc38 (0x13fc38%bv : word) eq_refl), <- (w_lit 0x1374c8 (0x1374c8%bv : word) eq_refl), <- (w_lit 0x140928 (0x140928%bv : word) eq_refl),
              <- (w_lit 0x1374d0 (0x1374d0%bv : word) eq_refl), <- (w_lit 0x140930 (0x140930%bv : word) eq_refl), <- (w_lit 0x1374d8 (0x1374d8%bv : word) eq_refl), <- (w_lit 0x140920 (0x140920%bv : word) eq_refl).
      split; [exact (IC 0x1374c0 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0x13fc38)) ltac:(img_rd) eq_refl)|].
      split; [exact (STC 0x13fc38 8 0x7fff8000 ltac:(unfold DG_CELLS, DGS_CELLS; cbn [In app]; tauto))|].
      split; [exact (IC 0x1374c8 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0x140928)) ltac:(img_rd) eq_refl)|].
      split; [exact (STC 0x140928 8 0 ltac:(unfold DG_CELLS, DGS_CELLS; cbn [In app]; tauto))|].
      split; [exact (IC 0x1374d0 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0x140930)) ltac:(img_rd) eq_refl)|].
      split; [exact (STC 0x140930 8 0 ltac:(unfold DG_CELLS, DGS_CELLS; cbn [In app]; tauto))|].
      split; [exact (IC 0x1374d8 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0x140920)) ltac:(img_rd) eq_refl)|].
      exact (STC 0x140920 8 (2 ^ 47 - 1) ltac:(unfold DG_CELLS, DGS_CELLS; cbn [In app]; tauto)). }
    split.
    - unfold Ba0DiagStrnlen_b.DSN.sn_cells, L5Defs.L5.u8_at, L5Defs.L5.u64_at.
      split; [exact (STC1 1313048 1 ltac:(unfold DG_CELLS, DGS_CELLS; cbn [In app]; tauto) eq_refl)|].
      split; [exact (STC 1283192 8 1221668 ltac:(unfold DG_CELLS, DGS_CELLS; cbn [In app]; tauto))|].
      split; [exact (STC 1282824 8 1218564 ltac:(unfold DG_CELLS, DGS_CELLS; cbn [In app]; tauto))|].
      split; [exact RT|].
      rewrite <- (w_lit 0x1374b0 (0x1374b0%bv : word) eq_refl), <- (w_lit 0x1d1863 (0x1d1863%bv : word) eq_refl).
      split; [exact (IC 0x1374b0 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0x1d1768)) ltac:(img_rd) eq_refl)|].
      exact (STC1 0x1d1863 1 ltac:(unfold DG_CELLS, DGS_CELLS; cbn [In app]; tauto) eq_refl).
    - unfold Ba0AsanMemcpy_b.mc_icpt_globs.
      rewrite <- (w_lit 0x138028 (0x138028%bv : word) eq_refl), <- (w_lit 0x140919 (0x140919%bv : word) eq_refl), <- (w_lit 0x1394c8 (0x1394c8%bv : word) eq_refl).
      split; [exact (IC 0x138028 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0x140919)) ltac:(img_rd) eq_refl)|].
      split; [exact (STC1 0x140919 1 ltac:(unfold DG_CELLS, DGS_CELLS; cbn [In app]; tauto) eq_refl)|].
      exact (STC 0x1394c8 8 0x129900 ltac:(unfold DG_CELLS, DGS_CELLS; cbn [In app]; tauto)).
  Qed.
End StrK.
End FPX_1.
