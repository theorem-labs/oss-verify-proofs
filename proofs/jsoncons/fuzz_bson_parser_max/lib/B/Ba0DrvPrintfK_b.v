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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg Hoare AsanAcctShape SymExec2 SymExec2Sound SymRun SymDrive SymDriveX
  HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import DrvKitA DrvNodesLazyK As0DrvKitA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0DrvEntry_b Ba0Drv_defs_b Ba0DrvLib_b Ba0DrvRead_b Ba0DrvPiece_b Ba0DrvStdio_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require L5Defs L5KnA ArtMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require BatFsInv_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import Ba0DrvP_dpA2_b Ba0DrvP_dpA3_b Ba0DrvP_dpA4_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition SOBUF : Z := 6898976.
Definition stdoutA (j : Z) (MV : word -> option byte) : Prop :=
  rdn ASEGS MV (Z_to_bv 64 1293752) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5))                       (* [comment removed for export] *)
  /\ rdn ASEGS MV (Z_to_bv 64 1293848) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1024))                 (* [comment removed for export] *)
  /\ rdn ASEGS MV (Z_to_bv 64 1293784) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (SOBUF + 1024)))       (* [comment removed for export] *)
  /\ rdn ASEGS MV (Z_to_bv 64 1293792) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (SOBUF + 2 * j)))      (* [comment removed for export] *)
  /\ rdn ASEGS MV (Z_to_bv 64 1293808) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 SOBUF))                (* [comment removed for export] *)
  /\ rdn ASEGS MV (Z_to_bv 64 1293892) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))           (* [comment removed for export] *)
  /\ rdn ASEGS MV (Z_to_bv 64 1293896) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))           (* [comment removed for export] *)
  /\ (forall a n, 1293752 <= a -> a + n <= 1293752 + 232 -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV (Z_to_bv 64 (a + d)) k = true)
  /\ (forall a n, SOBUF <= a -> a + n <= SOBUF + 1024 -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV (Z_to_bv 64 (a + d)) k = true)
  /\ (forall i, 0 <= i < j -> rdn ASEGS MV (Z_to_bv 64 (SOBUF + 2 * i)) 1 = Some [Z_to_bv 8 48] /\ rdn ASEGS MV (Z_to_bv 64 (SOBUF + 2 * i + 1)) 1 = Some [Z_to_bv 8 10]).

(* [comment removed for export] *)
Definition Wpf (S j a : Z) : Prop :=
  S - 3232 <= a < S \/ 1293752 <= a < 1293756 \/ 1293792 <= a < 1293800 \/ SOBUF + 2 * j <= a < SOBUF + 2 * j + 2.

Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section PrintfK.
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
  Hypothesis Hpr : incl PR_CELLS (asc_cells C).
  Variable M0 : word -> option byte.
  #[local] Notation dinvA := (dinv ar HI sp0 M0).
  #[local] Notation usp := (bv_unsigned sp0).
  #[local] Notation rom := (seg_rom ASEGS).

  #[using="L C IL HIok ICok ILY Hsp DL Hpr"] Lemma printf2_run : forall LB LK cr A M (model : Model) R (S canz : Z) K,
    dinvA LB LK cr A M model ->
    let MV := mrestrict (ahid A model) M in
    usp - 4096 <= S -> S + 32 <= usp -> S mod 16 = 0 -> 0 <= canz < 2 ^ 64 ->
    getr R 1%bv = Z_to_bv 64 688024 -> getr R 2%bv = Z_to_bv 64 S -> getr R 10%bv = Z_to_bv 64 85514 -> getr R 11%bv = Z_to_bv 64 (S + 24) ->
    (forall a n, usp - 8388608 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV (Z_to_bv 64 (a + d)) k = true) ->
    (forall i, 65536 <= i < 1282048 -> MV (Z_to_bv 64 i) = None) ->
    rdn ASEGS MV (Z_to_bv 64 6896960) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 canz)) ->
    rdn ASEGS MV (Z_to_bv 64 (S + 24)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
    stdoutA 0 MV ->
    (forall (fx' : PropExec.FPState) R' M1 (model1 : Model),
        dinvA LB LK cr A M1 model1 -> same_but_materialized model model1 ->
        (forall x, In x AS0DRVP_dpA2.KS_dpA2 -> getr R' (Z_to_bv 5 (Z.of_nat x)) = getr R (Z_to_bv 5 (Z.of_nat x))) ->
        getr R' 10%bv = Z_to_bv 64 2 ->
        stdoutA 1 (mrestrict (ahid A model1) M1) ->
        (forall a, 0 <= a < 2 ^ 64 -> ~ Wpf S 0 a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
        (forall a, 0 <= a < 2 ^ 64 -> ~ Wpf S 0 a -> mrestrict (ahid A model1) M1 (Z_to_bv 64 a) = MV (Z_to_bv 64 a)) ->
        (forall a : word, MV a <> None -> mrestrict (ahid A model1) M1 a <> None) ->
        srealizes ASEGS scfg (mkCfg (@mkst fx' R' (Z_to_bv 64 0xa7f98) M1 rom) model1) K) ->
    srealizes ASEGS scfg (mkCfg (@mkst fx R (Z_to_bv 64 0x633ac) M rom) model) K.
  Proof.
    intros LB LK cr A M model R S canz K D MV HS1 HS2 HS16 Hcan R1 R2 R10 R11 WIN IMG CAN ARG SO KONT.
    pose proof Hsp as Hsp'. destruct SO as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & FW & BW & BC).
    assert (PC : forall a n v, In (a, n, v) PR_CELLS -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros a n v Hin; exact (pr_cell_vis scfg L ar C IL HI HIok sp0 Hsp DL Hpr M0 _ _ _ _ _ _ a n v D Hin)).
    assert (P1 : forall a v, In (a, 1, v) PR_CELLS -> 0 <= v < 2 ^ 64 -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros a v Hin Hv. rewrite <- (ArtMem.art_bytes1 v Hv). exact (PC a 1 v Hin). }
    set (V := fun n : nat => match n with 2%nat => S | 40%nat => canz | _ => 0 end).
    destruct (AS0DRVP_dpA2.dpA2_conc fx R MV V) as (fx' & R' & MV' & GR & _ & FRZ & MS & KS & _ & Q10 & _ & _ & _ & _ & _ & _ & _ & O1 & O2 & O3 & O4).
    all: cbn [V].
    all: try assumption.
    all: try (clear - Hsp' HS1 HS2 Hcan; lia).
    - (* [comment removed for export] *) intros d k Hd Hk. apply (WIN (S - 3232) 3232); lia.
    - (* [comment removed for export] *) intros i Hi. apply (store_ok_defined sp0); [lia|]. apply (WIN (S - 3232) 3232); lia.
    - (* [comment removed for export] *)
      intros i Hi. apply (stk_sh0 scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ _ D).
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      clear - Hsp' Hal HS1 HS2 HS16 Hi. lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    - (* [comment removed for export] *)
      apply BatFsInv_b.cell_zero_bytes; [right; reflexivity | lia | lia |]. intros j Hj. unfold byte_at.
      apply (img_sh0 scfg L ar IL HI ICok sp0 DL M0 _ _ _ _ _ _ 0x14dc0 64 _ D); [lia | lia | lia | | lia].
      rewrite (aicl_poison IL ILY). repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
    - apply BatFsInv_b.cell_zero_bytes; [right; reflexivity | lia | lia |]. intros j Hj. unfold byte_at.
      apply (img_sh0 scfg L ar IL HI ICok sp0 DL M0 _ _ _ _ _ _ 0x14e00 64 _ D); [lia | lia | lia | | lia].
      rewrite (aicl_poison IL ILY). repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
    - (* [comment removed for export] *)
      apply BatFsInv_b.cell_zero_bytes; [right; reflexivity | lia | lia |]. intros j Hj. unfold byte_at.
      apply (img_sh0 scfg L ar IL HI ICok sp0 DL M0 _ _ _ _ _ _ 0x694500 64 _ D); [lia | lia | lia | | lia].
      rewrite (aicl_poison IL ILY). repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
    - intros d k Hd Hk. apply (FW 1293752 4); lia.
    - intros d k Hd Hk. apply (FW 1293792 8); lia.
    - intros d k Hd Hk. apply (BW 6898976 1); unfold SOBUF; lia.
    - intros d k Hd Hk. apply (BW 6898977 1); unfold SOBUF; lia.
    - apply P1; [unfold PR_CELLS; cbn [In]; tauto | lia].
    - apply P1; [unfold PR_CELLS; cbn [In]; tauto | lia].
    - exact (PC 0x13fc38 8 0x7fff8000 ltac:(unfold PR_CELLS; cbn [In]; tauto)).
    - exact (PC 0x139348 8 0x1273fc ltac:(unfold PR_CELLS; cbn [In]; tauto)).
    - exact (PC 0x139350 8 0x121118 ltac:(unfold PR_CELLS; cbn [In]; tauto)).
    - apply P1; [unfold PR_CELLS; cbn [In]; tauto | lia].
    - exact (PC 0x1394c8 8 0x129900 ltac:(unfold PR_CELLS; cbn [In]; tauto)).
    - exact (PC 0x1394d0 8 0x129d04 ltac:(unfold PR_CELLS; cbn [In]; tauto)).
    - (* [comment removed for export] *)
      unfold V in FRZ, MS; cbn beta iota in FRZ, MS.
      assert (FRW : forall a, 0 <= a < 2 ^ 64 -> ~ Wpf S 0 a -> MV' (Z_to_bv 64 a) = MV (Z_to_bv 64 a)).
      { intros a Ha Hn. apply FRZ; [exact Ha | | | | |]; intros X; apply Hn; unfold Wpf, SOBUF; lia. }
      apply (drv_piece scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M model fx fx' R (Z_to_bv 64 0x633ac) R' (Z_to_bv 64 0xa7f98) MV' (Wpf S 0) K D MS GR FRW).
      + intros a [Ha|[Ha|[Ha|Ha]]]; unfold CWA; [right; left; lia | | |]; right; right.
        * exists 0x13bcc8, 0x13bfc0. split; [unfold IMG_W_A; cbn [In]; tauto | lia].
        * exists 0x13bcc8, 0x13bfc0. split; [unfold IMG_W_A; cbn [In]; tauto | lia].
        * exists 0x673d30, 0x6951b8. split; [unfold IMG_W_A; cbn [In]; tauto | unfold SOBUF in Ha; lia].
      + intros M1 model1 D1 SBM VIS FR1. apply (KONT fx' R' M1 model1 D1 SBM KS Q10); [|exact FR1 | rewrite VIS; exact FRW | rewrite VIS; exact GR].
        rewrite VIS. unfold stdoutA.
        assert (TR : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
                     (forall i, a <= i < a + Z.of_nat n -> ~ Wpf S 0 i) -> rdn ASEGS MV' (Z_to_bv 64 a) n = Some bs).
        { intros a n bs Hr Ha Hn Ho. apply (rdn_tr MV MV' a n bs Hr Ha Hn). intros i Hi. apply FRW; [lia | exact (Ho i Hi)]. }
        split; [exact O1|]. split; [apply TR; [exact F2 | lia | cbn; lia | intros i Hi; unfold Wpf, SOBUF; cbn in Hi; lia]|].
        split; [apply TR; [exact F3 | lia | cbn; lia | intros i Hi; unfold Wpf, SOBUF; cbn in Hi; lia]|].
        split; [exact O2|].
        split; [apply TR; [exact F5 | lia | cbn; lia | intros i Hi; unfold Wpf, SOBUF; cbn in Hi; lia]|].
        split; [apply TR; [exact F6 | lia | cbn; lia | intros i Hi; unfold Wpf, SOBUF; cbn in Hi; lia]|].
        split; [apply TR; [exact F7 | lia | cbn; lia | intros i Hi; unfold Wpf, SOBUF; cbn in Hi; lia]|].
        split; [intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MV' _ GR); apply (FW a n); assumption|].
        split; [intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MV' _ GR); apply (BW a n); assumption|].
        intros i Hi. destruct (Z.eq_dec i 0) as [->|N]; [split; [exact O4 | exact O3]|].
        destruct (BC i ltac:(lia)) as (B1 & B2).
        split; (apply TR; [assumption | unfold SOBUF; lia | unfold SOBUF; cbn; lia | intros x Hx; unfold Wpf, SOBUF in *; cbn in Hx; lia]).
  Qed.

  #[using="L C IL HIok ICok ILY Hsp DL Hpr"] Lemma printf3_run : forall LB LK cr A M (model : Model) R (S canz : Z) K,
    dinvA LB LK cr A M model ->
    let MV := mrestrict (ahid A model) M in
    usp - 4096 <= S -> S + 32 <= usp -> S mod 16 = 0 -> 0 <= canz < 2 ^ 64 ->
    getr R 1%bv = Z_to_bv 64 688024 -> getr R 2%bv = Z_to_bv 64 S -> getr R 10%bv = Z_to_bv 64 85514 -> getr R 11%bv = Z_to_bv 64 (S + 24) ->
    (forall a n, usp - 8388608 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV (Z_to_bv 64 (a + d)) k = true) ->
    (forall i, 65536 <= i < 1282048 -> MV (Z_to_bv 64 i) = None) ->
    rdn ASEGS MV (Z_to_bv 64 6896960) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 canz)) ->
    rdn ASEGS MV (Z_to_bv 64 (S + 24)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
    stdoutA 1 MV ->
    (forall (fx' : PropExec.FPState) R' M1 (model1 : Model),
        dinvA LB LK cr A M1 model1 -> same_but_materialized model model1 ->
        (forall x, In x AS0DRVP_dpA3.KS_dpA3 -> getr R' (Z_to_bv 5 (Z.of_nat x)) = getr R (Z_to_bv 5 (Z.of_nat x))) ->
        getr R' 10%bv = Z_to_bv 64 2 ->
        stdoutA 2 (mrestrict (ahid A model1) M1) ->
        (forall a, 0 <= a < 2 ^ 64 -> ~ Wpf S 1 a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
        (forall a, 0 <= a < 2 ^ 64 -> ~ Wpf S 1 a -> mrestrict (ahid A model1) M1 (Z_to_bv 64 a) = MV (Z_to_bv 64 a)) ->
        (forall a : word, MV a <> None -> mrestrict (ahid A model1) M1 a <> None) ->
        srealizes ASEGS scfg (mkCfg (@mkst fx' R' (Z_to_bv 64 0xa7f98) M1 rom) model1) K) ->
    srealizes ASEGS scfg (mkCfg (@mkst fx R (Z_to_bv 64 0x633ac) M rom) model) K.
  Proof.
    intros LB LK cr A M model R S canz K D MV HS1 HS2 HS16 Hcan R1 R2 R10 R11 WIN IMG CAN ARG SO KONT.
    pose proof Hsp as Hsp'. destruct SO as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & FW & BW & BC).
    assert (PC : forall a n v, In (a, n, v) PR_CELLS -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros a n v Hin; exact (pr_cell_vis scfg L ar C IL HI HIok sp0 Hsp DL Hpr M0 _ _ _ _ _ _ a n v D Hin)).
    assert (P1 : forall a v, In (a, 1, v) PR_CELLS -> 0 <= v < 2 ^ 64 -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros a v Hin Hv. rewrite <- (ArtMem.art_bytes1 v Hv). exact (PC a 1 v Hin). }
    set (V := fun n : nat => match n with 2%nat => S | 40%nat => canz | _ => 0 end).
    destruct (AS0DRVP_dpA3.dpA3_conc fx R MV V) as (fx' & R' & MV' & GR & _ & FRZ & MS & KS & _ & Q10 & _ & _ & _ & _ & _ & _ & _ & O1 & O2 & O3 & O4).
    all: cbn [V].
    all: try assumption.
    all: try (clear - Hsp' HS1 HS2 Hcan; lia).
    - (* [comment removed for export] *) intros d k Hd Hk. apply (WIN (S - 3232) 3232); lia.
    - (* [comment removed for export] *) intros i Hi. apply (store_ok_defined sp0); [lia|]. apply (WIN (S - 3232) 3232); lia.
    - (* [comment removed for export] *)
      intros i Hi. apply (stk_sh0 scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ _ D).
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      clear - Hsp' Hal HS1 HS2 HS16 Hi. lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    - (* [comment removed for export] *)
      apply BatFsInv_b.cell_zero_bytes; [right; reflexivity | lia | lia |]. intros j Hj. unfold byte_at.
      apply (img_sh0 scfg L ar IL HI ICok sp0 DL M0 _ _ _ _ _ _ 0x14dc0 64 _ D); [lia | lia | lia | | lia].
      rewrite (aicl_poison IL ILY). repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
    - apply BatFsInv_b.cell_zero_bytes; [right; reflexivity | lia | lia |]. intros j Hj. unfold byte_at.
      apply (img_sh0 scfg L ar IL HI ICok sp0 DL M0 _ _ _ _ _ _ 0x14e00 64 _ D); [lia | lia | lia | | lia].
      rewrite (aicl_poison IL ILY). repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
    - (* [comment removed for export] *)
      apply BatFsInv_b.cell_zero_bytes; [right; reflexivity | lia | lia |]. intros j Hj. unfold byte_at.
      apply (img_sh0 scfg L ar IL HI ICok sp0 DL M0 _ _ _ _ _ _ 0x694500 64 _ D); [lia | lia | lia | | lia].
      rewrite (aicl_poison IL ILY). repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
    - intros d k Hd Hk. apply (FW 1293752 4); lia.
    - intros d k Hd Hk. apply (FW 1293792 8); lia.
    - intros d k Hd Hk. apply (BW 6898978 1); unfold SOBUF; lia.
    - intros d k Hd Hk. apply (BW 6898979 1); unfold SOBUF; lia.
    - apply P1; [unfold PR_CELLS; cbn [In]; tauto | lia].
    - apply P1; [unfold PR_CELLS; cbn [In]; tauto | lia].
    - exact (PC 0x13fc38 8 0x7fff8000 ltac:(unfold PR_CELLS; cbn [In]; tauto)).
    - exact (PC 0x139348 8 0x1273fc ltac:(unfold PR_CELLS; cbn [In]; tauto)).
    - exact (PC 0x139350 8 0x121118 ltac:(unfold PR_CELLS; cbn [In]; tauto)).
    - apply P1; [unfold PR_CELLS; cbn [In]; tauto | lia].
    - exact (PC 0x1394c8 8 0x129900 ltac:(unfold PR_CELLS; cbn [In]; tauto)).
    - exact (PC 0x1394d0 8 0x129d04 ltac:(unfold PR_CELLS; cbn [In]; tauto)).
    - (* [comment removed for export] *)
      unfold V in FRZ, MS; cbn beta iota in FRZ, MS.
      assert (FRW : forall a, 0 <= a < 2 ^ 64 -> ~ Wpf S 1 a -> MV' (Z_to_bv 64 a) = MV (Z_to_bv 64 a)).
      { intros a Ha Hn. apply FRZ; [exact Ha | | | | |]; intros X; apply Hn; unfold Wpf, SOBUF; lia. }
      apply (drv_piece scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M model fx fx' R (Z_to_bv 64 0x633ac) R' (Z_to_bv 64 0xa7f98) MV' (Wpf S 1) K D MS GR FRW).
      + intros a [Ha|[Ha|[Ha|Ha]]]; unfold CWA; [right; left; lia | | |]; right; right.
        * exists 0x13bcc8, 0x13bfc0. split; [unfold IMG_W_A; cbn [In]; tauto | lia].
        * exists 0x13bcc8, 0x13bfc0. split; [unfold IMG_W_A; cbn [In]; tauto | lia].
        * exists 0x673d30, 0x6951b8. split; [unfold IMG_W_A; cbn [In]; tauto | unfold SOBUF in Ha; lia].
      + intros M1 model1 D1 SBM VIS FR1. apply (KONT fx' R' M1 model1 D1 SBM KS Q10); [|exact FR1 | rewrite VIS; exact FRW | rewrite VIS; exact GR].
        rewrite VIS. unfold stdoutA.
        assert (TR : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
                     (forall i, a <= i < a + Z.of_nat n -> ~ Wpf S 1 i) -> rdn ASEGS MV' (Z_to_bv 64 a) n = Some bs).
        { intros a n bs Hr Ha Hn Ho. apply (rdn_tr MV MV' a n bs Hr Ha Hn). intros i Hi. apply FRW; [lia | exact (Ho i Hi)]. }
        split; [exact O1|]. split; [apply TR; [exact F2 | lia | cbn; lia | intros i Hi; unfold Wpf, SOBUF; cbn in Hi; lia]|].
        split; [apply TR; [exact F3 | lia | cbn; lia | intros i Hi; unfold Wpf, SOBUF; cbn in Hi; lia]|].
        split; [exact O2|].
        split; [apply TR; [exact F5 | lia | cbn; lia | intros i Hi; unfold Wpf, SOBUF; cbn in Hi; lia]|].
        split; [apply TR; [exact F6 | lia | cbn; lia | intros i Hi; unfold Wpf, SOBUF; cbn in Hi; lia]|].
        split; [apply TR; [exact F7 | lia | cbn; lia | intros i Hi; unfold Wpf, SOBUF; cbn in Hi; lia]|].
        split; [intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MV' _ GR); apply (FW a n); assumption|].
        split; [intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MV' _ GR); apply (BW a n); assumption|].
        intros i Hi. destruct (Z.eq_dec i 1) as [->|N]; [split; [exact O4 | exact O3]|].
        destruct (BC i ltac:(lia)) as (B1 & B2).
        split; (apply TR; [assumption | unfold SOBUF; lia | unfold SOBUF; cbn; lia | intros x Hx; unfold Wpf, SOBUF in *; cbn in Hx; lia]).
  Qed.

  #[using="L C IL HIok ICok ILY Hsp DL Hpr"] Lemma printf4_run : forall LB LK cr A M (model : Model) R (S canz : Z) K,
    dinvA LB LK cr A M model ->
    let MV := mrestrict (ahid A model) M in
    usp - 4096 <= S -> S + 32 <= usp -> S mod 16 = 0 -> 0 <= canz < 2 ^ 64 ->
    getr R 1%bv = Z_to_bv 64 688024 -> getr R 2%bv = Z_to_bv 64 S -> getr R 10%bv = Z_to_bv 64 85514 -> getr R 11%bv = Z_to_bv 64 (S + 24) ->
    (forall a n, usp - 8388608 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV (Z_to_bv 64 (a + d)) k = true) ->
    (forall i, 65536 <= i < 1282048 -> MV (Z_to_bv 64 i) = None) ->
    rdn ASEGS MV (Z_to_bv 64 6896960) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 canz)) ->
    rdn ASEGS MV (Z_to_bv 64 (S + 24)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
    stdoutA 2 MV ->
    (forall (fx' : PropExec.FPState) R' M1 (model1 : Model),
        dinvA LB LK cr A M1 model1 -> same_but_materialized model model1 ->
        (forall x, In x AS0DRVP_dpA4.KS_dpA4 -> getr R' (Z_to_bv 5 (Z.of_nat x)) = getr R (Z_to_bv 5 (Z.of_nat x))) ->
        getr R' 10%bv = Z_to_bv 64 2 ->
        stdoutA 3 (mrestrict (ahid A model1) M1) ->
        (forall a, 0 <= a < 2 ^ 64 -> ~ Wpf S 2 a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
        (forall a, 0 <= a < 2 ^ 64 -> ~ Wpf S 2 a -> mrestrict (ahid A model1) M1 (Z_to_bv 64 a) = MV (Z_to_bv 64 a)) ->
        (forall a : word, MV a <> None -> mrestrict (ahid A model1) M1 a <> None) ->
        srealizes ASEGS scfg (mkCfg (@mkst fx' R' (Z_to_bv 64 0xa7f98) M1 rom) model1) K) ->
    srealizes ASEGS scfg (mkCfg (@mkst fx R (Z_to_bv 64 0x633ac) M rom) model) K.
  Proof.
    intros LB LK cr A M model R S canz K D MV HS1 HS2 HS16 Hcan R1 R2 R10 R11 WIN IMG CAN ARG SO KONT.
    pose proof Hsp as Hsp'. destruct SO as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & FW & BW & BC).
    assert (PC : forall a n v, In (a, n, v) PR_CELLS -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros a n v Hin; exact (pr_cell_vis scfg L ar C IL HI HIok sp0 Hsp DL Hpr M0 _ _ _ _ _ _ a n v D Hin)).
    assert (P1 : forall a v, In (a, 1, v) PR_CELLS -> 0 <= v < 2 ^ 64 -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros a v Hin Hv. rewrite <- (ArtMem.art_bytes1 v Hv). exact (PC a 1 v Hin). }
    set (V := fun n : nat => match n with 2%nat => S | 40%nat => canz | _ => 0 end).
    destruct (AS0DRVP_dpA4.dpA4_conc fx R MV V) as (fx' & R' & MV' & GR & _ & FRZ & MS & KS & _ & Q10 & _ & _ & _ & _ & _ & _ & _ & O1 & O2 & O3 & O4).
    all: cbn [V].
    all: try assumption.
    all: try (clear - Hsp' HS1 HS2 Hcan; lia).
    - (* [comment removed for export] *) intros d k Hd Hk. apply (WIN (S - 3232) 3232); lia.
    - (* [comment removed for export] *) intros i Hi. apply (store_ok_defined sp0); [lia|]. apply (WIN (S - 3232) 3232); lia.
    - (* [comment removed for export] *)
      intros i Hi. apply (stk_sh0 scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ _ D).
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      clear - Hsp' Hal HS1 HS2 HS16 Hi. lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    - (* [comment removed for export] *)
      apply BatFsInv_b.cell_zero_bytes; [right; reflexivity | lia | lia |]. intros j Hj. unfold byte_at.
      apply (img_sh0 scfg L ar IL HI ICok sp0 DL M0 _ _ _ _ _ _ 0x14dc0 64 _ D); [lia | lia | lia | | lia].
      rewrite (aicl_poison IL ILY). repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
    - apply BatFsInv_b.cell_zero_bytes; [right; reflexivity | lia | lia |]. intros j Hj. unfold byte_at.
      apply (img_sh0 scfg L ar IL HI ICok sp0 DL M0 _ _ _ _ _ _ 0x14e00 64 _ D); [lia | lia | lia | | lia].
      rewrite (aicl_poison IL ILY). repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
    - (* [comment removed for export] *)
      apply BatFsInv_b.cell_zero_bytes; [right; reflexivity | lia | lia |]. intros j Hj. unfold byte_at.
      apply (img_sh0 scfg L ar IL HI ICok sp0 DL M0 _ _ _ _ _ _ 0x694500 64 _ D); [lia | lia | lia | | lia].
      rewrite (aicl_poison IL ILY). repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
    - intros d k Hd Hk. apply (FW 1293752 4); lia.
    - intros d k Hd Hk. apply (FW 1293792 8); lia.
    - intros d k Hd Hk. apply (BW 6898980 1); unfold SOBUF; lia.
    - intros d k Hd Hk. apply (BW 6898981 1); unfold SOBUF; lia.
    - apply P1; [unfold PR_CELLS; cbn [In]; tauto | lia].
    - apply P1; [unfold PR_CELLS; cbn [In]; tauto | lia].
    - exact (PC 0x13fc38 8 0x7fff8000 ltac:(unfold PR_CELLS; cbn [In]; tauto)).
    - exact (PC 0x139348 8 0x1273fc ltac:(unfold PR_CELLS; cbn [In]; tauto)).
    - exact (PC 0x139350 8 0x121118 ltac:(unfold PR_CELLS; cbn [In]; tauto)).
    - apply P1; [unfold PR_CELLS; cbn [In]; tauto | lia].
    - exact (PC 0x1394c8 8 0x129900 ltac:(unfold PR_CELLS; cbn [In]; tauto)).
    - exact (PC 0x1394d0 8 0x129d04 ltac:(unfold PR_CELLS; cbn [In]; tauto)).
    - (* [comment removed for export] *)
      unfold V in FRZ, MS; cbn beta iota in FRZ, MS.
      assert (FRW : forall a, 0 <= a < 2 ^ 64 -> ~ Wpf S 2 a -> MV' (Z_to_bv 64 a) = MV (Z_to_bv 64 a)).
      { intros a Ha Hn. apply FRZ; [exact Ha | | | | |]; intros X; apply Hn; unfold Wpf, SOBUF; lia. }
      apply (drv_piece scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M model fx fx' R (Z_to_bv 64 0x633ac) R' (Z_to_bv 64 0xa7f98) MV' (Wpf S 2) K D MS GR FRW).
      + intros a [Ha|[Ha|[Ha|Ha]]]; unfold CWA; [right; left; lia | | |]; right; right.
        * exists 0x13bcc8, 0x13bfc0. split; [unfold IMG_W_A; cbn [In]; tauto | lia].
        * exists 0x13bcc8, 0x13bfc0. split; [unfold IMG_W_A; cbn [In]; tauto | lia].
        * exists 0x673d30, 0x6951b8. split; [unfold IMG_W_A; cbn [In]; tauto | unfold SOBUF in Ha; lia].
      + intros M1 model1 D1 SBM VIS FR1. apply (KONT fx' R' M1 model1 D1 SBM KS Q10); [|exact FR1 | rewrite VIS; exact FRW | rewrite VIS; exact GR].
        rewrite VIS. unfold stdoutA.
        assert (TR : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
                     (forall i, a <= i < a + Z.of_nat n -> ~ Wpf S 2 i) -> rdn ASEGS MV' (Z_to_bv 64 a) n = Some bs).
        { intros a n bs Hr Ha Hn Ho. apply (rdn_tr MV MV' a n bs Hr Ha Hn). intros i Hi. apply FRW; [lia | exact (Ho i Hi)]. }
        split; [exact O1|]. split; [apply TR; [exact F2 | lia | cbn; lia | intros i Hi; unfold Wpf, SOBUF; cbn in Hi; lia]|].
        split; [apply TR; [exact F3 | lia | cbn; lia | intros i Hi; unfold Wpf, SOBUF; cbn in Hi; lia]|].
        split; [exact O2|].
        split; [apply TR; [exact F5 | lia | cbn; lia | intros i Hi; unfold Wpf, SOBUF; cbn in Hi; lia]|].
        split; [apply TR; [exact F6 | lia | cbn; lia | intros i Hi; unfold Wpf, SOBUF; cbn in Hi; lia]|].
        split; [apply TR; [exact F7 | lia | cbn; lia | intros i Hi; unfold Wpf, SOBUF; cbn in Hi; lia]|].
        split; [intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MV' _ GR); apply (FW a n); assumption|].
        split; [intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MV' _ GR); apply (BW a n); assumption|].
        intros i Hi. destruct (Z.eq_dec i 2) as [->|N]; [split; [exact O4 | exact O3]|].
        destruct (BC i ltac:(lia)) as (B1 & B2).
        split; (apply TR; [assumption | unfold SOBUF; lia | unfold SOBUF; cbn; lia | intros x Hx; unfold Wpf, SOBUF in *; cbn in Hx; lia]).
  Qed.

End PrintfK.
End FPX_1.
