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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg ShapeLaws SpinAlg Hoare AgentLib Spec AsanAcctShape SymExec2 SymExec2Sound SymRun SymDrive SymDriveX
  HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import DrvKitA DrvNodesLazyK As0DrvKitA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0DrvEntry_b Ba0Drv_defs_b Ba0DrvLib_b Ba0DrvRead_b Ba0DrvPiece_b Ba0DiagLoopK_b Ba0DrvStdio_b Ba0DrvPrintfK_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require L5Defs L5KnA ArtMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require BatFsInv_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import Ba0DrvP_dpA_b Ba0DrvP_dpB_notty_b Ba0DrvP_dpCd_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition stdout0A (MV : word -> option byte) : Prop :=
  rdn ASEGS MV (Z_to_bv 64 1293892) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))             (* [comment removed for export] *)
  /\ rdn ASEGS MV (Z_to_bv 64 1293752) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5))                    (* [comment removed for export] *)
  /\ rdn ASEGS MV (Z_to_bv 64 1293848) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1024))                 (* [comment removed for export] *)
  /\ rdn ASEGS MV (Z_to_bv 64 1293784) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))                    (* [comment removed for export] *)
  /\ rdn ASEGS MV (Z_to_bv 64 1293888) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0))                    (* [comment removed for export] *)
  /\ rdn ASEGS MV (Z_to_bv 64 1293840) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 SOBUF))                (* [comment removed for export] *)
  /\ rdn ASEGS MV (Z_to_bv 64 1293896) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 10))                   (* [comment removed for export] *)
  /\ rdn ASEGS MV (Z_to_bv 64 1293824) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1183420))               (* [comment removed for export] *)
  /\ rdn ASEGS MV (Z_to_bv 64 1293872) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 1))                    (* [comment removed for export] *)
  /\ (forall a n, 1293752 <= a -> a + n <= 1293752 + 232 -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV (Z_to_bv 64 (a + d)) k = true)
  /\ (forall a n, SOBUF <= a -> a + n <= SOBUF + 1024 -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV (Z_to_bv 64 (a + d)) k = true).

(* [comment removed for export] *)
Definition stdoutXA (MV : word -> option byte) : Prop :=
  rdn ASEGS MV (Z_to_bv 64 1293824) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1180112))                  (* [comment removed for export] *)
  /\ rdn ASEGS MV (Z_to_bv 64 1293872) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 1))                    (* [comment removed for export] *)
  /\ rdn ASEGS MV (Z_to_bv 64 1293840) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 SOBUF))                (* [comment removed for export] *)
  /\ rdn ASEGS MV (Z_to_bv 64 1293760) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))                    (* [comment removed for export] *)
  /\ rdn ASEGS MV (Z_to_bv 64 1293768) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).                   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition Wpf1 (S a : Z) : Prop := S - 3232 <= a < S \/ 1293752 <= a < 1293752 + 232 \/ SOBUF <= a < SOBUF + 1024.

(* [comment removed for export] *)
Lemma TRf : forall (MVa MVb : word -> option byte) (W : Z -> Prop),
  (forall a, 0 <= a < 2 ^ 64 -> ~ W a -> MVb (Z_to_bv 64 a) = MVa (Z_to_bv 64 a)) ->
  forall a (n : nat) bs, rdn ASEGS MVa (Z_to_bv 64 a) n = Some bs -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, a <= i < a + Z.of_nat n -> ~ W i) -> rdn ASEGS MVb (Z_to_bv 64 a) n = Some bs.
Proof. intros MVa MVb W FR a n bs Hr Ha Hn Ho. apply (rdn_tr MVa MVb a n bs Hr Ha Hn). intros i Hi. apply FR; [lia | exact (Ho i Hi)]. Qed.

Lemma le4_m1 : word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615) = word_to_le_bytes 4 (Z_to_bv 64 4294967295).
Proof. vm_compute. repeat (apply f_equal2; [apply bv_eq; reflexivity|]). reflexivity. Qed.
Lemma nl_imgA : rdn ASEGS (fun _ => None) (Z_to_bv 64 85516) 1 = Some [Z_to_bv 8 10].
Proof. vm_compute. reflexivity. Qed.
Lemma fetch_ioctlA : fetch_word ASEGS (Z_to_bv 64 0x120f18) = Some ECALLW.
Proof. vm_compute. reflexivity. Qed.

Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section Printf1.
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

  (* [comment removed for export] *)
  #[using="scfg L C IL HIok Hsp DL"] Lemma nl_pt : forall LB LK cr A M (model : Model) x, dinvA LB LK cr A M model -> 0 <= x < 2 ^ 64 -> (x < 0x696000 \/ usp - 8388608 <= x) ->
    page_in_ranges (page_base_of x) (m_vm_lazy model) = false.
  Proof.
    intros LB LK cr A M model x D Hx Hc.
    assert (U : bv_unsigned (Z_to_bv 64 x) = x) by (apply u64_lit; lia).
    pose proof (nolazy_of_inv scfg L ar C IL HI HIok sp0 Hsp DL _ _ _ _ _ _ model (Z_to_bv 64 x) 1 (di_inv _ _ _ _ _ _ _ _ _ _ D) ltac:(rewrite U; lia)) as X.
    assert (Y : forall k, 0 <= k < 1 -> bv_unsigned (Z_to_bv 64 x) + k < 6905856 \/ usp - 8388608 <= bv_unsigned (Z_to_bv 64 x) + k \/ in_block LB (bv_unsigned (Z_to_bv 64 x) + k))
      by (intros k Hk; rewrite U; destruct Hc; [left | right; left]; lia).
    specialize (X Y 0 ltac:(lia)). rewrite U, Z.add_0_r in X. exact X.
  Qed.

  #[using="L C IL HIok ICok ILY Hsp DL Hpr"] Lemma printf1_run : forall LB LK cr A M (model : Model) R (S canz : Z) K,
    dinvA LB LK cr A M model ->
    let MV := mrestrict (ahid A model) M in
    usp - 4096 <= S -> S + 32 <= usp -> S mod 16 = 0 -> 0 <= canz < 2 ^ 64 ->
    getr R 1%bv = Z_to_bv 64 688024 -> getr R 2%bv = Z_to_bv 64 S -> getr R 10%bv = Z_to_bv 64 85514 -> getr R 11%bv = Z_to_bv 64 (S + 24) ->
    (forall a n, usp - 8388608 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV (Z_to_bv 64 (a + d)) k = true) ->
    (forall i, 65536 <= i < 1282048 -> MV (Z_to_bv 64 i) = None) ->
    rdn ASEGS MV (Z_to_bv 64 6896960) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 canz)) ->
    rdn ASEGS MV (Z_to_bv 64 (S + 24)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
    stdout0A MV ->
    fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
    K [] ->
    (forall (fx' : PropExec.FPState) R' M1 (model1 : Model),
        dinvA LB LK cr A M1 model1 -> same_but_materialized model model1 ->
        (forall r, In r c_kept -> getr R' r = getr R r) ->
        getr R' 10%bv = Z_to_bv 64 2 ->
        stdoutA 0 (mrestrict (ahid A model1) M1) -> stdoutXA (mrestrict (ahid A model1) M1) ->
        (forall a, 0 <= a < 2 ^ 64 -> ~ Wpf1 S a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
        (forall a, 0 <= a < 2 ^ 64 -> ~ Wpf1 S a -> mrestrict (ahid A model1) M1 (Z_to_bv 64 a) = MV (Z_to_bv 64 a)) ->
        (forall a : word, MV a <> None -> mrestrict (ahid A model1) M1 a <> None) ->
        srealizes ASEGS scfg (mkCfg (@mkst fx' R' (Z_to_bv 64 0xa7f98) M1 rom) model1) K) ->
    srealizes ASEGS scfg (mkCfg (@mkst fx R (Z_to_bv 64 0x633ac) M rom) model) (t_emit (W 1 [Z_to_bv 8 48; Z_to_bv 8 10]) K).
  Proof.
    intros LB LK cr A M model R S canz K D MV HS1 HS2 HS16 Hcan R1 R2 R10 R11 WIN IMG CAN ARG SO FD1 HK0 KONT.
    pose proof Hsp as Hsp'. destruct SO as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & FW & BW).
    assert (PCg : forall LK' cr' A' M' (model' : Model), dinvA LB LK' cr' A' M' model' -> forall a n v, In (a, n, v) PR_CELLS ->
                  rdn ASEGS (mrestrict (ahid A' model') M') (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros LK' cr' A' M' model' D' a n v Hin; exact (pr_cell_vis scfg L ar C IL HI HIok sp0 Hsp DL Hpr M0 _ _ _ _ _ _ a n v D' Hin)).
    assert (P1g : forall LK' cr' A' M' (model' : Model), dinvA LB LK' cr' A' M' model' -> forall a v, In (a, 1, v) PR_CELLS -> 0 <= v < 2 ^ 64 ->
                  rdn ASEGS (mrestrict (ahid A' model') M') (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros LK' cr' A' M' model' D' a v Hin Hv. rewrite <- (ArtMem.art_bytes1 v Hv). exact (PCg _ _ _ _ _ D' a 1 v Hin). }
    (* [comment removed for export] *)
    set (V := fun n : nat => match n with 2%nat => S | 40%nat => canz | _ => 0 end).
    destruct (AS0DRVP_dpA.dpA_conc fx R MV V) as
(fx1 & R1' & MV1 & AGR & _ & AFRZ & AMS & AKS & Ar1 & Ar2 & Ar5 & Ar8 & Ar9 & Ar10 & Ar11 & Ar12 & Ar13 & Ar14 & Ar15 & Ar16 & Ar17 & Ar18 & Ar19 & Ar20 & Ar21 & Ar22 & Ar23 & Ar24 & Ar25 & Ar26 & Ar27 & Aa892264 & Am1096 & Am1088 & Am1080 & Am1064 & Am1056 & Am1048 & Am1040 & Am1032 & Am1024 & Am1016 & Aa892232 & Am1104 & Aa6361368 & Am832 & Am1072 & Am1000 & Am976 & Am992 & Am1008 & Am984 & Am896 & Am464 & Am968 & Am960 & Am904 & Am928 & Am576 & Am912 & Am920 & Am936 & Am952 & Am944 & Am568 & Am560 & Am552 & Am544 & Am536 & Am528 & Am520 & Am512 & Am504 & Am496 & Am488 & Am480 & Am472 & Aa892224 & Aa892208 & Aa892200 & Aa892248 & Aa892328 & Aa892192 & Am176 & Am184 & Am192 & Am200 & Am168 & Am456 & Am160 & Am152 & Am144 & Am136 & Am128 & Am120 & Am112 & Am104 & Am96 & Am88 & Am80 & Am72 & Am64 & Am56 & Am40 & Am32 & Am24 & Am16 & Am8 & Ad1 & Ad2 & Ad3 & Ad4).
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
    - intros d k Hd Hk. apply (FW 1293760 8); lia.
    - intros d k Hd Hk. apply (FW 1293768 8); lia.
    - intros d k Hd Hk. apply (FW 1293784 8); lia.
    - intros d k Hd Hk. apply (FW 1293792 8); lia.
    - intros d k Hd Hk. apply (FW 1293808 8); lia.
    - intros d k Hd Hk. apply (FW 1293824 8); lia.
    - intros d k Hd Hk. apply (FW 1293888 4); lia.
    - intros d k Hd Hk. apply (BW 6898976 1); unfold SOBUF; lia.
    - apply (P1g _ _ _ _ _ D); [unfold PR_CELLS; cbn [In]; tauto | lia].
    - apply (P1g _ _ _ _ _ D); [unfold PR_CELLS; cbn [In]; tauto | lia].
    - exact (PCg _ _ _ _ _ D 0x13fc38 8 0x7fff8000 ltac:(unfold PR_CELLS; cbn [In]; tauto)).
    - exact (PCg _ _ _ _ _ D 0x139348 8 0x1273fc ltac:(unfold PR_CELLS; cbn [In]; tauto)).
    - exact (PCg _ _ _ _ _ D 0x139350 8 0x121118 ltac:(unfold PR_CELLS; cbn [In]; tauto)).
    - apply (P1g _ _ _ _ _ D); [unfold PR_CELLS; cbn [In]; tauto | lia].
    - exact (PCg _ _ _ _ _ D 0x1394c8 8 0x129900 ltac:(unfold PR_CELLS; cbn [In]; tauto)).
    - exact (PCg _ _ _ _ _ D 0x1394d0 8 0x129d04 ltac:(unfold PR_CELLS; cbn [In]; tauto)).
    - (* [comment removed for export] *)
      unfold V in AFRZ, AMS; cbn beta iota in AFRZ, AMS. cbn [V] in *.
      set (WA := fun a : Z => S - 3232 <= a < S \/ 1293752 <= a < 1293756 \/ 1293760 <= a < 1293776 \/ 1293784 <= a < 1293800 \/ 1293808 <= a < 1293816 \/ 1293824 <= a < 1293832 \/ 1293888 <= a < 1293892 \/ a = 6898976).
      assert (FRA : forall a, 0 <= a < 2 ^ 64 -> ~ WA a -> MV1 (Z_to_bv 64 a) = MV (Z_to_bv 64 a)).
      { intros a Ha Hn. apply AFRZ; [exact Ha | | | | | | | | | |]; intros X; apply Hn; unfold WA; lia. }
      apply (drv_piece scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M model fx fx1 R (Z_to_bv 64 0x633ac) R1' (Z_to_bv 64 0x120f18) MV1 WA _ D AMS AGR FRA).
      { intros a Ha. unfold CWA. destruct Ha as [Ha|Ha]; [right; left; clear - Hsp' HS1 HS2 Ha; lia|]. right; right.
        destruct (Z.eq_dec a 6898976) as [->|Ne].
        - exists 0x673d30, 0x6951b8. split; [unfold IMG_W_A; cbn [In]; tauto | lia].
        - exists 0x13bcc8, 0x13bfc0. split; [unfold IMG_W_A; cbn [In]; tauto | clear - Ha Ne; lia]. }
      intros M1 model1 D1 SBM1 VIS1 FRM1.
      subst MV1.
      set (MVa := mrestrict (ahid A model1) M1) in *.
      (* [comment removed for export] *)
      assert (WIN1 : forall a n, usp - 8388608 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MVa (Z_to_bv 64 (a + d)) k = true)
        by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MVa _ AGR); apply (WIN a n); assumption).
      assert (FW1 : forall a n, 1293752 <= a -> a + n <= 1293752 + 232 -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MVa (Z_to_bv 64 (a + d)) k = true)
        by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MVa _ AGR); apply (FW a n); assumption).
      assert (BW1 : forall a n, SOBUF <= a -> a + n <= SOBUF + 1024 -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MVa (Z_to_bv 64 (a + d)) k = true)
        by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MVa _ AGR); apply (BW a n); assumption).
      assert (IMG1 : forall i, 65536 <= i < 1282048 -> MVa (Z_to_bv 64 i) = None).
      { intros i Hi. rewrite FRA; [apply IMG; exact Hi | lia | unfold WA; clear - Hsp' HS1 HS2 Hi; lia]. }
      assert (CAN1 : rdn ASEGS MVa (Z_to_bv 64 6896960) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 canz))).
      { apply (TRf _ _ _ FRA _ _ _ CAN); [lia | cbn; lia | intros i Hi X; unfold WA in X; cbn in Hi; clear - Hsp' HS1 HS2 Hi X; lia]. }
      assert (F1a : rdn ASEGS MVa (Z_to_bv 64 1293892) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))).
      { apply (TRf _ _ _ FRA _ _ _ F1); [lia | cbn; lia | intros i Hi X; unfold WA in X; cbn in Hi; clear - Hsp' HS1 HS2 Hi X; lia]. }
      assert (F3a : rdn ASEGS MVa (Z_to_bv 64 1293848) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1024))).
      { apply (TRf _ _ _ FRA _ _ _ F3); [lia | cbn; lia | intros i Hi X; unfold WA in X; cbn in Hi; clear - Hsp' HS1 HS2 Hi X; lia]. }
      assert (F6a : rdn ASEGS MVa (Z_to_bv 64 1293840) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 SOBUF))).
      { apply (TRf _ _ _ FRA _ _ _ F6); [lia | cbn; lia | intros i Hi X; unfold WA in X; cbn in Hi; clear - Hsp' HS1 HS2 Hi X; lia]. }
      assert (F9a : rdn ASEGS MVa (Z_to_bv 64 1293872) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 1))).
      { apply (TRf _ _ _ FRA _ _ _ F9); [lia | cbn; lia | intros i Hi X; unfold WA in X; cbn in Hi; clear - Hsp' HS1 HS2 Hi X; lia]. }
      assert (FD1a : fd_lookup (m_fds model1) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))) by (rewrite (sbm_fds' _ _ SBM1); exact FD1).
      (* [comment removed for export] *)
      eapply (rz_ioctl_winsz_lz ASEGS scfg R1' _ M1 model1 ECALLW (Z_to_bv 64 1) (FdChannel (Z_to_bv 64 1)));
        [exact fetch_ioctlA | apply is_ecall_ECALLW | exact (di_halt _ _ _ _ _ _ _ _ _ _ D1) | exact Ar17 | exact Ar10 | rewrite u64_lit by lia; lia
        | exact FD1a | reflexivity | exact Ar11 |].
      rewrite v_addi_pc4 by lia. change (0x120f18 + 4) with 0x120f1c.
      set (R1b := regupd R1' 10%bv (errno_ret ENOTTY)).
      assert (RBo : forall r : reg, r <> 10%bv -> getr R1b r = getr R1' r) by (intros r Hr; unfold R1b; apply getr_other; exact Hr).
      assert (RB10 : getr R1b 10%bv = Z_to_bv 64 18446744073709551591).
      { unfold R1b. rewrite getr_same by (intros X; discriminate X). rewrite errno_ret_lit. apply bv_eq. reflexivity. }
      (* [comment removed for export] *)
      set (VB := fun n : nat => match n with 2%nat => S - 1104 | 40%nat => canz | _ => 0 end).
      assert (Bg2 : getr R1b (Z_to_bv 5 (Z.of_nat 2)) = Z_to_bv 64 (S - 1104)) by (rewrite RBo by (intros X; discriminate X); exact Ar2).
      assert (Bg8 : getr R1b (Z_to_bv 5 (Z.of_nat 8)) = Z_to_bv 64 6896960) by (rewrite RBo by (intros X; discriminate X); exact Ar8).
      assert (Bg9 : getr R1b (Z_to_bv 5 (Z.of_nat 9)) = Z_to_bv 64 1) by (rewrite RBo by (intros X; discriminate X); exact Ar9).
      assert (Bg13 : getr R1b (Z_to_bv 5 (Z.of_nat 13)) = Z_to_bv 64 85516) by (rewrite RBo by (intros X; discriminate X); exact Ar13).
      assert (Bg15 : getr R1b (Z_to_bv 5 (Z.of_nat 15)) = Z_to_bv 64 1) by (rewrite RBo by (intros X; discriminate X); exact Ar15).
      assert (Bg16 : getr R1b (Z_to_bv 5 (Z.of_nat 16)) = Z_to_bv 64 1293752) by (rewrite RBo by (intros X; discriminate X); exact Ar16).
      assert (Bg18 : getr R1b (Z_to_bv 5 (Z.of_nat 18)) = Z_to_bv 64 85516) by (rewrite RBo by (intros X; discriminate X); exact Ar18).
      assert (Bg19 : getr R1b (Z_to_bv 5 (Z.of_nat 19)) = Z_to_bv 64 1) by (rewrite RBo by (intros X; discriminate X); exact Ar19).
      assert (Bg20 : getr R1b (Z_to_bv 5 (Z.of_nat 20)) = Z_to_bv 64 0) by (rewrite RBo by (intros X; discriminate X); exact Ar20).
      assert (Bg21 : getr R1b (Z_to_bv 5 (Z.of_nat 21)) = Z_to_bv 64 85517) by (rewrite RBo by (intros X; discriminate X); exact Ar21).
      assert (Bg22 : getr R1b (Z_to_bv 5 (Z.of_nat 22)) = Z_to_bv 64 1) by (rewrite RBo by (intros X; discriminate X); exact Ar22).
      destruct (AS0DRVP_dpB_notty.dpB_notty_conc fx1 R1b MVa VB ltac:(cbn [VB]; clear - Hsp' HS1 HS2; lia) Hcan Bg2 Bg8 Bg9 RB10 Bg13 Bg15 Bg16 Bg18 Bg19 Bg20 Bg21 Bg22
                  ltac:(cbn [VB]; clear - Hsp' HS1 HS2; lia)) as
(fx2 & R2' & MV2 & BGR & _ & BFRZ & BMS & BKS & Br1 & Br2 & Br8 & Br9 & Br10 & Br11 & Br12 & Br13 & Br17 & Br18 & Br19 & Br21 & Br22 & Bm80 & Bm88 & Bm96 & Bm104 & Bm72 & Bm64 & Bm56 & Bm48 & Bm40 & Bm32 & Bm24 & Bm16 & Bm8 & Ba892336 & Bd1).
      all: cbn [VB].
      { unfold AS0DRVP_dpB_notty.aligned. clear - HS16. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
      { intros d k Hd Hk. apply (WIN1 (S - 1104 - 112) 112); clear - Hsp' HS1 HS2 Hd Hk; lia. }
      { intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN1 (S - 1104 - 112) 112); clear - Hsp' HS1 HS2 Hi; lia. }
      { exact IMG1. }
      { intros d k Hd Hk. apply (FW1 1293896 4); lia. }
      { exact CAN1. }
      { exact Aa892232. }
      { exact Aa892248. }
      { exact F9a. }
      unfold VB in BFRZ, BMS; cbn beta iota in BFRZ, BMS. cbn [VB] in *.
      set (WB := fun a : Z => S - 1216 <= a < S - 1104 \/ 1293896 <= a < 1293900).
      assert (FRB : forall a, 0 <= a < 2 ^ 64 -> ~ WB a -> MV2 (Z_to_bv 64 a) = MVa (Z_to_bv 64 a)).
      { intros a Ha Hn. apply BFRZ; [exact Ha | |]; intros X; apply Hn; unfold WB; clear - X; lia. }
      apply (drv_piece scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M1 model1 fx1 fx2 R1b (Z_to_bv 64 0x120f1c) R2' (Z_to_bv 64 0x120258) MV2 WB _ D1 BMS BGR FRB).
      { intros a Ha. unfold CWA. destruct Ha as [Ha|Ha]; [right; left; clear - Hsp' HS1 HS2 Ha; lia|]. right; right.
        exists 0x13bcc8, 0x13bfc0. split; [unfold IMG_W_A; cbn [In]; tauto | clear - Ha; lia]. }
      intros M2 model2 D2 SBM2 VIS2 FRM2.
      subst MV2. set (MVb := mrestrict (ahid A model2) M2) in *.
      (* [comment removed for export] *)
      assert (WIN2 : forall a n, usp - 8388608 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MVb (Z_to_bv 64 (a + d)) k = true)
        by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MVa MVb _ BGR); apply (WIN1 a n); assumption).
      assert (IMG2 : forall i, 65536 <= i < 1282048 -> MVb (Z_to_bv 64 i) = None).
      { intros i Hi. rewrite FRB; [apply IMG1; exact Hi | lia | unfold WB; clear - Hsp' HS1 HS2 Hi; lia]. }
      assert (F9b : rdn ASEGS MVb (Z_to_bv 64 1293872) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 1))).
      { apply (TRf _ _ _ FRB _ _ _ F9a); [lia | cbn; lia | intros i Hi X; unfold WB in X; cbn in Hi; clear - Hsp' HS1 HS2 Hi X; lia]. }
      assert (DATA1 : rdn ASEGS MVb (Z_to_bv 64 6898976) 1 = Some [Z_to_bv 8 48]).
      { apply (TRf _ _ _ FRB _ _ _ Aa6361368); [lia | cbn; lia | intros i Hi X; unfold WB in X; cbn in Hi; clear - Hsp' HS1 HS2 Hi X; lia]. }
      assert (DATA2 : rdn ASEGS MVb (Z_to_bv 64 85516) 1 = Some [Z_to_bv 8 10]).
      { apply (img_cell MVb 85516 1 _ nl_imgA); [lia | cbn; lia | intros i Hi; apply IMG2; cbn in Hi; lia]. }
      assert (FD1b : fd_lookup (m_fds model2) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))) by (rewrite (sbm_fds' _ _ SBM2); exact FD1a).
      (* [comment removed for export] *)
      pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D2) as (HH2 & HL2 & HA2 & HM2 & Hh2).
      set (q := S - 1104 - 104) in *.
      assert (Hq : 0 <= q /\ q <= q + 32 /\ q + 32 + 16 <= 2 ^ 47) by (unfold q; clear - Hsp' HS1 HS2; lia).
      assert (Hf : 0 <= 1293752 /\ (1293752 + 124 <= q \/ q + 32 + 16 <= 1293752 + 120) /\ 1293752 + 124 < 2 ^ 63) by (unfold q; clear - Hsp' HS1 HS2; lia).
      assert (NLq : forall x, q <= x < q + 32 -> page_in_ranges (page_base_of x) (m_vm_lazy model2) = false).
      { intros x Hx. apply (nl_pt _ _ _ _ _ _ x D2); unfold q in Hx; clear - Hsp' HS1 HS2 Hx; lia. }
      unfold W. change (map (WriteEv (Z_to_bv 64 1)) [Z_to_bv 8 48; Z_to_bv 8 10]) with (map (WriteEv (Z_to_bv 64 1)) ([Z_to_bv 8 48] ++ [Z_to_bv 8 10])).
      apply (wv_loop scfg (ahid A model2) A HH2 (m_vm_lazy model2) HL2 HA2 1293752 1 ltac:(lia) q (q + 32) Hq Hf NLq K HK0 2%nat true R2' M2 model2 q 2 6898976 1 85516 1 [Z_to_bv 8 48] [Z_to_bv 8 10]).
      { cbn. lia. }
      { reflexivity. }
      { exact HM2. }
      { exact Hh2. }
      { exact FD1b. }
      { unfold wv_regs. repeat split; try assumption. }
      { fold MVb. unfold wv_iov. split; [lia|]. split; [lia|]. split; [right; reflexivity|].
        split; [exact Bm104|]. split; [replace (q + 8) with (S - 1104 - 96) by (unfold q; ring); exact Bm96|].
        split; [replace (Z_to_bv 64 q) with (Z_to_bv 64 (q + 0)) by (f_equal; lia); apply (WIN2 q 32); [unfold q; clear - Hsp' HS1 HS2; lia | unfold q; clear - Hsp' HS1 HS2; lia | lia | cbn; lia]|].
        split; [unfold wv_buf; split; [lia|]; split; [lia|]; split; [lia|]; split; [right; left; unfold q; clear - Hsp' HS1 HS2; lia|]; split; [exact DATA1|];
                intros x Hx; apply (nl_pt _ _ _ _ _ _ x D2); lia|].
        split; [intros X; discriminate X|]. intros _.
        split; [replace (q + 16) with (S - 1104 - 88) by (unfold q; ring); exact Bm88|].
        split; [replace (q + 24) with (S - 1104 - 80) by (unfold q; ring); exact Bm80|].
        split; [|lia].
        unfold wv_buf; split; [lia|]; split; [lia|]; split; [lia|]; split; [right; left; unfold q; clear - Hsp' HS1 HS2; lia|]; split; [exact DATA2|].
        intros x Hx; apply (nl_pt _ _ _ _ _ _ x D2); lia. }
      { lia. }
      { exact F9b. }
      (* [comment removed for export] *)
      intros R3 M3 model3 MI3 SBM3 KR3 FRM3 FRV3 GRM3 GRV3.
      assert (D3 : dinvA LB LK cr A M3 model3).
      { apply (dinv_frame scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M2 M3 model2 model3 D2).
        - intros a Ha Hn. apply FRM3; [exact Ha|]. intros X. apply Hn. unfold CWA. right; left. unfold q in X. clear - Hsp' HS1 HS2 X. lia.
        - exact GRM3.
        - exact (sbm_vml _ _ SBM3).
        - exact MI3.
        - rewrite (sbm_halted_eq _ _ SBM3). exact Hh2. }
      pose proof (ahid_sbm A model2 model3 SBM3) as AH3.
      set (MVc := mrestrict (ahid A model3) M3) in *.
      assert (EQc : mrestrict (ahid A model2) M3 = MVc) by (unfold MVc; rewrite AH3; reflexivity).
      rewrite EQc in FRV3, GRV3. fold MVb in FRV3, GRV3.
      set (SC := S - 1104 - 112) in *.
      assert (FRca : forall i, 0 <= i < 2 ^ 64 -> ~ (SC <= i < S - 1104) -> ~ (1293896 <= i < 1293900) -> MVc (Z_to_bv 64 i) = MVa (Z_to_bv 64 i)).
      { intros i Hi N1 N2. rewrite FRV3 by (unfold q, SC in *; clear - Hi N1; lia). apply FRB; [exact Hi | unfold WB, SC in *; clear - N1 N2; lia]. }
      assert (cellA : forall off k (n : nat) bs, rdn ASEGS MVa (Z_to_bv 64 (S - k)) n = Some bs ->
                (off + k =? 1216) && (Z.of_nat n <=? k) && (k <=? 1104) = true -> rdn ASEGS MVc (Z_to_bv 64 (SC + off)) n = Some bs).
      { intros off k n bs Hr Hb. apply andb_prop in Hb as (Hb & Hb3). apply andb_prop in Hb as (Hb1 & Hb2).
        apply Z.eqb_eq in Hb1. apply Z.leb_le in Hb2, Hb3. replace (SC + off) with (S - k) by (unfold SC; lia).
        apply (rdn_tr MVa MVc _ _ _ Hr); [clear - Hsp' HS1 HS2 Hb3; lia | clear - Hsp' HS1 HS2 Hb2; lia|].
        intros i Hi. apply FRca; unfold SC; clear - Hsp' HS1 HS2 Hb2 Hb3 Hi; lia. }
      assert (cellB : forall off k (n : nat) bs, rdn ASEGS MVb (Z_to_bv 64 (S - 1104 - k)) n = Some bs ->
                (off + k =? 112) && (Z.of_nat n <=? k) && (k <=? 72) = true -> rdn ASEGS MVc (Z_to_bv 64 (SC + off)) n = Some bs).
      { intros off k n bs Hr Hb. apply andb_prop in Hb as (Hb & Hb3). apply andb_prop in Hb as (Hb1 & Hb2).
        apply Z.eqb_eq in Hb1. apply Z.leb_le in Hb2, Hb3. replace (SC + off) with (S - 1104 - k) by (unfold SC; lia).
        apply (rdn_tr MVb MVc _ _ _ Hr); [clear - Hsp' HS1 HS2 Hb3; lia | clear - Hsp' HS1 HS2 Hb2; lia|].
        intros i Hi. apply FRV3; unfold q; clear - Hsp' HS1 HS2 Hb2 Hb3 Hi; lia. }
      assert (cellL : forall a (n : nat) bs, rdn ASEGS MVa (Z_to_bv 64 a) n = Some bs ->
                (0 <=? a) && (a + Z.of_nat n <=? 10000000) && ((a + Z.of_nat n <=? 1293896) || (1293900 <=? a)) = true -> rdn ASEGS MVc (Z_to_bv 64 a) n = Some bs).
      { intros a n bs Hr Hb. apply andb_prop in Hb as (Hb & Hb3). apply andb_prop in Hb as (Hb1 & Hb2).
        apply Z.leb_le in Hb1, Hb2. apply orb_prop in Hb3. rewrite !Z.leb_le in Hb3.
        apply (rdn_tr MVa MVc _ _ _ Hr); [exact Hb1 | lia|].
        intros i Hi. apply FRca; unfold SC; clear - Hsp' HS1 HS2 Hb1 Hb2 Hb3 Hi; lia. }
      assert (WIN3 : forall a n, usp - 8388608 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MVc (Z_to_bv 64 (a + d)) k = true)
        by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MVb MVc _ GRV3); apply (WIN2 a n); assumption).
      assert (FW3 : forall a n, 1293752 <= a -> a + n <= 1293752 + 232 -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MVc (Z_to_bv 64 (a + d)) k = true)
        by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MVb MVc _ GRV3); apply (store_ok_mono ASEGS k MVa MVb _ BGR); apply (FW1 a n); assumption).
      assert (IMG3 : forall i, 65536 <= i < 1282048 -> MVc (Z_to_bv 64 i) = None).
      { intros i Hi. rewrite FRV3; [apply IMG2; exact Hi | lia | unfold q; clear - Hsp' HS1 HS2 Hi; lia]. }
      assert (ST910489 : rdn ASEGS MVc (Z_to_bv 64 1313049) 1 = Some [Z_to_bv 8 1]) by (apply (P1g _ _ _ _ _ D3); [unfold PR_CELLS; cbn [In]; tauto | lia]).
      assert (ST881824 : rdn ASEGS MVc (Z_to_bv 64 1283272) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1218816)))
        by exact (PCg _ _ _ _ _ D3 0x1394c8 8 0x129900 ltac:(unfold PR_CELLS; cbn [In]; tauto)).
      (* [comment removed for export] *)
      assert (R3k : forall r : reg, In r WV_KEEP -> getr R3 r = getr R2' r) by exact KR3.
      assert (R2k : forall x, In x AS0DRVP_dpB_notty.KS_dpB_notty -> getr R2' (Z_to_bv 5 (Z.of_nat x)) = getr R1' (Z_to_bv 5 (Z.of_nat x))).
      { intros x Hx. rewrite (BKS x Hx). apply RBo. intros X. unfold AS0DRVP_dpB_notty.KS_dpB_notty in Hx. cbn [In] in Hx.
        repeat (destruct Hx as [<-|Hx]; [discriminate X|]). exact Hx. }
      set (VC := fun n : nat => match n with
                 | 2%nat => SC | 40%nat => canz
                 | 8%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 8))) | 9%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 9)))
                 | 18%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 18))) | 19%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 19)))
                 | 20%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 20))) | 21%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 21)))
                 | 22%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 22))) | 23%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 23)))
                 | 24%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 24))) | 25%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 25)))
                 | 26%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 26))) | 27%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 27)))
                 | 118%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 18))) | 119%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 19)))
                 | 120%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 20))) | 122%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 22)))
                 | 125%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 25))) | 127%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 27)))
                 | _ => 0 end).
      assert (Cg2 : getr R3 (Z_to_bv 5 (Z.of_nat 2)) = Z_to_bv 64 (VC 2%nat)) by (eapply eq_trans; [exact (R3k 2%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Br2]).
      assert (Cg8 : getr R3 (Z_to_bv 5 (Z.of_nat 8)) = Z_to_bv 64 1) by (eapply eq_trans; [exact (R3k 8%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Br8]).
      assert (Cg9 : getr R3 (Z_to_bv 5 (Z.of_nat 9)) = Z_to_bv 64 1293752) by (eapply eq_trans; [exact (R3k 9%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Br9]).
      assert (Cg21 : getr R3 (Z_to_bv 5 (Z.of_nat 21)) = Z_to_bv 64 6896960) by (eapply eq_trans; [exact (R3k 21%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Br21]).
      assert (Cg23 : getr R3 (Z_to_bv 5 (Z.of_nat 23)) = Z_to_bv 64 85516).
      { eapply eq_trans; [exact (R3k 23%bv ltac:(unfold WV_KEEP; cbn [In]; tauto))|]. eapply eq_trans; [|exact Ar23]. apply (R2k 23%nat). unfold AS0DRVP_dpB_notty.KS_dpB_notty. cbn [In]. tauto. }
      assert (Cg24 : getr R3 (Z_to_bv 5 (Z.of_nat 24)) = Z_to_bv 64 1).
      { eapply eq_trans; [exact (R3k 24%bv ltac:(unfold WV_KEEP; cbn [In]; tauto))|]. eapply eq_trans; [|exact Ar24]. apply (R2k 24%nat). unfold AS0DRVP_dpB_notty.KS_dpB_notty. cbn [In]. tauto. }
      assert (Cg26 : getr R3 (Z_to_bv 5 (Z.of_nat 26)) = Z_to_bv 64 1).
      { eapply eq_trans; [exact (R3k 26%bv ltac:(unfold WV_KEEP; cbn [In]; tauto))|]. eapply eq_trans; [|exact Ar26]. apply (R2k 26%nat). unfold AS0DRVP_dpB_notty.KS_dpB_notty. cbn [In]. tauto. }
      assert (Cg18 : getr R3 (Z_to_bv 5 (Z.of_nat 18)) = Z_to_bv 64 (VC 118%nat)) by (cbn [VC]; symmetry; apply Z_to_bv_bv_unsigned).
      assert (Cg19 : getr R3 (Z_to_bv 5 (Z.of_nat 19)) = Z_to_bv 64 (VC 119%nat)) by (cbn [VC]; symmetry; apply Z_to_bv_bv_unsigned).
      assert (Cg20 : getr R3 (Z_to_bv 5 (Z.of_nat 20)) = Z_to_bv 64 (VC 120%nat)) by (cbn [VC]; symmetry; apply Z_to_bv_bv_unsigned).
      assert (Cg22 : getr R3 (Z_to_bv 5 (Z.of_nat 22)) = Z_to_bv 64 (VC 122%nat)) by (cbn [VC]; symmetry; apply Z_to_bv_bv_unsigned).
      assert (Cg25 : getr R3 (Z_to_bv 5 (Z.of_nat 25)) = Z_to_bv 64 (VC 125%nat)) by (cbn [VC]; symmetry; apply Z_to_bv_bv_unsigned).
      assert (Cg27 : getr R3 (Z_to_bv 5 (Z.of_nat 27)) = Z_to_bv 64 (VC 127%nat)) by (cbn [VC]; symmetry; apply Z_to_bv_bv_unsigned).
      assert (HSC : 0 <= VC 2%nat < 2 ^ 64) by (cbn [VC]; unfold SC; clear - Hsp' HS1 HS2; lia).
      assert (HSCr : 140735332552704 <= VC 2%nat <= 140737488355328) by (cbn [VC]; unfold SC; clear - Hsp' HS1 HS2; lia).
      assert (HSCa : AS0DRVP_dpCd.aligned (VC 2%nat) 16).
      { cbn [VC]. unfold AS0DRVP_dpCd.aligned, SC. clear - HS16. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
      assert (CWR : L5Defs.L5.writable ASEGS MVc (VC 2%nat - 2016) 2160).
      { cbn [VC]. intros d k Hd Hk. apply (WIN3 (SC - 2016) 2160); unfold SC; clear - Hsp' HS1 HS2 Hd Hk; lia. }
      assert (CDF : L5Defs.L5.defined MVc (VC 2%nat - 2016) 2160).
      { cbn [VC]. intros i Hi. apply (store_ok_defined sp0); [unfold SC; clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN3 (SC - 2016) 2160); unfold SC; clear - Hsp' HS1 HS2 Hi; lia. }
      assert (Cv1088 : L5Defs.L5.u64_at ASEGS MVc (VC 2%nat + 1088) (VC 2%nat + 1240)).
      { cbn [VC]. replace (SC + 1240) with (S + 24) by (unfold SC; ring). exact (cellA 1088 128 _ _ Am128 eq_refl). }
      assert (Cv1144 : L5Defs.L5.u64_at ASEGS MVc (VC 2%nat + 1144) (VC 2%nat + 1240)).
      { cbn [VC]. replace (SC + 1240) with (S + 24) by (unfold SC; ring). exact (cellA 1144 72 _ _ Am72 eq_refl). }
      destruct (AS0DRVP_dpCd.dpCd_conc fx2 R3 MVc VC
           HSC (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) Hcan
           (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) Cg2 Cg8 Cg9 Cg18 Cg19 Cg20 Cg21 Cg22 Cg23 Cg24 Cg25 Cg26 Cg27 HSCr HSCa CWR CDF IMG3
           (fun d k Hd Hk => FW3 1293752 4 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 1293784 8 ltac:(lia) ltac:(lia) d k Hd Hk)
           (fun d k Hd Hk => FW3 1293792 8 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 1293808 8 ltac:(lia) ltac:(lia) d k Hd Hk) (cellL _ _ _ F6a eq_refl) (cellL _ _ _ F3a eq_refl)
           (cellL _ _ _ CAN1 eq_refl) (cellB 40 72 _ _ Bm72 eq_refl) (cellB 104 8 _ _ Bm8 eq_refl) (cellB 96 16 _ _ Bm16 eq_refl) (cellB 88 24 _ _ Bm24 eq_refl) (cellB 80 32 _ _ Bm32 eq_refl)
           (cellB 72 40 _ _ Bm40 eq_refl) (cellB 64 48 _ _ Bm48 eq_refl) (cellB 56 56 _ _ Bm56 eq_refl) (cellB 48 64 _ _ Bm64 eq_refl) (cellA 120 1096 _ _ Am1096 eq_refl)
           (cellA 136 1080 _ _ Am1080 eq_refl) (cellA 128 1088 _ _ Am1088 eq_refl) ST910489 ST881824 (cellA 200 1016 _ _ Am1016 eq_refl) (cellA 192 1024 _ _ Am1024 eq_refl)
           (cellA 184 1032 _ _ Am1032 eq_refl) (cellA 176 1040 _ _ Am1040 eq_refl) (cellA 168 1048 _ _ Am1048 eq_refl) (cellA 160 1056 _ _ Am1056 eq_refl) (cellA 152 1064 _ _ Am1064 eq_refl)
           (cellA 304 912 _ _ Am912 eq_refl) (cellA 640 576 _ _ Am576 eq_refl) (cellA 744 472 _ _ Am472 eq_refl) (cellA 736 480 _ _ Am480 eq_refl) (cellA 728 488 _ _ Am488 eq_refl)
           (cellA 720 496 _ _ Am496 eq_refl) (cellA 712 504 _ _ Am504 eq_refl) (cellA 704 512 _ _ Am512 eq_refl) (cellA 696 520 _ _ Am520 eq_refl) (cellA 688 528 _ _ Am528 eq_refl)
           (cellA 680 536 _ _ Am536 eq_refl) (cellA 672 544 _ _ Am544 eq_refl) (cellA 664 552 _ _ Am552 eq_refl) (cellA 656 560 _ _ Am560 eq_refl) (cellA 648 568 _ _ Am568 eq_refl)
           (cellL _ _ _ Aa892192 eq_refl) (cellA 1056 160 _ _ Am160 eq_refl) (cellA 1112 104 _ _ Am104 eq_refl) (cellA 1104 112 _ _ Am112 eq_refl) (cellA 1096 120 _ _ Am120 eq_refl) Cv1088
           (cellA 1080 136 _ _ Am136 eq_refl) (cellA 1072 144 _ _ Am144 eq_refl) (cellA 1064 152 _ _ Am152 eq_refl) (cellA 1160 56 _ _ Am56 eq_refl) (cellA 1152 64 _ _ Am64 eq_refl) Cv1144
           (cellA 1136 80 _ _ Am80 eq_refl) (cellA 1208 8 _ _ Am8 eq_refl) (cellA 1200 16 _ _ Am16 eq_refl) (cellA 1192 24 _ _ Am24 eq_refl)) as
(fx3 & R4 & MV4 & CGR & _ & CFRZ & CMS & CKS & Cr1 & Cr2 & Cr8 & Cr9 & Cr10 & Cr11 & Cr12 & Cr13 & Cr14 & Cr15 & Cr18 & Cr19 & Cr20 & Cr21 & Cr22 & Cr23 & Cr24 & Cr25 & Cr26 & Cr27 & Ca892192 & Ca892232 & Ca892248 & Ca892224).
      unfold VC in CFRZ, CMS; cbn beta iota in CFRZ, CMS. cbn [VC] in *.
      set (WC := fun a : Z => SC - 2016 <= a < SC - 2016 + 2160 \/ 1293752 <= a < 1293756 \/ 1293784 <= a < 1293800 \/ 1293808 <= a < 1293816).
      assert (FRC : forall a, 0 <= a < 2 ^ 64 -> ~ WC a -> MV4 (Z_to_bv 64 a) = MVc (Z_to_bv 64 a)).
      { intros a Ha Hn. apply CFRZ; [exact Ha | | | | |]; intros X; apply Hn; unfold WC; clear - X; lia. }
      apply (drv_piece scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M3 model3 fx2 fx3 R3 (Z_to_bv 64 0x120264) R4 (Z_to_bv 64 0xa7f98) MV4 WC _ D3 CMS CGR FRC).
      { intros a Ha. unfold CWA. destruct Ha as [Ha|Ha]; [right; left; unfold SC in Ha; clear - Hsp' HS1 HS2 Ha; lia|]. right; right.
        exists 0x13bcc8, 0x13bfc0. split; [unfold IMG_W_A; cbn [In]; tauto | clear - Ha; lia]. }
      intros M4 model4 D4 SBM4 VIS4 FRM4.
      assert (cellL4 : forall a (n : nat) bs, rdn ASEGS MVc (Z_to_bv 64 a) n = Some bs ->
                (0 <=? a) && (a + Z.of_nat n <=? 10000000) && ((a + Z.of_nat n <=? 1293752) || (1293816 <=? a) || ((1293756 <=? a) && (a + Z.of_nat n <=? 1293784)) || ((1293800 <=? a) && (a + Z.of_nat n <=? 1293808))) = true ->
                rdn ASEGS MV4 (Z_to_bv 64 a) n = Some bs).
      { intros a n bs Hr Hb. apply andb_prop in Hb as (Hb & Hb3). apply andb_prop in Hb as (Hb1 & Hb2).
        apply Z.leb_le in Hb1, Hb2. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in Hb3.
        apply (rdn_tr MVc MV4 _ _ _ Hr); [exact Hb1 | lia|].
        intros i Hi. apply FRC; [lia|]. unfold WC, SC. clear - Hsp' HS1 HS2 Hb1 Hb2 Hb3 Hi. lia. }
      apply (KONT fx3 R4 M4 model4 D4).
      + exact (same_but_materialized_trans _ _ _ SBM1 (same_but_materialized_trans _ _ _ SBM2 (same_but_materialized_trans _ _ _ SBM3 SBM4))).
      + (* [comment removed for export] *)
        assert (K34 : forall x, (x = 3 \/ x = 4)%nat -> getr R4 (Z_to_bv 5 (Z.of_nat x)) = getr R (Z_to_bv 5 (Z.of_nat x))).
        { intros x [-> | ->].
          all: (eapply eq_trans; [apply CKS; unfold AS0DRVP_dpCd.KS_dpCd; cbn [In]; repeat first [left; reflexivity | right]|]).
          all: (eapply eq_trans; [apply R3k; unfold WV_KEEP; cbn [In]; repeat first [left; apply bv_eq; reflexivity | right]|]).
          all: (eapply eq_trans; [apply R2k; unfold AS0DRVP_dpB_notty.KS_dpB_notty; cbn [In]; repeat first [left; reflexivity | right]|]).
          all: (apply AKS; unfold AS0DRVP_dpA.KS_dpA; cbn [In]; repeat first [left; reflexivity | right]). }
        intros r Hr. unfold c_kept in Hr. cbn [In] in Hr.
        destruct Hr as [<-|Hr]; [eapply eq_trans; [exact Cr2|]; rewrite R2; f_equal; unfold SC; ring|].
        destruct Hr as [<-|Hr]; [exact (K34 3%nat ltac:(left; reflexivity))|].
        destruct Hr as [<-|Hr]; [exact (K34 4%nat ltac:(right; reflexivity))|].
        destruct Hr as [<-|Hr]; [eapply eq_trans; [exact Cr8|]; apply Z_to_bv_bv_unsigned|].
        destruct Hr as [<-|Hr]; [eapply eq_trans; [exact Cr9|]; apply Z_to_bv_bv_unsigned|].
        destruct Hr as [<-|Hr]; [eapply eq_trans; [exact Cr18|]; apply Z_to_bv_bv_unsigned|].
        destruct Hr as [<-|Hr]; [eapply eq_trans; [exact Cr19|]; apply Z_to_bv_bv_unsigned|].
        destruct Hr as [<-|Hr]; [eapply eq_trans; [exact Cr20|]; apply Z_to_bv_bv_unsigned|].
        destruct Hr as [<-|Hr]; [eapply eq_trans; [exact Cr21|]; apply Z_to_bv_bv_unsigned|].
        destruct Hr as [<-|Hr]; [eapply eq_trans; [exact Cr22|]; apply Z_to_bv_bv_unsigned|].
        destruct Hr as [<-|Hr]; [eapply eq_trans; [exact Cr23|]; apply Z_to_bv_bv_unsigned|].
        destruct Hr as [<-|Hr]; [eapply eq_trans; [exact Cr24|]; apply Z_to_bv_bv_unsigned|].
        destruct Hr as [<-|Hr]; [eapply eq_trans; [exact Cr25|]; apply Z_to_bv_bv_unsigned|].
        destruct Hr as [<-|Hr]; [eapply eq_trans; [exact Cr26|]; apply Z_to_bv_bv_unsigned|].
        destruct Hr as [<-|Hr]; [eapply eq_trans; [exact Cr27|]; apply Z_to_bv_bv_unsigned|].
        destruct Hr.
      + exact Cr10.
      + (* [comment removed for export] *)
        rewrite VIS4. unfold stdoutA.
        split; [exact Ca892192|].
        split; [exact (cellL4 _ _ _ (cellL _ _ _ F3a eq_refl) eq_refl)|].
        split; [exact Ca892224|].
        split; [exact Ca892232|].
        split; [exact Ca892248|].
        split; [exact (cellL4 _ _ _ (cellL _ _ _ F1a eq_refl) eq_refl)|].
        split.
        { apply (cellL4 1293896 4%nat); [|reflexivity]. rewrite <- le4_m1.
          apply (rdn_tr MVb MVc _ _ _ Ba892336); [lia | cbn; lia|]. intros i Hi. apply FRV3; [cbn in Hi; lia|]. unfold q. cbn in Hi. clear - Hsp' HS1 HS2 Hi. lia. }
        split; [intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MVc MV4 _ CGR); apply (FW3 a n); assumption|].
        split.
        { intros a n H1 H2 d k Hd Hk. apply (store_ok_mono ASEGS k MVc MV4 _ CGR). apply (store_ok_mono ASEGS k MVb MVc _ GRV3).
          apply (store_ok_mono ASEGS k MVa MVb _ BGR). apply (BW1 a n); assumption. }
        intros i Hi. lia.
      + (* [comment removed for export] *)
        rewrite VIS4. unfold stdoutXA.
        split; [exact (cellL4 _ _ _ (cellL _ _ _ Aa892264 eq_refl) eq_refl)|].
        split; [exact (cellL4 _ _ _ (cellL _ _ _ F9a eq_refl) eq_refl)|].
        split; [exact (cellL4 _ _ _ (cellL _ _ _ F6a eq_refl) eq_refl)|].
        split; [exact (cellL4 _ _ _ (cellL _ _ _ Aa892200 eq_refl) eq_refl) | exact (cellL4 _ _ _ (cellL _ _ _ Aa892208 eq_refl) eq_refl)].
      + (* [comment removed for export] *)
        intros a Ha Hn.
        rewrite FRM4 by (exact Ha || (intros X; apply Hn; unfold Wpf1, WC, SC, SOBUF in *; clear - Hsp' HS1 HS2 X; lia)).
        rewrite FRM3 by (exact Ha || (intros X; apply Hn; unfold Wpf1, q, SOBUF in *; clear - Hsp' HS1 HS2 X; lia)).
        rewrite FRM2 by (exact Ha || (intros X; apply Hn; unfold Wpf1, WB, SOBUF in *; clear - Hsp' HS1 HS2 X; lia)).
        apply FRM1; [exact Ha|]. intros X; apply Hn; unfold Wpf1, WA, SOBUF in *; clear - Hsp' HS1 HS2 X; lia.
      + (* [comment removed for export] *)
        intros a Ha Hn. rewrite VIS4.
        rewrite FRC by (exact Ha || (intros X; apply Hn; unfold Wpf1, WC, SC, SOBUF in *; clear - Hsp' HS1 HS2 X; lia)).
        rewrite FRV3 by (exact Ha || (intros X; apply Hn; unfold Wpf1, q, SOBUF in *; clear - Hsp' HS1 HS2 X; lia)).
        rewrite FRB by (exact Ha || (intros X; apply Hn; unfold Wpf1, WB, SOBUF in *; clear - Hsp' HS1 HS2 X; lia)).
        apply FRA; [exact Ha|]. intros X; apply Hn; unfold Wpf1, WA, SOBUF in *; clear - Hsp' HS1 HS2 X; lia.
      + intros a Ha. rewrite VIS4. apply CGR. apply GRV3. apply BGR. apply AGR. exact Ha.
  Qed.
End Printf1.
End FPX_1.
