(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk StreamSim ShapeAlg ShapeLaws SpinAlg Hoare AgentLib Spec AsanAcctShape SymExec2 SymExec2Sound SymRun SymDrive SymDriveX
  HeapIface HeapIfaceA PmHeapIfaceA IcptIfaceA PmIcptIfaceA Pm8IcptLayout PmIcptDrvA DrvKitA DrvNodesLazyK As0DrvKitA Pm8DrvEntry Pm8Drv_defs Pm8DrvLib Pm8DrvRead Pm8DrvPiece Pm8DiagLoopK Pm8DrvStdio Pm8DrvPrintfK Pm8DrvPrintf1 Pm8DrvExit
  Pm8DrvA Pm8DrvG_defs Pm8DrvG Pm8DrvE Pm8DiagChainK.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require L5Defs L5KnA ArtMem Pm8ArtFsInv Pm8DiagKit Pm8DiagGlue Pm8DiagRefuse.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.
Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FPX_0. Context {fx : PropExec.FPState}.
Definition rRFA := Eval vm_compute in runA (SCR [true; true] [] []) (SS 0xaed6c srLPA [] knLPA 71).
Definition srRFA : list expr := Eval vm_compute in s_regs (fst (fst rRFA)).
Definition knRFA : list kentry := Eval vm_compute in kn_after rRFA knLPA.
End FPX_0.

Definition DG_KN : list kentry := [KImg 65536 1392640; KImg 1407328 1407568; KImg 1407568 1407800; KWord (SA (ELit 0) 7015056) 8 (EVar 3)].
Definition dg_kn_ok (kn : list kentry) : bool := forallb (fun K => existsb (kentry_eqb K) kn) (DG_KN ++ XKN) && has_window kn.
Lemma refuse_itinerary_okA :
  (s_pc (fst (fst rRFA)), snd (fst rRFA), s_log (fst (fst rRFA)))
  = (0x6a59c, [SCBr true BC_NE (EAlu ALU_SRL (EVar 70) (ELit 26)) (ELit 0); SCBr true BC_EQ (EVar 70) (EVar 38)], [])
  /\ (nth 1 srRFA (ELit 0), nth 2 srRFA (ELit 0), nth 4 srRFA (ELit 0), nth 10 srRFA (ELit 0), nth 11 srRFA (ELit 0), nth 12 srRFA (ELit 0))
     = (ELit 716616, EAlu ALU_ADD (EVar 0) (ELit (-128)), ELit 6883920, ELit 1407328, ELit 110226, ELit 67108864)
  /\ dg_kn_ok knRFA = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section Arm.
  Variable L : asan_layout.
  Variable ar : asan_run.
  Variable C : asan_statics_cells.
  Variable IL : icpt_layout.
  Variable HI : asan_iface.
  Hypothesis HIok : asan_iface_ok L ar C scfg HI.
  Hypothesis ICok : aicpt_ok L ar IL scfg HI.
  Hypothesis ILY : as0_icpt_layout IL.
  Variable sp0 : word.
  Hypothesis Hsp : 0x7fff80000000 <= bv_unsigned sp0 <= 2 ^ 47.
  Hypothesis Hal : bv_unsigned sp0 mod 16 = 0.
  Hypothesis DL : drv_layoutA L ar IL sp0.
  Hypothesis Hex : incl EX_CELLS (asc_cells C).
  Hypothesis Hdg : incl DG_CELLS (asc_cells C).
  Variable M0 : word -> option byte.
  Variable fdata : list byte.
  #[local] Notation dinvA := (dinv ar HI sp0 M0).
  #[local] Notation usp := (bv_unsigned sp0).
  #[local] Notation ENVG := (ENVA fdata).
  #[local] Notation rom := (seg_rom ASEGS).

  Lemma dg_cell_vis : forall LB LK cr A M (model : Model) a n v, dinvA LB LK cr A M model -> In (a, n, v) DG_CELLS ->
    rdn ASEGS (mrestrict (ahid A model) M) (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)).
  Proof.
    intros LB LK cr A M model a n v D Hin. pose proof (di_inv _ _ _ _ _ _ _ _ _ _ D) as HH.
    destruct (aio_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & CS). rewrite (dla_segs _ _ _ _ DL) in CS.
    pose proof (proj1 (Forall_forall _ _) CS (a, n, v) (Hdg _ Hin)) as X. unfold cell_is in X. cbn [fst snd] in X.
    rewrite rdn_mrestrict_eq; [exact X|].
    intros k Hk. unfold woff.
    assert (B : 0 <= a /\ a + Z.of_nat (Z.to_nat n) <= 0x6b3000).
    { unfold DG_CELLS in Hin. cbn [In] in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <- <-; cbn; lia|]). destruct Hin. }
    rewrite (u_small a) by lia. apply (vis_low scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ _ D). lia.
  Qed.

  Lemma wseg_stderr : wseg_ok ASEGS (Z_to_bv 64 1407328) 152 = true.  Proof. vmc_refl. Qed.

  Lemma dg_machine_pre : forall vals kn LB LK cr A M (model : Model) (can : word) S,
    know_ok ASEGS (ENVG vals) (mrestrict (ahid A model) M) kn -> dg_kn_ok kn = true -> vals_ev vals 0 = sp0 -> vals_ev vals 3 = can ->
    dinvA LB LK cr A M model -> usp - 4096 <= S -> S + 64 <= usp -> S mod 16 = 0 ->
    let MV := mrestrict (ahid A model) M in
    L5Defs.L5.writable ASEGS MV (S - 5440) 5440 /\ L5Defs.L5.defined MV (S - 5440) 5440 /\ L5Defs.L5.img_clear MV 65536 1392640
    /\ L5KnA.L5KA.zeros_at MV (SB + S / 8 - 680) 688 /\ Pm8DiagGlue.DG.diag_cells MV (bv_unsigned can).
  Proof.
    intros vals kn LB LK cr A M model can S HK OKb P0 P3 D HS1 HS2 HS16 MV. pose proof Hsp as Hsp'.
    unfold dg_kn_ok in OKb. apply andb_prop in OKb as (OKb & HW). rewrite forallb_forall in OKb.
    assert (KB : forall K, In K (DG_KN ++ XKN) -> existsb (kentry_eqb K) kn = true) by (intros K HKin; exact (OKb K HKin)).
    assert (WIN : forall a n, usp - 8388608 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV (Z_to_bv 64 (a + d)) k = true)
      by (intros a n Ha Hn d k Hd Hk; exact (stk_wr sp0 Hsp vals _ MV kn a n HK HW P0 Ha Hn d k Hd Hk)).
    pose proof (kimg_clear (ENVG vals) MV kn 1407328 1407568 HK (KB (KImg 1407328 1407568) ltac:(unfold DG_KN; cbn [In app]; tauto))) as CLe.
    assert (ICe : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (1407328 <=? a) && (a + Z.of_nat n <=? 1407568) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hc. apply andb_prop in Hc as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply CLe. lia. }
    assert (STC : forall a n v, In (a, n, v) DG_CELLS -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros a n v Hin; exact (dg_cell_vis _ _ _ _ _ _ a n v D Hin)).
    assert (STC1 : forall a v, In (a, 1, v) DG_CELLS -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros a v Hin Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (STC a 1 v Hin). }
    split. { intros d k Hd Hk. apply (WIN (S - 5440) 5440); lia. }
    split. { intros i Hi. apply (store_ok_defined sp0); [lia|]. replace (S - 5440 + i) with (S - 5440 + i + 0) by lia. apply (WIN (S - 5440 + i) 1); lia. }
    split. { exact (kimg_clear (ENVG vals) MV kn 65536 1392640 HK (KB (KImg 65536 1392640) ltac:(unfold DG_KN; cbn [In app]; tauto))). }
    split. { intros i Hi. apply (stk_sh0 scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ _ D). unfold SB.
             Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
             clear - Hsp' Hal HS1 HS2 HS16 Hi. lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    unfold Pm8DiagGlue.DG.diag_cells, L5Defs.L5.u8_at, L5Defs.L5.u64_at, L5Defs.L5.u32_at.
    split; [exact (STC1 1431192 1 ltac:(unfold DG_CELLS; cbn [In]; tauto) eq_refl)|]. split; [exact (STC1 1431193 1 ltac:(unfold DG_CELLS; cbn [In]; tauto) eq_refl)|].
    split; [exact (STC1 2024764 1 ltac:(unfold DG_CELLS; cbn [In]; tauto) eq_refl)|]. split; [exact (STC 1427896 8 2147450880 ltac:(unfold DG_CELLS; cbn [In]; tauto))|].
    split; [exact (STC 1396704 8 1296156 ltac:(unfold DG_CELLS; cbn [In]; tauto))|]. split; [exact (STC 1397080 8 1330948 ltac:(unfold DG_CELLS; cbn [In]; tauto))|].
    split. { rewrite Z_to_bv_bv_unsigned, <- P3.
             exact (kword_lit sp0 _ MV kn 7015056 8%nat (EVar 3) HK (KB (KWord (SA (ELit 0) 7015056) 8 (EVar 3)) ltac:(unfold DG_KN; cbn [In app]; tauto)) ltac:(lia) ltac:(cbn; lia)). }
    split; [exact (ICe 1407328 4%nat (word_to_le_bytes 4 (Z_to_bv 64 5)) ltac:(img_rd) eq_refl)|]. split; [exact (ICe 1407424 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
    split; [exact (ICe 1407416 8%nat (word_to_le_bytes 8 (Z_to_bv 64 7017064)) ltac:(img_rd) eq_refl)|]. split; [exact (ICe 1407464 4%nat (word_to_le_bytes 4 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
    split; [exact (ICe 1407468 4%nat (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) ltac:(img_rd) eq_refl)|]. split; [exact (ICe 1407472 4%nat (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) ltac:(img_rd) eq_refl)|].
    split; [exact (ICe 1407400 8%nat (word_to_le_bytes 8 (Z_to_bv 64 1292244)) ltac:(img_rd) eq_refl)|]. split; [exact (ICe 1407448 4%nat (word_to_le_bytes 4 (Z_to_bv 64 2)) ltac:(img_rd) eq_refl)|].
    exact (wsg_writable sp0 Hsp M0 MV 1407328 152%nat wseg_stderr ltac:(lia) ltac:(cbn; lia)).
  Qed.

  Lemma dg_init_of : forall vals kn (MV : word -> option byte),
    know_ok ASEGS (ENVG vals) MV kn -> dg_kn_ok kn = true -> vals_ev vals 0 = sp0 ->
    (forall a n, usp - 8388608 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV (Z_to_bv 64 (a + d)) k = true)
    /\ (forall i, 65536 <= i < 1392640 -> MV (Z_to_bv 64 i) = None)
    /\ exitA (bv_unsigned (vals_ev vals 4)) MV /\ stdoutPA MV.
  Proof.
    intros vals kn MV HK OKb P0. unfold dg_kn_ok in OKb. apply andb_prop in OKb as (OKb & HW). rewrite forallb_forall in OKb.
    assert (KB : forall K, In K (DG_KN ++ XKN) -> existsb (kentry_eqb K) kn = true) by (intros K HKin; exact (OKb K HKin)).
    split; [intros a n Ha Hn d k Hd Hk; exact (stk_wr sp0 Hsp vals _ MV kn a n HK HW P0 Ha Hn d k Hd Hk)|].
    split; [exact (kimg_clear (ENVG vals) MV kn 65536 1392640 HK (KB (KImg 65536 1392640) ltac:(unfold DG_KN; cbn [In app]; tauto)))|].
    split. { apply (exitf_of_kn sp0 Hsp fdata 65536 ltac:(lia) vals MV kn HK). apply forallb_forall. intros K HKin. apply KB. apply in_or_app. right. exact HKin. }
    pose proof (kimg_clear (ENVG vals) MV kn 1407568 1407800 HK (KB (KImg 1407568 1407800) ltac:(unfold DG_KN; cbn [In app]; tauto))) as CLo.
    assert (ICo : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (1407568 <=? a) && (a + Z.of_nat n <=? 1407800) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hc. apply andb_prop in Hc as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply CLo. lia. }
    unfold stdoutPA.
    split; [exact (ICo 1407708 4%nat (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) ltac:(img_rd) eq_refl)|]. split; [exact (ICo 1407608 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
    split; [exact (ICo 1407624 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|]. split; [exact (ICo 1407576 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)|].
    exact (ICo 1407584 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl).
  Qed.

  Lemma refuse_chain : forall (fxq : PropExec.FPState) R (MV : word -> option byte) (S can : Z),
    getr R 1%bv = Z_to_bv 64 716616 -> getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6883920 ->
    getr R 10%bv = Z_to_bv 64 1407328 -> getr R 11%bv = Z_to_bv 64 110226 -> getr R 12%bv = Z_to_bv 64 67108864 ->
    usp - 4096 <= S -> S + 64 <= usp -> S mod 16 = 0 ->
    L5Defs.L5.writable ASEGS MV (S - 5440) 5440 -> L5Defs.L5.defined MV (S - 5440) 5440 -> L5Defs.L5.img_clear MV 65536 1392640 ->
    L5KnA.L5KA.zeros_at MV (SB + S / 8 - 680) 688 -> L5KnA.L5KA.zeros_at MV 2147464656 8 -> 0 <= can < 2 ^ 64 -> Pm8DiagGlue.DG.diag_cells MV can ->
    dg_chain usp MV S S [Pm8DiagRefuse.DRF.MSGR] fxq R 0x6a59c MV.
  Proof.
    intros fxq R MV S can G1 G2 G4 G10 G11 G12 HS1 HS2 HS16 HW HD HIMG HSTK HFMT Hcan HC. pose proof Hsp as Hsp'.
    destruct (Pm8DiagRefuse.DRF.refuse_run fxq R MV S can G1 G2 G10 G11 G12 ltac:(lia) HS16 HW HD HIMG HSTK HFMT Hcan HC)
      as (fxE & RE & ME & MS & E17 & E10 & E11 & E12 & E9 & E18 & E19 & E22 & I0 & I1 & I2 & I3 & BUF & FDc & AGE & MGE & POST).
    cbn [dg_chain]. exists fxE, RE, ME, (S - 584), (S - 584), 2, (S - 464), 38, 0, 0, Pm8DiagRefuse.DRF.MSGR, (@nil byte).
    split; [exact MS|].
    split.
    { constructor.
      - exact (conj E17 (conj E10 (conj E11 (conj E12 (conj E9 (conj E18 (conj E22 E19))))))).
      - lia.
      - split; [exact I0|]. replace (S - 584 + 8) with (S - 576) by lia. exact I1.
      - split; [lia|]. split; [lia|]. split; [lia|]. split; [right; right; lia|]. split; [right; right; lia|]. exact BUF.
      - intros X. discriminate X.
      - intros _. split; [replace (S - 584 + 16) with (S - 568) by lia; exact I2|]. split; [replace (S - 584 + 24) with (S - 560) by lia; exact I3|].
        split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [left; reflexivity|]. split; [left; reflexivity|]. reflexivity.
      - lia.
      - exact FDc. }
    split; [rewrite app_nil_r; reflexivity|]. split; [exact AGE|].
    intros RX MX FRX GRX KX.
    destruct (POST fxE RX MX (fun x Hx => FRX x (fun X => Hx ltac:(lia))) GRX KX) as (fxF & RF & MF & MSF & F10 & F2 & AGF & MGF & _ & _ & _ & C2 & C1 & _ & C3 & C4 & F4).
    exists fxF, RF, MF. split; [exact MSF|]. unfold dg_finA.
    split; [exact F10|]. split; [exact F2|]. split; [eapply eq_trans; [exact F4 | exact G4]|]. split; [exact AGF|].
    split; [exact C1|]. split; [exact C2|]. split; [exact C3 | exact C4].
  Qed.

  Lemma MSGR_eq : Pm8DiagRefuse.DRF.MSGR = msg_refused.
  Proof. apply Pm8DiagGlue.DG.list_bv_eq. vm_compute. reflexivity. Qed.

  Lemma dg_refuse_site : forall (fxq : PropExec.FPState) vals R M (model : Model) LB LK cr A fs (can : word),
    regs_ok (ENVG vals) srRFA R -> know_ok ASEGS (ENVG vals) (mrestrict (ahid A model) M) knRFA -> vals_ev vals 0 = sp0 -> vals_ev vals 3 = can ->
    dinvA LB LK cr A M model -> m_fs model = fs -> fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    srealizes ASEGS scfg (mkCfg (@mkst fxq R (Z_to_bv 64 0x6a59c) M rom) model) (t_die msg_refused fs).
  Proof.
    intros fxq vals R M model LB LK cr A fs can HR HK P0 P3 D EFS FD2. pose proof Hsp as Hsp'.
    destruct refuse_itinerary_okA as (_ & _ & OKb).
    set (S := usp - 128). set (MV := mrestrict (ahid A model) M) in *.
    assert (HS16 : S mod 16 = 0).
    { unfold S. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - Hal. lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    destruct (dg_machine_pre vals knRFA LB LK cr A M model can S HK OKb P0 P3 D ltac:(unfold S; lia) ltac:(unfold S; lia) HS16) as (HW & HD & HIMG & HSTK & HC).
    destruct (dg_init_of vals knRFA MV HK OKb P0) as (WINi & IMGi & XAi & SOPi).
    assert (HFMT : L5KnA.L5KA.zeros_at MV 2147464656 8).
    { intros i Hi. apply (img_sh0 scfg L ar IL HI ICok sp0 DL M0 _ _ _ _ _ _ 110208 64 _ D); [lia | lia | lia | | lia].
      rewrite (aicl_poison IL ILY). repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
    assert (G1 : getr R 1%bv = Z_to_bv 64 716616) by (regv HR (1%bv : reg); reflexivity).
    assert (G2 : getr R 2%bv = Z_to_bv 64 S) by (regv HR (2%bv : reg); cbn [edenot ev ENVA]; rewrite P0; apply alu_add_w_litA).
    assert (G4 : getr R 4%bv = Z_to_bv 64 6883920) by (regv HR (4%bv : reg); reflexivity).
    assert (G10 : getr R 10%bv = Z_to_bv 64 1407328) by (regv HR (10%bv : reg); reflexivity).
    assert (G11 : getr R 11%bv = Z_to_bv 64 110226) by (regv HR (11%bv : reg); reflexivity).
    assert (G12 : getr R 12%bv = Z_to_bv 64 67108864) by (regv HR (12%bv : reg); reflexivity).
    pose proof (refuse_chain fxq R MV S (bv_unsigned can) G1 G2 G4 G10 G11 G12 ltac:(unfold S; lia) ltac:(unfold S; lia) HS16 HW HD HIMG HSTK HFMT (u64_range can) HC) as CH.
    unfold t_die. rewrite <- MSGR_eq.
    exact (dg_chain_run scfg L ar C IL HI HIok ICok ILY sp0 Hsp Hal DL Hex M0 [Pm8DiagRefuse.DRF.MSGR] LB LK cr A MV S S (bv_unsigned (vals_ev vals 4)) fs fxq R 0x6a59c M model D EFS
             (fun x _ _ => eq_refl) (mem_grows_refl _) ltac:(unfold S; lia) ltac:(unfold S; lia) HS16 WINi IMGi XAi SOPi FD2 CH).
  Qed.

  Theorem refuse_armA : forall path fs0 p0 p1 can LK0 A0,
    refuse_kA scfg ar HI sp0 path fs0 fdata p0 p1 can M0 LK0 A0 (t_die msg_refused fs0).
  Proof.
    intros path fs0 p0 p1 can LK0 A0. unfold refuse_kA.
    intros A1 vals R M model A cr HL HV P38 P48 P70 HR HK DI HINC (MF & MS).
    pose proof HV as (P0 & _ & _ & P3). pose proof Hsp as Hsp'.
    drv_block0 HIok Hsp DL HR HK DI P0 (SCR [true; true] [] []) 71%nat.
    { cbn [sc_denot branch_taken edenot ev ENVA]. rewrite P70. vm_compute. reflexivity. }
    { cbn [sc_denot branch_taken edenot ev ENVA]. rewrite P70, P38. vm_compute. reflexivity. }
    pose proof (block_nolog _ _ _ _ _ EQM EQH) as EQA.
    assert (EM : M1 = M) by (apply FunctionalExtensionality.functional_extensionality; exact EQA). subst M1.
    destruct (sbm_fds _ _ SBM) as (G1 & G2). rewrite MF in G1. rewrite MS in G2.
    apply (dg_refuse_site fx vals R0 M model0 [(A1, 67108864)] LK0 cr A fs0 can HR0 HK0 P0 P3 DI0 G2).
    rewrite G1. reflexivity.
  Qed.
End Arm.
End FPX_1.
