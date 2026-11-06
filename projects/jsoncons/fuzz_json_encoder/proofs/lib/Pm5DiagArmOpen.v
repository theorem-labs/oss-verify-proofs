(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk StreamSim ShapeAlg ShapeLaws SpinAlg Hoare AgentLib Spec AsanAcctShape SymExec2 SymExec2Sound SymRun SymDrive SymDriveX
  HeapIface HeapIfaceA PmHeapIfaceA IcptIfaceA PmIcptIfaceA Pm5IcptLayout PmIcptDrvA DrvKitA DrvNodesLazyK As0DrvKitA Pm5DrvEntry Pm5Drv_defs Pm5DrvLib Pm5DrvRead Pm5DrvPiece Pm5DiagLoopK Pm5DrvStdio Pm5DrvPrintfK Pm5DrvPrintf1 Pm5DrvExit
  Pm5DrvA Pm5DrvG_defs Pm5DrvG Pm5DrvE Pm5DiagChainK Pm5DiagArmRefuse Pm5DiagStrK.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require L5Defs L5KnA ArtMem Pm5ArtFsInv Pm5RegionPoisoned Pm5AsanMemcpy Pm5DiagStrnlen Pm5DiagKit Pm5DiagGlue Pm5DiagOpenA Pm5DiagOpenB Pm5DiagOpenC.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Notation u64A := (L5Defs.L5.u64_at ASEGS).
#[local] Notation agree0 := Pm5DiagGlue.DG.agree0.
#[local] Notation rom := (seg_rom ASEGS).

(* [comment removed for export] *)
Section FPX_0. Context {fx : PropExec.FPState}.
Definition srOE0 : list expr := sr_upd srA (ridx 10) (EVar 38).
Definition rOEA := Eval vm_compute in runA (SCR [false] [] []) (SS 0x157494 srOE0 [] knA 39).
Definition srOEA : list expr := Eval vm_compute in s_regs (fst (fst rOEA)).
Definition knOEA : list kentry := Eval vm_compute in kn_after rOEA knA.
End FPX_0.
Lemma open_itinerary_okA :
  (s_pc (fst (fst rOEA)), snd (fst rOEA))
  = (0x6c238, [SCStoreOk (SA (ELit 0) 6952940) 4; SCBr false BC_LTU (EAluw ALU_ADD (EVar 38) (ELit 0)) (ELit 18446744073709547521)])
  /\ (nth 1 srOEA (ELit 0), nth 2 srOEA (ELit 0), nth 4 srOEA (ELit 0), nth 10 srOEA (ELit 0), nth 11 srOEA (ELit 0), nth 12 srOEA (ELit 0))
     = (ELit 723940, EAlu ALU_ADD (EVar 0) (ELit (-128)), ELit 6953104, ELit 1477960, ELit 131045, EVar 2)
  /\ dg_kn_ok knOEA = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Lemma errno_ltuA : forall e, 1 <= e <= 4095 ->
  branch_taken BC_LTU (sext 64 (alu32 ALU_ADD (low32 (errno_ret e)) (low32 (Z_to_bv 64 0)))) (Z_to_bv 64 18446744073709547521) = false.
Proof.
  intros e He.
  assert (X : forallb (fun k => negb (branch_taken BC_LTU (sext 64 (alu32 ALU_ADD (low32 (errno_ret (Z.of_nat k))) (low32 (Z_to_bv 64 0)))) (Z_to_bv 64 18446744073709547521)))
                      (seq 1 4095) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in X. specialize (X (Z.to_nat e) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in X by lia. apply negb_true_iff in X. exact X.
Qed.
Lemma wseg_errno : wseg_ok ASEGS (Z_to_bv 64 6952940) 4 = true.  Proof. vm_compute. reflexivity. Qed.

Lemma msg_open_eqA : forall path, Pm5DiagOpenA.DOA.PRE17 ++ path ++ Pm5DiagOpenA.DOA.SUF1 = msg_cannot_open path.
Proof.
  intros path. unfold msg_cannot_open. f_equal; try f_equal; try (apply Pm5DiagGlue.DG.list_bv_eq; vm_compute; reflexivity).
Qed.
Lemma pre17_BA : Pm5DiagOpenB.DOB.PRE17 = Pm5DiagOpenA.DOA.PRE17.  Proof. reflexivity. Qed.
Lemma suf1_BA : Pm5DiagOpenB.DOB.SUF1 = Pm5DiagOpenA.DOA.SUF1.  Proof. reflexivity. Qed.
Lemma pre17_CA : Pm5DiagOpenC.DOC.PRE17 = Pm5DiagOpenA.DOA.PRE17.  Proof. reflexivity. Qed.
Lemma suf1_CA : Pm5DiagOpenC.DOC.SUF1 = Pm5DiagOpenA.DOA.SUF1.  Proof. reflexivity. Qed.

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
  Hypothesis Hdgs : incl DGS_CELLS (asc_cells C).
  Variable M0 : word -> option byte.
  Variable fdata : list byte.
  #[local] Notation dinvA := (dinv ar HI sp0 M0).
  #[local] Notation usp := (bv_unsigned sp0).
  #[local] Notation ENVG := (ENVA fdata).

  (* [comment removed for export] *)
  Lemma fin_ofA : forall (MV : word -> option byte) (S : Z) (R : bvmap 5 word) (fx' : PropExec.FPState) RX MX,
    getr R 4%bv = Z_to_bv 64 6953104 ->
    (exists fxF RF MF,
        msteps ASEGS (@mkst fx' RX (Z_to_bv 64 0x14ce1c) MX rom) (@mkst fxF RF (Z_to_bv 64 0x14538c) MF rom)
        /\ getr RF 10%bv = Z_to_bv 64 2 /\ getr RF 2%bv = Z_to_bv 64 S
        /\ agree0 MV MF S /\ mem_grows MV MF
        /\ L5Defs.L5.u32_at ASEGS MF 1477960 5 /\ u64A MF 1478056 0 /\ u64A MF 1478048 7086248
        /\ u64A MF 1478016 0 /\ u64A MF 1478000 0 /\ u64A MF 1477992 0 /\ u64A MF 1477968 0 /\ u64A MF 1477976 0 /\ getr RF 4%bv = getr R 4%bv) ->
    dg_chain usp MV S S [] fx' RX 0x14ce1c MX.
  Proof.
    intros MV S R fx' RX MX G4 (fxF & RF & MF & MSF & F10 & F2 & AGF & MGF & _ & _ & _ & C2 & C1 & _ & C3 & C4 & F4).
    cbn [dg_chain]. exists fxF, RF, MF. split; [exact MSF|]. unfold dg_finA.
    split; [exact F10|]. split; [exact F2|]. split; [eapply eq_trans; [exact F4 | exact G4]|]. split; [exact AGF|].
    split; [exact C1|]. split; [exact C2|]. split; [exact C3 | exact C4].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Chains.
    Variables (fxq : PropExec.FPState) (R : bvmap 5 word) (MV : word -> option byte) (S can p : Z) (bs t8 : list byte).
    #[local] Notation n := (Z.of_nat (length bs)).
    #[local] Notation PRE := Pm5DiagOpenA.DOA.PRE17.
    #[local] Notation SUF := Pm5DiagOpenA.DOA.SUF1.
    Hypothesis G1 : getr R 1%bv = Z_to_bv 64 723940.
    Hypothesis G2 : getr R 2%bv = Z_to_bv 64 S.
    Hypothesis G4 : getr R 4%bv = Z_to_bv 64 6953104.
    Hypothesis G10 : getr R 10%bv = Z_to_bv 64 1477960.
    Hypothesis G11 : getr R 11%bv = Z_to_bv 64 131045.
    Hypothesis G12 : getr R 12%bv = Z_to_bv 64 p.
    Hypothesis HS1 : usp - 4096 <= S.
    Hypothesis HS2 : S + 64 <= usp.
    Hypothesis HS16 : S mod 16 = 0.
    Hypothesis HW : L5Defs.L5.writable ASEGS MV (S - 5440) 5440.
    Hypothesis HD : L5Defs.L5.defined MV (S - 5440) 5440.
    Hypothesis HIMG : L5Defs.L5.img_clear MV 65536 1466368.
    Hypothesis Hp : S <= p /\ p + n + 1 + 16 <= 2 ^ 47.
    Hypothesis HSTR : Pm5DiagStrnlen.DSN.cstr MV p bs t8.
    Hypothesis HSH : forall x : word, Pm5RegionPoisoned.SB + p / 8 - 7 <= bv_unsigned x < Z.min (Pm5RegionPoisoned.SB + (p + n) / 8 + 8) (Pm5RegionPoisoned.SB + 2 ^ 44) -> MV x = Some (Z_to_bv 8 0).
    Hypothesis HSTK : L5KnA.L5KA.zeros_at MV (Pm5RegionPoisoned.SB + S / 8 - 680) 688.
    Hypothesis HFMT : L5KnA.L5KA.zeros_at MV 2147467256 16.
    Hypothesis Hcan : 0 <= can < 2 ^ 64.
    Hypothesis HC : Pm5DiagGlue.DG.diag_cells MV can.
    Hypothesis HSN : Pm5DiagStrnlen.DSN.sn_cells MV.
    Hypothesis HMC : Pm5AsanMemcpy.mc_icpt_globs MV.

    Lemma HSm : 140735332552704 + 5440 <= S <= 140737488355328.  Proof. pose proof Hsp. lia. Qed.

    Lemma open_chainA : n <= 62 -> dg_chain usp MV S S [PRE ++ bs ++ SUF] fxq R 0x6c238 MV.
    Proof.
      intros Hn. pose proof Hsp as Hsp'.
      destruct (Pm5DiagOpenA.DOA.open_A fxq R MV S p can bs t8 G1 G2 G10 G11 G12 HSm HS16 HW HD HIMG Hp Hn HSTR HSH HSTK HFMT Hcan HC HSN HMC)
        as (fxE & RE & ME & MS & E17 & E10 & E11 & E12 & E9 & E18 & E19 & E22 & I0 & I1 & I2 & I3 & BUF & FDc & AGE & MGE & POST).
      cbn [dg_chain]. exists fxE, RE, ME, (S - 584), (S - 584), 2, (S - 464), (n + 18), 0, 0, (PRE ++ bs ++ SUF), (@nil byte).
      split; [exact MS|].
      split.
      { constructor.
        - exact (conj E17 (conj E10 (conj E11 (conj E12 (conj E9 (conj E18 (conj (eq_trans E22 (f_equal (Z_to_bv 64) (eq_sym (Z.add_0_r _)))) E19))))))).
        - lia.
        - split; [exact I0|]. replace (S - 584 + 8) with (S - 576) by lia. exact I1.
        - split; [lia|]. split; [lia|]. split; [lia|]. split; [right; right; lia|]. split; [right; right; lia|].
          replace (Z.to_nat (n + 18)) with (17 + (length bs + 1))%nat by lia. exact BUF.
        - intros X. discriminate X.
        - intros _. split; [replace (S - 584 + 16) with (S - 568) by lia; exact I2|]. split; [replace (S - 584 + 24) with (S - 560) by lia; exact I3|].
          split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [left; reflexivity|]. split; [left; reflexivity|]. reflexivity.
        - lia.
        - exact FDc. }
      split; [rewrite app_nil_r; reflexivity|]. split; [exact AGE|].
      intros RX MX FRX GRX KX.
      exact (fin_ofA MV S R fxE RX MX G4 (POST fxE RX MX (fun x Hx => FRX x (fun X => Hx ltac:(lia))) GRX KX)).
    Qed.

    Lemma open_chainB : n = 63 -> dg_chain usp MV S S [(PRE ++ bs) ++ SUF; []] fxq R 0x6c238 MV.
    Proof.
      intros Hn. pose proof Hsp as Hsp'.
      destruct (Pm5DiagOpenB.DOB.open_B fxq R MV S p can bs t8 G1 G2 G10 G11 G12 HSm HS16 HW HD HIMG Hp Hn HSTR HSH HSTK HFMT Hcan HC HSN HMC)
        as (fxE & RE & ME & MS & E17 & E10 & E11 & E12 & E9 & E18 & E19 & E22 & I0 & I1 & I2 & I3 & BUF & BUF2 & FDc & AGE & MGE & POST).
      cbn [dg_chain]. exists fxE, RE, ME, (S - 1128), (S - 1128), 2, (S - 464), (n + 17), 131064, 1, (PRE ++ bs), SUF.
      split; [exact MS|].
      split.
      { constructor.
        - replace (n + 18) with (n + 17 + 1) in E22 by lia. exact (conj E17 (conj E10 (conj E11 (conj E12 (conj E9 (conj E18 (conj E22 E19))))))).
        - lia.
        - split; [exact I0|]. replace (S - 1128 + 8) with (S - 1120) by lia. exact I1.
        - split; [lia|]. split; [lia|]. split; [lia|]. split; [right; right; lia|]. split; [right; right; lia|].
          replace (Z.to_nat (n + 17)) with (17 + length bs)%nat by lia. exact BUF.
        - intros X. discriminate X.
        - intros _. split; [replace (S - 1128 + 16) with (S - 1112) by lia; exact I2|]. split; [replace (S - 1128 + 24) with (S - 1104) by lia; exact I3|].
          split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [right; left; lia|]. split; [right; left; lia|]. exact BUF2.
        - lia.
        - exact FDc. }
      split; [reflexivity|]. split; [exact AGE|].
      intros RX MX FRX GRX KX.
      destruct (POST fxE RX MX (fun x Hx => FRX x (fun X => Hx ltac:(lia))) GRX KX)
        as (fxE2 & RE2 & ME2 & MS2 & Q17 & Q10 & Q11 & Q12 & Q9 & Q18 & Q19 & Q22 & J0 & J1 & FDc2 & AGE2 & MGE2 & POST2).
      cbn [dg_chain]. exists fxE2, RE2, ME2, (S - 584), (S - 568), 1, 0, 0, 0, 0, (@nil byte), (@nil byte).
      split; [exact MS2|].
      split.
      { constructor.
        - exact (conj Q17 (conj Q10 (conj Q11 (conj Q12 (conj Q9 (conj Q18 (conj Q22 Q19))))))).
        - lia.
        - split; [exact J0|]. replace (S - 568 + 8) with (S - 560) by lia. exact J1.
        - split; [lia|]. split; [lia|]. split; [lia|]. split; [left; reflexivity|]. split; [left; reflexivity|]. reflexivity.
        - intros _. split; reflexivity.
        - intros X. discriminate X.
        - lia.
        - exact FDc2. }
      split; [reflexivity|]. split; [exact AGE2|].
      intros RY MY FRY GRY KY.
      exact (fin_ofA MV S R fxE2 RY MY G4 (POST2 fxE2 RY MY (fun x Hx => FRY x (fun X => Hx ltac:(lia))) GRY KY)).
    Qed.

    Lemma open_chainC : 64 <= n <= 131071 -> dg_chain usp MV S S [PRE ++ bs; SUF] fxq R 0x6c238 MV.
    Proof.
      intros Hn. pose proof Hsp as Hsp'.
      destruct (Pm5DiagOpenC.DOC.open_C fxq R MV S p can bs t8 G1 G2 G10 G11 G12 HSm HS16 HW HD HIMG Hp Hn HSTR HSH HSTK HFMT Hcan HC HSN)
        as (fxE & RE & ME & MS & E17 & E10 & E11 & E12 & E9 & E18 & E19 & E22 & I0 & I1 & I2 & I3 & BUF & BUF2 & FDc & AGE & MGE & POST).
      cbn [dg_chain]. exists fxE, RE, ME, (S - 1128), (S - 1128), 2, (S - 464), 17, p, n, PRE, bs.
      split; [exact MS|].
      split.
      { constructor.
        - replace (n + 17) with (17 + n) in E22 by lia. exact (conj E17 (conj E10 (conj E11 (conj E12 (conj E9 (conj E18 (conj E22 E19))))))).
        - lia.
        - split; [exact I0|]. replace (S - 1128 + 8) with (S - 1120) by lia. exact I1.
        - split; [lia|]. split; [lia|]. split; [lia|]. split; [right; right; lia|]. split; [right; right; lia|]. exact BUF.
        - intros X. discriminate X.
        - intros _. split; [replace (S - 1128 + 16) with (S - 1112) by lia; exact I2|]. split; [replace (S - 1128 + 24) with (S - 1104) by lia; exact I3|].
          split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [right; right; lia|]. split; [right; right; lia|].
          rewrite Nat2Z.id. exact BUF2.
        - lia.
        - exact FDc. }
      split; [reflexivity|]. split; [exact AGE|].
      intros RX MX FRX GRX KX.
      destruct (POST fxE RX MX (fun x Hx => FRX x (fun X => Hx ltac:(lia))) GRX KX)
        as (fxE2 & RE2 & ME2 & MS2 & Q17 & Q10 & Q11 & Q12 & Q9 & Q18 & Q19 & Q22 & J0 & J1 & J2 & J3 & BUF3 & FDc2 & AGE2 & MGE2 & POST2).
      cbn [dg_chain]. exists fxE2, RE2, ME2, (S - 584), (S - 584), 2, (S - 464), 1, 0, 0, SUF, (@nil byte).
      split; [exact MS2|].
      split.
      { constructor.
        - exact (conj Q17 (conj Q10 (conj Q11 (conj Q12 (conj Q9 (conj Q18 (conj Q22 Q19))))))).
        - lia.
        - split; [exact J0|]. replace (S - 584 + 8) with (S - 576) by lia. exact J1.
        - split; [lia|]. split; [lia|]. split; [lia|]. split; [right; right; lia|]. split; [right; right; lia|]. exact BUF3.
        - intros X. discriminate X.
        - intros _. split; [replace (S - 584 + 16) with (S - 568) by lia; exact J2|]. split; [replace (S - 584 + 24) with (S - 560) by lia; exact J3|].
          split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [left; reflexivity|]. split; [left; reflexivity|]. reflexivity.
        - lia.
        - exact FDc2. }
      split; [rewrite app_nil_r; reflexivity|]. split; [exact AGE2|].
      intros RY MY FRY GRY KY.
      exact (fin_ofA MV S R fxE2 RY MY G4 (POST2 fxE2 RY MY (fun x Hx => FRY x (fun X => Hx ltac:(lia))) GRY KY)).
    Qed.
  End Chains.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma die_of_chain : forall parts msg vals kn LB LK cr A M (model : Model) (fxq : PropExec.FPState) R fs (S : Z),
    know_ok ASEGS (ENVG vals) (mrestrict (ahid A model) M) kn -> dg_kn_ok kn = true -> vals_ev vals 0 = sp0 ->
    dinvA LB LK cr A M model -> m_fs model = fs -> fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    usp - 4096 <= S -> S + 64 <= usp -> S mod 16 = 0 ->
    concat parts = msg ->
    dg_chain usp (mrestrict (ahid A model) M) S S parts fxq R 0x6c238 (mrestrict (ahid A model) M) ->
    srealizes ASEGS scfg (mkCfg (@mkst fxq R (Z_to_bv 64 0x6c238) M rom) model) (t_die msg fs).
  Proof.
    intros parts msg vals kn LB LK cr A M model fxq R fs S HK OKb P0 D EFS FD2 HS1 HS2 HS16 Ecat CH.
    destruct (dg_init_of sp0 Hsp M0 fdata vals kn _ HK OKb P0) as (WINi & IMGi & XAi & SOPi).
    unfold t_die. rewrite <- Ecat.
    eapply srz_conseq; [|apply dg_shape_eq].
    exact (dg_chain_run scfg L ar C IL HI HIok ICok ILY sp0 Hsp Hal DL Hex M0 parts LB LK cr A _ S S (bv_unsigned (vals_ev vals 4)) fs fxq R 0x6c238 M model D EFS
             (fun x _ _ => eq_refl) (mem_grows_refl _) ltac:(lia) ltac:(lia) HS16 WINi IMGi XAi SOPi FD2 CH).
  Qed.

  (* [comment removed for export] *)
  Record str_atA (A : list (Z * Z)) (p1 : word) (path : list byte) : Prop := STR_ATA {
    sa_lo : usp <= bv_unsigned p1 /\ bv_unsigned p1 + Z.of_nat (length path) + 1 + 16 <= 2 ^ 47;
    sa_str : rdn ASEGS M0 p1 (length path + 1) = Some (path ++ [Z_to_bv 8 0]);
    sa_nonul : ~ In (Z_to_bv 8 0) path;
    sa_len : Z.of_nat (length path) <= 131071;
    sa_def : defined M0 (bv_unsigned p1) (Z.of_nat (length path) + 1 + 16);
    sa_sah : shadow_allowed A (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar)
  }.

  (* [comment removed for export] *)
  Lemma dg_open_site : forall (fxq : PropExec.FPState) vals R M (model : Model) LB LK cr A fs (p1 : word) (path : list byte),
    regs_ok (ENVG vals) srOEA R -> know_ok ASEGS (ENVG vals) (mrestrict (ahid A model) M) knOEA -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = p1 ->
    dinvA LB LK cr A M model -> m_fs model = fs -> fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    str_atA A p1 path ->
    srealizes ASEGS scfg (mkCfg (@mkst fxq R (Z_to_bv 64 0x6c238) M rom) model) (t_die (msg_cannot_open path) fs).
  Proof.
    intros fxq vals R M model LB LK cr A fs p1 path HR HK P0 P2 D EFS FD2 [PLO STR NONUL PLEN PDEF SAH]. pose proof Hsp as Hsp'.
    destruct open_itinerary_okA as (_ & _ & OKb).
    set (S := usp - 128). set (MV := mrestrict (ahid A model) M) in *. set (can := vals_ev vals 3).
    assert (HS16 : S mod 16 = 0).
    { unfold S. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - Hal. lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    destruct (dg_machine_pre scfg L ar C IL HI HIok sp0 Hsp DL Hdg M0 fdata vals knOEA LB LK cr A M model can S HK OKb P0 eq_refl D ltac:(unfold S; lia) ltac:(unfold S; lia) HS16)
      as (HW & HD & HIMG & HSTK & HC).
    assert (HFMT : L5KnA.L5KA.zeros_at MV 2147467256 16).
    { intros i Hi. apply (img_sh0 scfg L ar IL HI ICok sp0 DL M0 _ _ _ _ _ _ 131008 128 _ D); [lia | lia | lia | | lia].
      rewrite (aicl_poison IL ILY). repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
    destruct (str_cstr scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ p1 path D (proj1 PLO) (proj2 PLO) STR NONUL PDEF) as (t8 & HSTR).
    pose proof (str_hull L ar IL HI sp0 Hsp DL M0 _ _ _ _ _ _ (bv_unsigned p1) (Z.of_nat (length path)) D SAH (proj1 PLO) ltac:(lia)) as HSH.
    destruct (str_statics scfg L ar C IL HI HIok sp0 Hsp DL Hdg Hdgs M0 _ _ _ _ _ _ D HIMG) as (HSN & HMC).
    assert (G1 : getr R 1%bv = Z_to_bv 64 723940) by (regv HR (1%bv : reg); reflexivity).
    assert (G2 : getr R 2%bv = Z_to_bv 64 S) by (regv HR (2%bv : reg); cbn [edenot ev ENVA]; rewrite P0; apply alu_add_w_litA).
    assert (G4 : getr R 4%bv = Z_to_bv 64 6953104) by (regv HR (4%bv : reg); reflexivity).
    assert (G10 : getr R 10%bv = Z_to_bv 64 1477960) by (regv HR (10%bv : reg); reflexivity).
    assert (G11 : getr R 11%bv = Z_to_bv 64 131045) by (regv HR (11%bv : reg); reflexivity).
    assert (G12 : getr R 12%bv = Z_to_bv 64 (bv_unsigned p1)) by (regv HR (12%bv : reg); cbn [edenot ev ENVA]; rewrite P2; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Hp : S <= bv_unsigned p1 /\ bv_unsigned p1 + Z.of_nat (length path) + 1 + 16 <= 2 ^ 47) by (unfold S; lia).
    destruct (Z_le_gt_dec (Z.of_nat (length path)) 62) as [HnA|HnA'].
    - apply (die_of_chain [Pm5DiagOpenA.DOA.PRE17 ++ path ++ Pm5DiagOpenA.DOA.SUF1] _ vals knOEA LB LK cr A M model fxq R fs S HK OKb P0 D EFS FD2
               ltac:(unfold S; lia) ltac:(unfold S; lia) HS16).
      + cbn [concat]. rewrite app_nil_r. apply msg_open_eqA.
      + exact (open_chainA fxq R MV S (bv_unsigned can) (bv_unsigned p1) path t8 G1 G2 G4 G10 G11 G12 ltac:(unfold S; lia) ltac:(unfold S; lia) HS16 HW HD HIMG Hp HSTR HSH HSTK HFMT
                 (u64_range can) HC HSN HMC HnA).
    - destruct (Z.eq_dec (Z.of_nat (length path)) 63) as [HnB|HnB'].
      + apply (die_of_chain [(Pm5DiagOpenA.DOA.PRE17 ++ path) ++ Pm5DiagOpenA.DOA.SUF1; []] _ vals knOEA LB LK cr A M model fxq R fs S HK OKb P0 D EFS FD2
                 ltac:(unfold S; lia) ltac:(unfold S; lia) HS16).
        * cbn [concat]. rewrite !app_nil_r, <- app_assoc. apply msg_open_eqA.
        * exact (open_chainB fxq R MV S (bv_unsigned can) (bv_unsigned p1) path t8 G1 G2 G4 G10 G11 G12 ltac:(unfold S; lia) ltac:(unfold S; lia) HS16 HW HD HIMG Hp HSTR HSH HSTK HFMT
                   (u64_range can) HC HSN HMC HnB).
      + apply (die_of_chain [Pm5DiagOpenA.DOA.PRE17 ++ path; Pm5DiagOpenA.DOA.SUF1] _ vals knOEA LB LK cr A M model fxq R fs S HK OKb P0 D EFS FD2
                 ltac:(unfold S; lia) ltac:(unfold S; lia) HS16).
        * cbn [concat]. rewrite !app_nil_r, <- app_assoc. apply msg_open_eqA.
        * exact (open_chainC fxq R MV S (bv_unsigned can) (bv_unsigned p1) path t8 G1 G2 G4 G10 G11 G12 ltac:(unfold S; lia) ltac:(unfold S; lia) HS16 HW HD HIMG Hp HSTR HSH HSTK HFMT
                   (u64_range can) HC HSN ltac:(lia)).
  Qed.

  (* [comment removed for export] *)
  Theorem open_armA : forall path fs0 p1 LK0 cr0 A0, str_atA A0 p1 path ->
    open_err_kA scfg ar HI sp0 fs0 fdata p1 M0 LK0 cr0 A0 (t_die (msg_cannot_open path) fs0).
  Proof.
    intros path fs0 p1 LK0 cr0 A0 SA. unfold open_err_kA.
    intros e vals R M model He HL P0 P2 P38 HR HK DI F1 F2. pose proof Hsp as Hsp'.
    drv_block0 HIok Hsp DL HR HK DI P0 (SCR [false] [] []) 39%nat.
    { cbn [sc_denot]. unfold adenot, v_addi. cbn [a_base a_off edenot].
      apply (store_ok_window ASEGS _ (Z_to_bv 64 6952940) _ 4%nat 4%nat 6952940 6952944); first [exact wseg_errno | reflexivity | lia | (vm_compute; intuition discriminate)]. }
    { cbn [sc_denot edenot ev ENVA]. rewrite P38. exact (errno_ltuA e He). }
    destruct (sbm_fds _ _ SBM) as (G1 & G2). rewrite F1 in G1. rewrite F2 in G2.
    apply (dg_open_site fx vals R0 M1 model0 [] LK0 cr0 A0 fs0 p1 path HR0 HK0 P0 P2 DI0 G2); [|exact SA].
    rewrite G1. vm_compute. reflexivity.
  Qed.
End Arm.
End FPX_1.
