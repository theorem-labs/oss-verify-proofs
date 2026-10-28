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
  HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import DrvKitA DrvNodesLazyK As0DrvKitA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0DrvEntry_b Ba0Drv_defs_b Ba0DrvLib_b Ba0DrvRead_b Ba0DrvPiece_b Ba0DiagLoopK_b Ba0DrvStdio_b Ba0DrvPrintfK_b Ba0DrvPrintf1_b Ba0DrvExit_b
  Ba0DrvA_b Ba0DrvG_defs_b Ba0DrvG_b Ba0DrvE_b Ba0DiagChainK_b Ba0DiagArmRefuse_b Ba0DiagStrK_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require L5Defs L5KnA ArtMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require BatFsInv_b Ba0RegionPoisoned_b Ba0AsanMemcpy_b Ba0DiagStrnlen_b Ba0DiagKit_b Ba0DiagGlue_b Ba0DiagOpenA_b Ba0DiagOpenB_b Ba0DiagOpenC_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Import SX2. Import SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Notation u64A := (L5Defs.L5.u64_at ASEGS).
#[local] Notation agree0 := Ba0DiagGlue_b.DG.agree0.
#[local] Notation rom := (seg_rom ASEGS).

(* [comment removed for export] *)
Section FPX_0. Context {fx : PropExec.FPState}.
Definition srOE0 : list expr := sr_upd srA (ridx 10) (EVar 38).
Definition rOEA := Eval vm_compute in runA (SCR [false] [] []) (SS 0x12a8dc srOE0 [] knA 39).
Definition srOEA : list expr := Eval vm_compute in s_regs (fst (fst rOEA)).
Definition knOEA : list kentry := Eval vm_compute in kn_after rOEA knA.
End FPX_0.
Lemma open_itinerary_okA :
  (s_pc (fst (fst rOEA)), snd (fst rOEA))
  = (0x633bc, [SCStoreOk (SA (ELit 0) 6765660) 4; SCBr false BC_LTU (EAluw ALU_ADD (EVar 38) (ELit 0)) (ELit 18446744073709547521)])
  /\ (nth 1 srOEA (ELit 0), nth 2 srOEA (ELit 0), nth 4 srOEA (ELit 0), nth 10 srOEA (ELit 0), nth 11 srOEA (ELit 0), nth 12 srOEA (ELit 0))
     = (ELit 687464, EAlu ALU_ADD (EVar 0) (ELit (-128)), ELit 6765824, ELit 1293512, ELit 127230, EVar 2)
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
Lemma wseg_errno : wseg_ok ASEGS (Z_to_bv 64 6765660) 4 = true.  Proof. vm_compute. reflexivity. Qed.

Lemma msg_open_eqA : forall path, Ba0DiagOpenA_b.DOA.PRE17 ++ path ++ Ba0DiagOpenA_b.DOA.SUF1 = msg_cannot_open path.
Proof.
  intros path. unfold msg_cannot_open. f_equal; try f_equal; try (apply Ba0DiagGlue_b.DG.list_bv_eq; vm_compute; reflexivity).
Qed.
Lemma pre17_BA : Ba0DiagOpenB_b.DOB.PRE17 = Ba0DiagOpenA_b.DOA.PRE17.  Proof. reflexivity. Qed.
Lemma suf1_BA : Ba0DiagOpenB_b.DOB.SUF1 = Ba0DiagOpenA_b.DOA.SUF1.  Proof. reflexivity. Qed.
Lemma pre17_CA : Ba0DiagOpenC_b.DOC.PRE17 = Ba0DiagOpenA_b.DOA.PRE17.  Proof. reflexivity. Qed.
Lemma suf1_CA : Ba0DiagOpenC_b.DOC.SUF1 = Ba0DiagOpenA_b.DOA.SUF1.  Proof. reflexivity. Qed.

Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section Arm.
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
  Hypothesis Hex : incl EX_CELLS (asc_cells C).
  Hypothesis Hdg : incl DG_CELLS (asc_cells C).
  Hypothesis Hdgs : incl DGS_CELLS (asc_cells C).
  Variable M0 : word -> option byte.
  Variable fdata : list byte.
  #[local] Notation dinvA := (dinv ar HI sp0 M0).
  #[local] Notation usp := (bv_unsigned sp0).
  #[local] Notation ENVG := (ENVA fdata).

  (* [comment removed for export] *)
  #[using="Type"] Lemma fin_ofA : forall (MV : word -> option byte) (S : Z) (R : bvmap 5 word) (fx' : PropExec.FPState) RX MX,
    getr R 4%bv = Z_to_bv 64 6765824 ->
    (exists fxF RF MF,
        msteps ASEGS (@mkst fx' RX (Z_to_bv 64 0x120264) MX rom) (@mkst fxF RF (Z_to_bv 64 0x118878) MF rom)
        /\ getr RF 10%bv = Z_to_bv 64 2 /\ getr RF 2%bv = Z_to_bv 64 S
        /\ agree0 MV MF S /\ mem_grows MV MF
        /\ L5Defs.L5.u32_at ASEGS MF 1293512 5 /\ u64A MF 1293608 0 /\ u64A MF 1293600 6898968
        /\ u64A MF 1293568 0 /\ u64A MF 1293552 0 /\ u64A MF 1293544 0 /\ u64A MF 1293520 0 /\ u64A MF 1293528 0 /\ getr RF 4%bv = getr R 4%bv) ->
    dg_chain usp MV S S [] fx' RX 0x120264 MX.
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
    #[local] Notation PRE := Ba0DiagOpenA_b.DOA.PRE17.
    #[local] Notation SUF := Ba0DiagOpenA_b.DOA.SUF1.
    Hypothesis G1 : getr R 1%bv = Z_to_bv 64 687464.
    Hypothesis G2 : getr R 2%bv = Z_to_bv 64 S.
    Hypothesis G4 : getr R 4%bv = Z_to_bv 64 6765824.
    Hypothesis G10 : getr R 10%bv = Z_to_bv 64 1293512.
    Hypothesis G11 : getr R 11%bv = Z_to_bv 64 127230.
    Hypothesis G12 : getr R 12%bv = Z_to_bv 64 p.
    Hypothesis HS1 : usp - 4096 <= S.
    Hypothesis HS2 : S + 64 <= usp.
    Hypothesis HS16 : S mod 16 = 0.
    Hypothesis HW : L5Defs.L5.writable ASEGS MV (S - 5440) 5440.
    Hypothesis HD : L5Defs.L5.defined MV (S - 5440) 5440.
    Hypothesis HIMG : L5Defs.L5.img_clear MV 65536 1282048.
    Hypothesis Hp : S <= p /\ p + n + 1 + 16 <= 2 ^ 47.
    Hypothesis HSTR : Ba0DiagStrnlen_b.DSN.cstr MV p bs t8.
    Hypothesis HSH : forall x : word, Ba0RegionPoisoned_b.SB + p / 8 - 7 <= bv_unsigned x < Z.min (Ba0RegionPoisoned_b.SB + (p + n) / 8 + 8) (Ba0RegionPoisoned_b.SB + 2 ^ 44) -> MV x = Some (Z_to_bv 8 0).
    Hypothesis HSTK : L5KnA.L5KA.zeros_at MV (Ba0RegionPoisoned_b.SB + S / 8 - 680) 688.
    Hypothesis HFMT : L5KnA.L5KA.zeros_at MV 2147466776 16.
    Hypothesis Hcan : 0 <= can < 2 ^ 64.
    Hypothesis HC : Ba0DiagGlue_b.DG.diag_cells MV can.
    Hypothesis HSN : Ba0DiagStrnlen_b.DSN.sn_cells MV.
    Hypothesis HMC : Ba0AsanMemcpy_b.mc_icpt_globs MV.

    #[using="sp0 Hsp M0 can p bs HS1 HS2 HS16 Hcan"] Lemma HSm : 140735332552704 + 5440 <= S <= 140737488355328.  Proof. pose proof Hsp. lia. Qed.

    #[using="Hsp M0 can p t8 G1 G2 G4 G10 G11 G12 HS1 HS2 HS16 HW HD HIMG Hp HSTR HSH HSTK HFMT Hcan HC HSN HMC"] Lemma open_chainA : n <= 62 -> dg_chain usp MV S S [PRE ++ bs ++ SUF] fxq R 0x633bc MV.
    Proof.
      intros Hn. pose proof Hsp as Hsp'.
      destruct (Ba0DiagOpenA_b.DOA.open_A fxq R MV S p can bs t8 G1 G2 G10 G11 G12 HSm HS16 HW HD HIMG Hp Hn HSTR HSH HSTK HFMT Hcan HC HSN HMC)
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

    #[using="Hsp M0 can p t8 G1 G2 G4 G10 G11 G12 HS1 HS2 HS16 HW HD HIMG Hp HSTR HSH HSTK HFMT Hcan HC HSN HMC"] Lemma open_chainB : n = 63 -> dg_chain usp MV S S [(PRE ++ bs) ++ SUF; []] fxq R 0x633bc MV.
    Proof.
      intros Hn. pose proof Hsp as Hsp'.
      destruct (Ba0DiagOpenB_b.DOB.open_B fxq R MV S p can bs t8 G1 G2 G10 G11 G12 HSm HS16 HW HD HIMG Hp Hn HSTR HSH HSTK HFMT Hcan HC HSN HMC)
        as (fxE & RE & ME & MS & E17 & E10 & E11 & E12 & E9 & E18 & E19 & E22 & I0 & I1 & I2 & I3 & BUF & BUF2 & FDc & AGE & MGE & POST).
      cbn [dg_chain]. exists fxE, RE, ME, (S - 1128), (S - 1128), 2, (S - 464), (n + 17), 127249, 1, (PRE ++ bs), SUF.
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

    #[using="Hsp M0 can p t8 G1 G2 G4 G10 G11 G12 HS1 HS2 HS16 HW HD HIMG Hp HSTR HSH HSTK HFMT Hcan HC HSN"] Lemma open_chainC : 64 <= n <= 131071 -> dg_chain usp MV S S [PRE ++ bs; SUF] fxq R 0x633bc MV.
    Proof.
      intros Hn. pose proof Hsp as Hsp'.
      destruct (Ba0DiagOpenC_b.DOC.open_C fxq R MV S p can bs t8 G1 G2 G10 G11 G12 HSm HS16 HW HD HIMG Hp Hn HSTR HSH HSTK HFMT Hcan HC HSN)
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
  #[using="L C IL HIok ICok ILY Hsp Hal DL Hex"] Lemma die_of_chain : forall parts msg vals kn LB LK cr A M (model : Model) (fxq : PropExec.FPState) R fs (S : Z),
    know_ok ASEGS (ENVG vals) (mrestrict (ahid A model) M) kn -> dg_kn_ok kn = true -> vals_ev vals 0 = sp0 ->
    dinvA LB LK cr A M model -> m_fs model = fs -> fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    usp - 4096 <= S -> S + 64 <= usp -> S mod 16 = 0 ->
    concat parts = msg ->
    dg_chain usp (mrestrict (ahid A model) M) S S parts fxq R 0x633bc (mrestrict (ahid A model) M) ->
    srealizes ASEGS scfg (mkCfg (@mkst fxq R (Z_to_bv 64 0x633bc) M rom) model) (t_die msg fs).
  Proof.
    intros parts msg vals kn LB LK cr A M model fxq R fs S HK OKb P0 D EFS FD2 HS1 HS2 HS16 Ecat CH.
    destruct (dg_init_of sp0 Hsp M0 fdata vals kn _ HK OKb P0) as (WINi & IMGi & XAi & SOPi).
    unfold t_die. rewrite <- Ecat.
    eapply srz_conseq; [|apply dg_shape_eq].
    exact (dg_chain_run scfg L ar C IL HI HIok ICok ILY sp0 Hsp Hal DL Hex M0 parts LB LK cr A _ S S (bv_unsigned (vals_ev vals 4)) fs fxq R 0x633bc M model D EFS
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
  #[using="L C IL HIok ICok ILY Hsp Hal DL Hex Hdg Hdgs"] Lemma dg_open_site : forall (fxq : PropExec.FPState) vals R M (model : Model) LB LK cr A fs (p1 : word) (path : list byte),
    regs_ok (ENVG vals) srOEA R -> know_ok ASEGS (ENVG vals) (mrestrict (ahid A model) M) knOEA -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = p1 ->
    dinvA LB LK cr A M model -> m_fs model = fs -> fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    str_atA A p1 path ->
    srealizes ASEGS scfg (mkCfg (@mkst fxq R (Z_to_bv 64 0x633bc) M rom) model) (t_die (msg_cannot_open path) fs).
  Proof.
    intros fxq vals R M model LB LK cr A fs p1 path HR HK P0 P2 D EFS FD2 [PLO STR NONUL PLEN PDEF SAH]. pose proof Hsp as Hsp'.
    destruct open_itinerary_okA as (_ & _ & OKb).
    set (S := usp - 128). set (MV := mrestrict (ahid A model) M) in *. set (can := vals_ev vals 3).
    assert (HS16 : S mod 16 = 0).
    { unfold S. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - Hal. lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    destruct (dg_machine_pre scfg L ar C IL HI HIok sp0 Hsp DL Hdg M0 fdata vals knOEA LB LK cr A M model can S HK OKb P0 eq_refl D ltac:(unfold S; lia) ltac:(unfold S; lia) HS16)
      as (HW & HD & HIMG & HSTK & HC).
    assert (HFMT : L5KnA.L5KA.zeros_at MV 2147466776 16).
    { intros i Hi. apply (img_sh0 scfg L ar IL HI ICok sp0 DL M0 _ _ _ _ _ _ 127168 128 _ D); [lia | lia | lia | | lia].
      rewrite (aicl_poison IL ILY). repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
    destruct (str_cstr scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ p1 path D (proj1 PLO) (proj2 PLO) STR NONUL PDEF) as (t8 & HSTR).
    pose proof (str_hull L ar IL HI sp0 Hsp DL M0 _ _ _ _ _ _ (bv_unsigned p1) (Z.of_nat (length path)) D SAH (proj1 PLO) ltac:(lia)) as HSH.
    destruct (str_statics scfg L ar C IL HI HIok sp0 Hsp DL Hdg Hdgs M0 _ _ _ _ _ _ D HIMG) as (HSN & HMC).
    assert (G1 : getr R 1%bv = Z_to_bv 64 687464) by (regv HR (1%bv : reg); reflexivity).
    assert (G2 : getr R 2%bv = Z_to_bv 64 S) by (regv HR (2%bv : reg); cbn [edenot ev ENVA]; rewrite P0; apply alu_add_w_litA).
    assert (G4 : getr R 4%bv = Z_to_bv 64 6765824) by (regv HR (4%bv : reg); reflexivity).
    assert (G10 : getr R 10%bv = Z_to_bv 64 1293512) by (regv HR (10%bv : reg); reflexivity).
    assert (G11 : getr R 11%bv = Z_to_bv 64 127230) by (regv HR (11%bv : reg); reflexivity).
    assert (G12 : getr R 12%bv = Z_to_bv 64 (bv_unsigned p1)) by (regv HR (12%bv : reg); cbn [edenot ev ENVA]; rewrite P2; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Hp : S <= bv_unsigned p1 /\ bv_unsigned p1 + Z.of_nat (length path) + 1 + 16 <= 2 ^ 47) by (unfold S; lia).
    destruct (Z_le_gt_dec (Z.of_nat (length path)) 62) as [HnA|HnA'].
    - apply (die_of_chain [Ba0DiagOpenA_b.DOA.PRE17 ++ path ++ Ba0DiagOpenA_b.DOA.SUF1] _ vals knOEA LB LK cr A M model fxq R fs S HK OKb P0 D EFS FD2
               ltac:(unfold S; lia) ltac:(unfold S; lia) HS16).
      + cbn [concat]. rewrite app_nil_r. apply msg_open_eqA.
      + exact (open_chainA fxq R MV S (bv_unsigned can) (bv_unsigned p1) path t8 G1 G2 G4 G10 G11 G12 ltac:(unfold S; lia) ltac:(unfold S; lia) HS16 HW HD HIMG Hp HSTR HSH HSTK HFMT
                 (u64_range can) HC HSN HMC HnA).
    - destruct (Z.eq_dec (Z.of_nat (length path)) 63) as [HnB|HnB'].
      + apply (die_of_chain [(Ba0DiagOpenA_b.DOA.PRE17 ++ path) ++ Ba0DiagOpenA_b.DOA.SUF1; []] _ vals knOEA LB LK cr A M model fxq R fs S HK OKb P0 D EFS FD2
                 ltac:(unfold S; lia) ltac:(unfold S; lia) HS16).
        * cbn [concat]. rewrite !app_nil_r, <- app_assoc. apply msg_open_eqA.
        * exact (open_chainB fxq R MV S (bv_unsigned can) (bv_unsigned p1) path t8 G1 G2 G4 G10 G11 G12 ltac:(unfold S; lia) ltac:(unfold S; lia) HS16 HW HD HIMG Hp HSTR HSH HSTK HFMT
                   (u64_range can) HC HSN HMC HnB).
      + apply (die_of_chain [Ba0DiagOpenA_b.DOA.PRE17 ++ path; Ba0DiagOpenA_b.DOA.SUF1] _ vals knOEA LB LK cr A M model fxq R fs S HK OKb P0 D EFS FD2
                 ltac:(unfold S; lia) ltac:(unfold S; lia) HS16).
        * cbn [concat]. rewrite !app_nil_r, <- app_assoc. apply msg_open_eqA.
        * exact (open_chainC fxq R MV S (bv_unsigned can) (bv_unsigned p1) path t8 G1 G2 G4 G10 G11 G12 ltac:(unfold S; lia) ltac:(unfold S; lia) HS16 HW HD HIMG Hp HSTR HSH HSTK HFMT
                   (u64_range can) HC HSN ltac:(lia)).
  Qed.

  (* [comment removed for export] *)
  #[using="L C IL HIok ICok ILY Hsp Hal DL Hex Hdg Hdgs"] Theorem open_armA : forall path fs0 p1 LK0 cr0 A0, str_atA A0 p1 path ->
    open_err_kA scfg ar HI sp0 fs0 fdata p1 M0 LK0 cr0 A0 (t_die (msg_cannot_open path) fs0).
  Proof.
    intros path fs0 p1 LK0 cr0 A0 SA. unfold open_err_kA.
    intros e vals R M model He HL P0 P2 P38 HR HK DI F1 F2. pose proof Hsp as Hsp'.
    drv_block0 HIok Hsp DL HR HK DI P0 (SCR [false] [] []) 39%nat.
    { cbn [sc_denot]. unfold adenot, v_addi. cbn [a_base a_off edenot].
      apply (store_ok_window ASEGS _ (Z_to_bv 64 6765660) _ 4%nat 4%nat 6765660 6765664); first [exact wseg_errno | reflexivity | lia | (vm_compute; intuition discriminate)]. }
    { cbn [sc_denot edenot ev ENVA]. rewrite P38. exact (errno_ltuA e He). }
    destruct (sbm_fds _ _ SBM) as (G1 & G2). rewrite F1 in G1. rewrite F2 in G2.
    apply (dg_open_site fx vals R0 M1 model0 [] LK0 cr0 A0 fs0 p1 path HR0 HK0 P0 P2 DI0 G2); [|exact SA].
    rewrite G1. vm_compute. reflexivity.
  Qed.
End Arm.
End FPX_1.
