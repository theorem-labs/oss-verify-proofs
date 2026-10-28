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
  Ba0DrvA_b Ba0DrvG_defs_b Ba0DrvG_b Ba0DrvE_b Ba0DiagChainK_b Ba0DiagArmRefuse_b Ba0DiagStrK_b Ba0DiagArmOpen_b Ba0DrvH_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require L5Defs L5KnA ArtMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require BatFsInv_b BatWrapMallocX_b Ba0RegionPoisoned_b Ba0AsanMemcpy_b Ba0DiagStrnlen_b Ba0DiagKit_b Ba0DiagGlue_b Ba0DiagReadA_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Import SX2. Import SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Notation rom := (seg_rom ASEGS).

Lemma msg_read_eqA : forall path, Ba0DiagReadA_b.DRA.PRE19 ++ path ++ Ba0DiagReadA_b.DRA.SUF1 = msg_read_error path.
Proof. intros path. unfold msg_read_error. f_equal; try f_equal; try (apply Ba0DiagGlue_b.DG.list_bv_eq; vm_compute; reflexivity). Qed.

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
  #[local] Notation dinvA := (dinv ar HI sp0 M0).
  #[local] Notation usp := (bv_unsigned sp0).
  #[local] Notation ENV0 := (ENVA []).

  (* [comment removed for export] *)
  #[using="L C IL HIok ICok ILY Hsp Hal DL Hex Hdg Hdgs"] Lemma dg_read_site : forall (fxq : PropExec.FPState) vals R M (model : Model) LB LK cr A fs (p1 : word) (path : list byte),
    regs_ok (ENV0 vals) srHE R -> know_ok ASEGS (ENV0 vals) (mrestrict (ahid A model) M) knHE -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = p1 ->
    dinvA LB LK cr A M model -> m_fs model = fs -> fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    str_atA ar sp0 M0 A p1 path -> length path = 1%nat ->
    srealizes ASEGS scfg (mkCfg (@mkst fxq R (Z_to_bv 64 0x633bc) M rom) model) (t_die (msg_read_error path) fs).
  Proof.
    intros fxq vals R M model LB LK cr A fs p1 path HR HK P0 P2 D EFS FD2 [PLO STR NONUL PLEN PDEF SAH] Hn1. pose proof Hsp as Hsp'.
    destruct dot_itinerary_okA as (_ & _ & _ & OKb).
    set (S := usp - 128). set (MV := mrestrict (ahid A model) M) in *. set (can := vals_ev vals 3).
    assert (HS16 : S mod 16 = 0).
    { unfold S. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - Hal. lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    destruct (dg_machine_pre scfg L ar C IL HI HIok sp0 Hsp DL Hdg M0 [] vals knHE LB LK cr A M model can S HK OKb P0 eq_refl D ltac:(unfold S; lia) ltac:(unfold S; lia) HS16)
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
    assert (G11 : getr R 11%bv = Z_to_bv 64 127251) by (regv HR (11%bv : reg); reflexivity).
    assert (G12 : getr R 12%bv = Z_to_bv 64 (bv_unsigned p1)) by (regv HR (12%bv : reg); cbn [edenot ev ENVA]; rewrite P2; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Hp : S <= bv_unsigned p1 /\ bv_unsigned p1 + Z.of_nat (length path) + 1 + 16 <= 2 ^ 47) by (unfold S; lia).
    assert (HSm : 140735332552704 + 5440 <= S <= 140737488355328) by (unfold S; lia).
    apply (die_of_chain scfg L ar C IL HI HIok ICok ILY sp0 Hsp Hal DL Hex M0 [] [Ba0DiagReadA_b.DRA.PRE19 ++ path ++ Ba0DiagReadA_b.DRA.SUF1] _ vals knHE LB LK cr A M model fxq R fs S HK OKb P0 D EFS FD2
             ltac:(unfold S; lia) ltac:(unfold S; lia) HS16).
    - cbn [concat]. rewrite app_nil_r. apply msg_read_eqA.
    - destruct (Ba0DiagReadA_b.DRA.read_run fxq R MV S (bv_unsigned p1) (bv_unsigned can) path t8 G1 G2 G10 G11 G12 HSm HS16 HW HD HIMG Hp ltac:(rewrite Hn1; reflexivity)
                  HSTR HSH HSTK HFMT (u64_range can) HC HSN HMC)
        as (fxE & RE & ME & MS & E17 & E10 & E11 & E12 & E9 & E18 & E19 & E22 & I0 & I1 & I2 & I3 & BUF & FDc & AGE & MGE & POST).
      set (n := Z.of_nat (length path)) in *.
      cbn [dg_chain]. exists fxE, RE, ME, (S - 584), (S - 584), 2, (S - 464), (n + 20), 0, 0, (Ba0DiagReadA_b.DRA.PRE19 ++ path ++ Ba0DiagReadA_b.DRA.SUF1), (@nil byte).
      split; [exact MS|].
      split.
      { constructor.
        - exact (conj E17 (conj E10 (conj E11 (conj E12 (conj E9 (conj E18 (conj (eq_trans E22 (f_equal (Z_to_bv 64) (eq_sym (Z.add_0_r _)))) E19))))))).
        - lia.
        - split; [exact I0|]. replace (S - 584 + 8) with (S - 576) by lia. exact I1.
        - split; [lia|]. split; [lia|]. split; [lia|]. split; [right; right; lia|]. split; [right; right; lia|].
          replace (Z.to_nat (n + 20)) with (19 + (length path + 1))%nat by lia. exact BUF.
        - intros X. discriminate X.
        - intros _. split; [replace (S - 584 + 16) with (S - 568) by lia; exact I2|]. split; [replace (S - 584 + 24) with (S - 560) by lia; exact I3|].
          split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [left; reflexivity|]. split; [left; reflexivity|]. reflexivity.
        - lia.
        - exact FDc. }
      split; [rewrite app_nil_r; reflexivity|]. split; [exact AGE|].
      intros RX MX FRX GRX KX.
      exact (fin_ofA sp0 MV S R fxE RX MX G4 (POST fxE RX MX (fun x Hx => FRX x (fun X => Hx ltac:(lia))) GRX KX)).
  Qed.

  (* [comment removed for export] *)
  #[using="C IL HIok ICok ILY Hsp Hal DL Hex Hdg Hdgs"] Theorem read_armA : forall fs0 p0 p1 can LK0 cr0 A0, str_atA ar sp0 M0 A0 p1 dot_path ->
    read_err_kA scfg L ar HI sp0 fs0 p0 p1 can M0 LK0 cr0 A0 (t_die (msg_read_error dot_path) fs0).
  Proof.
    intros fs0 p0 p1 can LK0 cr0 A0 [PLO STR NONUL PLEN PDEF SAH]. unfold read_err_kA.
    intros vals R M model A A1 HL P0 P1 P2 P3 P48 HR HK DI HINC F1 F2 HBR.
    apply (dg_read_site fx vals R M model [(A1, 65536)] LK0 (adebit L cr0 65536) A fs0 p1 dot_path HR HK P0 P2 DI F2).
    - rewrite F1. vm_compute. reflexivity.
    - constructor; try assumption. intros x Hx. exact (BatWrapMallocX_b.art_page_allowedb_incl A0 A _ HINC (SAH x Hx)).
    - reflexivity.
  Qed.
End Arm.
End FPX_1.
