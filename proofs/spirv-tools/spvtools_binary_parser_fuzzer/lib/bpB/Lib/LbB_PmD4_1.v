(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps SymExec3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require RtB_Td.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_ContStmt LbB_PrsStmt LbB_FKit LbB_Own LbB_PmBase LbB_Call LbB_Bridge.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_DStat LbB_SR LbB_WoGen LbB_WoDefs LbB_WoKit LbB_PiStmt LbB_PiInit.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRepFacts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BllocRep BG_Free6.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_WoBP LbB_PmExit.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_DiagStmt LbB_WoDiagP LbB_WoKit2 LbB_WoDiagF LbB_PmMagW LbB_PmHTK.
Import ListNotations.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_TablStmt LbB_PmCall LbB_Conv LbB_Kit LbB_PmGlue.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_WoDiagC LbB_WoDiagC2 LbB_WoDiagH LbB_WdD4S LbB_PmD4Sh.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require SeqExec.
Open Scope Z_scope.

Ltac lit_acc :=
  lazymatch goal with |- forall _, ACONST _ -> accessible _ ?p ?n =>
    let M' := fresh "M'" in let ACM' := fresh "ACM'" in
    intros M' ACM'; eapply (addressable_accessible M' p);
      [ eapply (ACONST_global_addressable M' p _ _ ACM'); [unfold aglobals; repeat (first [left; reflexivity | right]) | lia]
      | lia | lia | unfold AAPP_HI; lia ]
  end.
Ltac lit_bytes :=
  lazymatch goal with |- exists bs, length bs = Z.to_nat ?n /\ forall _, mem_inv asegs _ -> bytes_at asegs _ ?p bs =>
    let nn := eval vm_compute in (Z.to_nat n) in
    let r := eval vm_compute in (PropExec.rdn asegs (fun _ => None) (Z_to_bv 64 p) nn) in
    lazymatch r with Some ?bs => exists bs; split; [reflexivity |
      let M' := fresh "M'" in let MIM' := fresh "MIM'" in let B' := fresh "B'" in
      intros M' MIM'; edestruct (img_lit M' p nn bs MIM') as [B' _]; [lia | cbn; lia | vm_compute; reflexivity | exact B']] end
  end.

Ltac fb1 :=
  rewrite <- ?Z.add_assoc;
  match goal with |- fldA _ (_ + (?x + ?y)) _ _ =>
    let z := eval vm_compute in (x + y) in change (x + y) with z end;
  assumption.

Ltac fbl n :=
  let l := eval vm_compute in (map Z.of_nat (seq 0 n)) in
  change (map Z.of_nat (seq 0 n)) with l;
  repeat (apply Forall_cons; [fb1 |]); apply Forall_nil.

Ltac dj := cbn [disjoint_from fst snd]; repeat split; try lia.

Lemma fb_all : forall m A (n : nat) v, Forall (fun k => fldA m (A + k) 1 v) (map Z.of_nat (seq 0 n)) ->
  forall i, 0 <= i < Z.of_nat n -> fldA m (A + i) 1 v.
Proof.
  intros m A n v HF i Hi. rewrite Forall_forall in HF. apply HF. apply in_map_iff. exists (Z.to_nat i). split; [lia|].
  apply in_seq. lia.
Qed.

Ltac pd4_split h := lazymatch type of h with _ /\ _ => let a := fresh "Hf" in destruct h as [a h]; pd4_split h | _ => idtac end.
Ltac pd4_inl := repeat (first [left; reflexivity | right]).
Ltac pd4_rgo K := first [assumption | rewrite K; [assumption | try unfold WD_KEEP; try unfold WD_MKEEP; cbn [In]; pd4_inl]].
Ltac pd4_rgs K := repeat (split; [pd4_rgo K|]); pd4_rgo K.
Ltac pd4_cj := repeat (split; [first [assumption | lia] |]); first [assumption | lia].
Ltac pd4_flw := unfold bp_flw; cbn [fst snd]; lia.
Ltac pd4_fa_flw := repeat (apply Forall_cons; [pd4_flw|]); apply Forall_nil.
Ltac pd4_fa_tt := repeat (apply Forall_cons; [exact I|]); apply Forall_nil.
Ltac pd4_fa_free := repeat (apply Forall_cons; [unfold d4_U_free; cbn [fst snd]; lia|]); apply Forall_nil.
Ltac pd4_fa_wf := repeat (apply Forall_cons; [cbn [wfree fst snd]; split; lia|]); apply Forall_nil.
Ltac pd4_segof M A n nn v GW WM :=
  eapply d4_seg_of_flds; try lia;
  [ eapply LbB_PmMagW.wr_at_sub; [eapply LbB_WoGen.wr_at_wmono; [exact GW | exact WM] | lia | lia | lia]
  | intros ?i ?Hi; apply (fb_all M A nn v); [fbl nn | change (Z.of_nat nn) with n; lia] ].

Lemma pd4_wsr_imp : forall {HCEIL : HeapCeil} (H : asr) ds_repA (e : went H) ff fp mo0 (w : piw H) c0 LBs s0 LB0 m0
    pc REGS S (P P' : mem -> Prop) spent c,
  wsr H ds_repA e ff fp mo0 w c0 LBs s0 LB0 m0 pc REGS S P spent c ->
  (forall XSc s LB m, winv H e ff fp XSc s LB m -> P m -> P' m) ->
  wsr H ds_repA e ff fp mo0 w c0 LBs s0 LB0 m0 pc REGS S P' spent c.
Proof.
  intros HCEIL H ds_repA e ff fp mo0 w c0 LBs s0 LB0 m0 pc REGS S P P' spent c
    (s & R & F & fc & m & XSc & LB & KR & MP & VIS & RF & FZ & HI & SL & RC & RG & AG & OWN & SES & HPm & AL) IMP.
  exists s, R, F, fc, m, XSc, LB.
  split; [exact KR|]. split; [exact MP|]. split; [exact VIS|]. split; [exact RF|]. split; [exact FZ|].
  split; [exact HI|]. split; [exact SL|]. split; [exact RC|]. split; [exact RG|].
  split; [exact AG|]. split; [exact OWN|]. split; [exact SES|].
  split; [exact (IMP XSc s LB m HI HPm)|]. exact AL.
Qed.

Lemma pd4_seg_munch : forall {HCEIL : HeapCeil} W m m' A n v, d4_seg m A n v -> munch W m m' -> wmono asegs m m' ->
  disjoint_from W A n -> 0 <= n -> d4_seg m' A n v.
Proof.
  intros HCEIL W m m' A n v [B Wr] MU WM D Hn. split.
  - eapply bytes_at_transport; [exact B | exact MU |]. rewrite repeat_length, Z2Nat.id by lia. exact D.
  - eapply wr_at_transport; [exact Wr | exact WM].
Qed.

Lemma pd4_rwt : forall W m m' A cs n, rw_cells asegs m A cs -> munch W m m' -> wmono asegs m m' ->
  Z.of_nat (cells_size cs) = n -> disjoint_from W A n -> rw_cells asegs m' A cs.
Proof.
  intros W m m' A cs n Hc MU WM En D. subst n. eapply rw_cells_transport; [exact Hc | exact MU | exact WM | exact D].
Qed.

Lemma pd4_fld2_1 : forall m a, fldA m a 2 0 -> fldA m a 1 0.
Proof.
  intros m a Hf. unfold fldA, fld in *. exact (SeqExec.rdn_firstn ASEGS m 2 (Z_to_bv 64 a) _ 1 Hf ltac:(lia)).
Qed.

Lemma pd4_fld4 : forall m a z, rw_cells asegs m a [C4 (Z_to_bv 64 z)] -> fldA m a 4 z.
Proof.
  intros m a z Hc. unfold fldA, fld.
  pose proof (rw_cells_read asegs m a _ 0%nat _ Hc eq_refl) as RD. replace (a + Z.of_nat 0) with a in RD by lia.
  rewrite <- LbB_Conv.rdn_of_ov. exact RD.
Qed.

Lemma pd4_slot48 : forall m A a b c d f, rw_cells asegs m A [C8 a; C8 b; C8 c; C8 d; C8 f] -> rw_cells asegs m (A + 24) [C8 d].
Proof.
  intros m A a b c d f Hc. change [C8 a; C8 b; C8 c; C8 d; C8 f] with ([C8 a; C8 b; C8 c] ++ [C8 d] ++ [C8 f]) in Hc.
  apply rw_cells_app in Hc as [_ Hc]. apply rw_cells_app in Hc as [Hc _]. exact Hc.
Qed.

Lemma pd4_wm1 : wz 18446744073709551615 = wz (-1).
Proof. unfold wz. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity. Qed.

Lemma pd4_m8 : forall ff, ff mod 64 = 0 -> ff mod 8 = 0.
Proof. intros ff Hm. Z.div_mod_to_equations. lia. Qed.

Lemma pd4_fd : forall ff, ff mod 64 = 0 -> 8 * (ff / 8) = ff.
Proof. intros ff Hm. Z.div_mod_to_equations. lia. Qed.

Lemma pd4_al8 : forall ff k, ff mod 64 = 0 -> k mod 8 = 0 -> (ff + k) mod 8 = 0.
Proof. intros ff k H1 H2. Z.div_mod_to_equations. lia. Qed.

Lemma pd4_al16 : forall ff k, ff mod 64 = 0 -> k mod 16 = 0 -> (ff + k) mod 16 = 0.
Proof. intros ff k H1 H2. Z.div_mod_to_equations. lia. Qed.

Section D4Defs.
  Context {HCEIL : HeapCeil}.

  Definition pd4K (R0 R : bvmap 5 word) : Prop := getr R 22 = getr R0 22 /\ getr R 23 = getr R0 23.
  Definition pd4R0 (ff : Z) (R0 R : bvmap 5 word) : Prop := getr R 18 = wz (ff + 3456) /\ pd4K R0 R.
  Definition pd4R1 (ff : Z) (R0 R : bvmap 5 word) : Prop :=
    getr R 1 = wz (0xea7c4 + 5916) /\ getr R 10 = wz (ff + 608) /\ getr R 11 = wz 0 /\ getr R 12 = wz 16
    /\ getr R 18 = wz (ff + 3456) /\ getr R 24 = wz (ff + 608) /\ pd4K R0 R.
  Definition pd4R2 (ff : Z) (R0 R : bvmap 5 word) : Prop :=
    getr R 18 = wz (ff + 3456) /\ getr R 24 = wz (ff + 608) /\ pd4K R0 R.
  Definition pd4R3 (ff : Z) (R0 R : bvmap 5 word) : Prop :=
    getr R 1 = wz (0xea7c4 + 6000) /\ getr R 10 = wz (ff + 2288) /\ getr R 11 = wz (ff + 608) /\ getr R 12 = wz (ff + 3376)
    /\ getr R 13 = wz (ff + 672) /\ getr R 14 = wz 18446744073709551615 /\ getr R 15 = wz (ff + 736)
    /\ getr R 18 = wz (ff + 2288) /\ getr R 25 = wz (ff + 672) /\ getr R 26 = wz (ff + 736) /\ pd4K R0 R.
  Definition pd4R4 (ff : Z) (R0 R : bvmap 5 word) : Prop :=
    getr R 18 = wz (ff + 2288) /\ getr R 25 = wz (ff + 672) /\ getr R 26 = wz (ff + 736) /\ pd4K R0 R.
  Definition pd4R5 (ff : Z) (R0 R : bvmap 5 word) : Prop :=
    getr R 1 = wz (0xea7c4 + 6116) /\ getr R 10 = wz (ff + 2288) /\ getr R 11 = wz 148032 /\ getr R 12 = wz 46
    /\ getr R 18 = wz (ff + 2288) /\ getr R 21 = wz 18446744073709551608 /\ pd4K R0 R.
  Definition pd4R6 (ff : Z) (R0 R : bvmap 5 word) : Prop :=
    getr R 18 = wz (ff + 2288) /\ getr R 21 = wz 18446744073709551608 /\ pd4K R0 R.
  Definition pd4R7 (ff : Z) (R0 R : bvmap 5 word) : Prop :=
    getr R 1 = wz (0xea7c4 + 6128) /\ getr R 10 = wz (ff + 2288) /\ getr R 21 = wz 18446744073709551608
    /\ getr R 24 = wz 18446744073709551615 /\ pd4K R0 R.
  Definition pd4R8 (R0 R : bvmap 5 word) : Prop :=
    getr R 21 = wz 18446744073709551608 /\ getr R 24 = wz 18446744073709551615 /\ pd4K R0 R.
  Definition pd4R9 (R0 R : bvmap 5 word) : Prop := getr R 24 = wz 18446744073709551615 /\ pd4K R0 R.

  Definition pd4P0 (ff pos : Z) (J : list byte) (m : mem) : Prop :=
    d4_U ff m /\ fldA m (ff + 3536) 8 pos /\ fldA m (ff + 3464) 8 (ff + 3376) /\ rw_cells asegs m (ff + 3376 + 32) [C8 (wz 0)]
    /\ rw_cells asegs m (ff + 608) [CB (Z.to_nat 16) J].
  Definition pd4P1 (ff pos : Z) (J : list byte) (m : mem) : Prop :=
    d4_U ff m /\ fldA m (ff + 3536) 8 pos /\ fldA m (ff + 3464) 8 (ff + 3376) /\ rw_cells asegs m (ff + 3376 + 32) [C8 (wz 0)]
    /\ rw_cells asegs m (ff + 608) [CB (Z.to_nat 16) J] /\ d4_seg m (sh ff + 76) 3 0 /\ d4_seg m (sh ff + 92) 3 0
    /\ d4_seg m (sh ff + 286) 50 0.
  Definition pd4P1s (ff pos : Z) (J : list byte) (m : mem) : Prop := pd4P1 ff pos J m /\ shvis m (ff + 608) (ff + 608 + 16).
  Definition pd4P2 (ff pos : Z) (m : mem) : Prop :=
    d4_U ff m /\ fldA m (ff + 3536) 8 pos /\ fldA m (ff + 3464) 8 (ff + 3376) /\ rw_cells asegs m (ff + 3376 + 32) [C8 (wz 0)]
    /\ d4_seg m (sh ff + 76) 3 0 /\ d4_seg m (sh ff + 92) 3 0 /\ d4_seg m (sh ff + 286) 50 0
    /\ fldA m (ff + 608) 8 0 /\ fldA m (ff + 608 + 8) 8 0.
  Definition pd4P3 (ff pos : Z) (m : mem) : Prop :=
    d4_U ff m /\ rw_cells asegs m (ff + 3376 + 32) [C8 (wz 0)] /\ d4_seg m (sh ff + 76) 3 0 /\ d4_seg m (sh ff + 84) 3 0
    /\ d4_seg m (sh ff + 92) 3 0 /\ d4_seg m (sh ff + 286) 50 0 /\ fldA m (ff + 608) 8 0 /\ fldA m (ff + 608 + 8) 8 0
    /\ fldA m (ff + 608 + 16) 8 pos /\ fldA m (ff + 672) 2 0 /\ fldA m (ff + 736) 2 0.
  Definition pd4P3s (ff pos : Z) (m : mem) : Prop :=
    pd4P3 ff pos m /\ wr_at asegs m ff 4096 /\ (exists j, rw_cells asegs m (ff + 672 + 2) [CB (Z.to_nat 22) j])
    /\ (exists j, rw_cells asegs m (ff + 736 + 2) [CB (Z.to_nat 22) j]).
  Definition pd4P4 (ff : Z) (m : mem) : Prop :=
    d4_U ff m /\ d4_seg m (sh ff + 286) 50 0 /\ fldA m (ff + 672) 1 0 /\ fldA m (ff + 736) 1 0.
  Definition pd4P5 (ff : Z) (m : mem) : Prop :=
    d4_U ff m /\ d4_seg m (sh ff + 286) 50 0 /\ d4_seg m (sh ff + 76) 3 248 /\ d4_seg m (sh ff + 84) 3 248
    /\ d4_seg m (sh ff + 92) 3 248.
  Definition pd4P9 (ff : Z) (m : mem) : Prop :=
    d4_U ff m /\ d4_seg m (sh ff + 286) 50 248 /\ d4_seg m (sh ff + 76) 3 248 /\ d4_seg m (sh ff + 84) 3 248
    /\ d4_seg m (sh ff + 92) 3 248.
End D4Defs.

Section D4.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable ds_repA : list block -> mem -> Z -> Z -> Z -> list block -> Prop.
  Hypothesis DSL : ds_rep_lawsA LINV_P5 ds_repA.
  Hypothesis HTR : ds_tr_ok H.
  Hypothesis CTOR : ds_ctor_stmtA H LINV_P5 ds_repA.
  Hypothesis CSEQ : put_cseq_stmtA H LINV_P5 ds_repA.
  Hypothesis DTOR : ds_dtor_stmtA H LINV_P5 ds_repA.

  Lemma pm_d4 : forall e ff fp Q mo0, bp_klexit H e ff fp Q mo0 -> bp_kd4 H e ff fp Q mo0.
  Proof.
    intros e ff fp Q mo0 KX s LB LBs m mo msF R F fc XSc w c VIS RF FZ KR MP HP HI SL SH RC (RG & A0) WL PL.
    pose proof PL as (ee & PIW & PP & PH & AL & BIN & RWc).
    pose proof (bp_pp_mdef H w LB LBs m c PP) as MD.
    pose proof (bp_al_res H w s _ AL) as HAL.
    pose proof WL as (WLp & WLc & WLw & WLn & _).
    pose proof BIN as (_ & _ & _ & N5).
    assert (HMEAS : pm_meas_ok (pw_n H w) LBs) by (apply (bp_meas H w LB LBs m c PP (bp_phc_st5 _ _ _ _ PH)); rewrite WLn; lia).
    pose proof (rt_bp_base H HHbp) as HH.
    pose proof RG as (R18 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
    pose proof (wframe_bounds H e ff fp XSc s LB m HP HI) as (B0 & B64 & B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
    pose proof (w_geo2 H HHbp ds_repA DSL HTR e ff fp mo0 w c LBs s LB m XSc HP WL PP HI MD HAL) as (G2a & G2b & G2c).
    pose proof (w_geo H HHbp ds_repA DSL HTR e ff fp mo0 w c LBs s LB m XSc HP WL PP HI MD HAL) as WGEO.
    pose proof (WGEO XSc s LB m HI) as (GW10 & GW20 & GL0 & GH0 & GS10 & GS20 & GD10 & GD20).
    pose proof (w_obj H HHbp ds_repA DSL HTR e ff fp mo0 w c LBs s LB m XSc HP WL PP HI MD HAL) as WOBJ.
    pose proof (w_keep_client H HHbp ds_repA DSL HTR e ff fp mo0 w c LBs s LB m XSc HP WL PP HI MD HAL) as WKC.
    pose proof (w_fld_keep H HHbp ds_repA DSL HTR e ff fp mo0 w c LBs s LB m XSc HP WL PP HI MD HAL) as WFK.
    pose proof (w_start H HHbp ds_repA DSL HTR e ff fp mo0 w c LBs s LB m XSc HP WL PP HI MD HAL) as WST.
    pose proof (w_chunk H HHbp ds_repA DSL HTR e ff fp mo0 w c LBs s LB m XSc HP WL PP HI MD HAL) as WCH.
    pose proof (w_exitL H HHbp ds_repA DSL HTR e ff fp mo0 w c LBs s LB m XSc HP WL PP HI MD HAL) as WEX.
    pose proof (w_memset H HHbp ds_repA DSL HTR e ff fp mo0 w c LBs s LB m XSc HP WL PP HI MD HAL HMEAS) as WMS.
    pose proof (w_ctor H HHbp ds_repA DSL HTR e ff fp mo0 w c LBs s LB m XSc HP WL PP HI MD HAL HMEAS CTOR) as WCT.
    pose proof (w_cseq H HHbp ds_repA DSL HTR e ff fp mo0 w c LBs s LB m XSc HP WL PP HI MD HAL HMEAS CSEQ) as WCS.
    pose proof (w_dtor H HHbp ds_repA DSL HTR e ff fp mo0 w c LBs s LB m XSc HP WL PP HI MD HAL HMEAS DTOR) as WDT.
    assert (WOF : WO_FLAGP = 4088) by reflexivity.
    assert (AIS : AINTRIN_STACK = 4096) by reflexivity.
    assert (DSS : DS_SIZE = 392) by reflexivity.
    assert (DEO : DS_ERR_OFF = 360) by reflexivity.
    assert (NSH : nsh DS_SIZE = 49) by reflexivity.
    pose proof (pd4_m8 ff B64) as FM8.
    pose proof (pd4_fd ff B64) as FD.
    assert (SHE : sh ff = ff / 8 + 2147450880) by (unfold sh; rewrite ASHADOW_BASE_val; ring).
    assert (SHE2 : sh (ff + 2288) = sh ff + 286).
    { unfold sh. replace (ff + 2288) with (ff + 286 * 8) by ring. rewrite Z.div_add by lia. ring. }
    assert (C16 : (ff + 3376) mod 16 = 0) by (apply pd4_al16; [exact B64 | reflexivity]).
    assert (DSOBJ : forall m', d4_seg m' (sh ff + 286) 50 0 ->
      ds_obj H ((6, ff, fp) :: w_LF e) m' (wS1 e) (ff + 2288) DS_SIZE /\ obj_inframe ((6, ff, fp) :: w_LF e) (ff + 2288) DS_SIZE).
    { intros m' S286.
      assert (AD : addressable m' (ff + 2288) 392) by (eapply d4_addr17; try lia; exact S286).
      destruct (WOBJ m' 2288 392 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(apply pd4_al8; [exact B64 | reflexivity]) AD) as [O1 I1].
      split; [exact O1 | exact I1]. }
    assert (P5KEEP : forall m5 m6, pd4P5 ff m5 -> LbB_WoDiagC.wxkeep H e ff fp LB [(ff + 2288, ff + 2288 + DS_SIZE)] m5 m6 ->
      pd4P5 ff m6).
    { intros m5 m6 (DU & S286 & S76 & S84 & S92) WK.
      destruct (WKC _ _ _ WK) as (LBk & XS & XP & XC).
      assert (XCs : forall a, sh ff <= a < sh ff + 512 -> xclient H LBk (wS1 e) ([(ff + 2288, ff + 2288 + DS_SIZE)] ++ XS) a).
      { intros a Ha. apply XC; [right; lia | apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil]]. }
      unfold pd4P5.
      split; [eapply d4_U_xpres; [exact XP | intros a Ha; apply XCs; lia | exact DU]|].
      split; [eapply d4_seg_xpres; [exact XP | intros a Ha; apply XCs; lia | exact S286]|].
      split; [eapply d4_seg_xpres; [exact XP | intros a Ha; apply XCs; lia | exact S76]|].
      split; [eapply d4_seg_xpres; [exact XP | intros a Ha; apply XCs; lia | exact S84]|].
      eapply d4_seg_xpres; [exact XP | intros a Ha; apply XCs; lia | exact S92]. }
    pose proof PP as (PR & PSH & HCc & HU & HD & SO & OWN & CW).
    pose proof PR as [PRc _ _ _ _ PRs _ _ _ _ _ _].
    pose proof PRs as [_ _ _ _ PRi _ _ _ _ _ _ _ _ _ _ _].
    assert (POS : exists pos, 0 <= pos < 2 ^ 64 /\ fldA m (ff + 3536) 8 pos).
    { exists (st_icount (pc_state c)). destruct PRi as [PB PF]. split; [exact PB|].
      unfold fldA, fld. rewrite WLp in PF. unfold ST_OFF in PF. replace (ff + 3456 + 48 + 32) with (ff + 3536) in PF by ring.
      exact PF. }
    destruct POS as (pos & POSB & FP0).
    assert (FC0 : fldA m (ff + 3464) 8 (ff + 3376)).
    { rewrite WLp, HCc, WLc in PRc. replace (ff + 3456 + 8) with (ff + 3464) in PRc by ring. exact PRc. }
    rewrite WLc in RWc.
    assert (JJ : exists J, rw_cells asegs m (ff + 608) [CB (Z.to_nat 16) J]) by (eapply w_junk; try eassumption; lia).
    destruct JJ as (J & RWJ0).
    assert (P0m : pd4P0 ff pos J m).
    { split; [eapply d4_U_of_shad; exact SH|]. split; [exact FP0|]. split; [exact FC0|]. split; [exact RWc|]. exact RWJ0. }

    apply (WST Q msF mo R F fc BP_D4 (pd4R0 ff R) (pd4P0 ff pos J) VIS RF FZ KR MP SL RC);
      [split; [exact R18 | split; reflexivity] | exact P0m |].
    intros c1 W1.
    apply (WCH Q BP_D4 AASAN_MEMSET (pd4R0 ff R) (pd4R1 ff R) None (pd4P0 ff pos J) (pd4P1 ff pos J) 0 c1 W1).
    { intros R1 F1 fc1 m1 XSc1 s1 LB1 (G18 & K22 & K23) RC1 (DU & FP & FC & RW32 & RWJ) HI1 SL1 _.
      destruct (WGEO XSc1 s1 LB1 m1 HI1) as (GW1 & GW2 & GL & GH & GS1 & GS2 & GD1 & GD2).
      pose proof RC1 as (C2 & C3 & C4 & C8 & C9 & C19 & C20).
      destruct (wd_d1_ea7c4 R1 F1 fc1 m1 ff) as (R' & M' & MS & MU & WM & POST); [unfold wd_d1_pre; pd4_cj|].
      pd4_split POST.
      assert (S76 : d4_seg M' (ff / 8 + 2147450956) 3 (0 mod 256)) by (pd4_segof M' (ff / 8 + 2147450956) 3 3%nat 0 GW2 WM).
      assert (S92 : d4_seg M' (ff / 8 + 2147450972) 3 (0 mod 256)) by (pd4_segof M' (ff / 8 + 2147450972) 3 3%nat 0 GW2 WM).
      assert (S286 : d4_seg M' (ff / 8 + 2147451166) 50 (0 mod 256)) by (pd4_segof M' (ff / 8 + 2147451166) 50 50%nat 0 GW2 WM).
      exists R', M'. eexists.
      split; [exact MS|]. split; [exact MU|]. split; [exact WM|]. split; [pd4_fa_flw|]. split; [pd4_fa_tt|].
      split; [unfold bp_rc; pd4_rgs POST|]. split; [unfold pd4R1, pd4K; pd4_rgs POST|].
      unfold pd4P1.
      split; [eapply d4_U_munch; [exact DU | exact MU | exact WM | pd4_fa_free]|].
      split; [eapply fld_munch; [exact FP | exact MU | dj | lia | lia]|].
      split; [eapply fld_munch; [exact FC | exact MU | dj | lia | lia]|].
      split; [eapply (pd4_rwt _ _ _ _ _ 8); [exact RW32 | exact MU | exact WM | reflexivity | dj]|].
      split; [eapply (pd4_rwt _ _ _ _ _ 16); [exact RWJ | exact MU | exact WM | reflexivity | dj]|].
      split; [rewrite SHE; replace (ff / 8 + 2147450880 + 76) with (ff / 8 + 2147450956) by ring; exact S76|].
      split; [rewrite SHE; replace (ff / 8 + 2147450880 + 92) with (ff / 8 + 2147450972) by ring; exact S92|].
      rewrite SHE; replace (ff / 8 + 2147450880 + 286) with (ff / 8 + 2147451166) by ring; exact S286. }
    intros c2 W2.
    assert (W2' : wsr H ds_repA e ff fp mo0 w c LBs s LB m AASAN_MEMSET (pd4R1 ff R) None (pd4P1s ff pos J) 0 c2).
    { eapply pd4_wsr_imp; [exact W2|]. intros XSc' s' LB' m' HI' P1m. split; [exact P1m|].
      eapply w_shvis; try eassumption; lia. }
    apply (WMS Q (pd4R1 ff R) (pd4R2 ff R) None (pd4P1s ff pos J) (pd4P2 ff pos) 0 c2 (0xea7c4 + 5916) (ff + 608) 0 16 J W2').
    { intros Ra (A1 & A10 & A11 & A12 & _). pd4_cj. }
    { reflexivity. }
    { lia. }
    { lia. }
    { lia. }
    { pd4_flw. }
    { exact I. }
    { lia. }
    { lia. }
    { lia. }
    { exact I. }
    { intros m2 ((DU & FP & FC & RW32 & RWJ & S76 & S92 & S286) & SV). split; [exact RWJ|]. split; [|exact SV].
      eapply w_acc; [eapply d4_addr9_16; try lia; exact S76 | lia]. }
    { intros Ra Rb (A1 & A10 & A11 & A12 & A18 & A24 & K22 & K23) KP. unfold pd4R2, pd4K. pd4_rgs KP. }
    { intros m2 m3 ((DU & FP & FC & RW32 & RWJ & S76 & S92 & S286) & SV) MU WM RZ.
      assert (Z0 : fldA m3 (ff + 608 + 0) 8 0) by (eapply w_zero_fld; [exact RZ | lia | rewrite Z2Nat.id by lia; lia]).
      assert (Z8 : fldA m3 (ff + 608 + 8) 8 0) by (eapply w_zero_fld; [exact RZ | lia | rewrite Z2Nat.id by lia; lia]).
      rewrite Z.add_0_r in Z0.
      unfold pd4P2.
      split; [eapply d4_U_munch; [exact DU | exact MU | exact WM | pd4_fa_free]|].
      split; [eapply fld_munch; [exact FP | exact MU | dj | lia | lia]|].
      split; [eapply fld_munch; [exact FC | exact MU | dj | lia | lia]|].
      split; [eapply (pd4_rwt _ _ _ _ _ 8); [exact RW32 | exact MU | exact WM | reflexivity | dj]|].
      split; [eapply pd4_seg_munch; [exact S76 | exact MU | exact WM | dj | lia]|].
      split; [eapply pd4_seg_munch; [exact S92 | exact MU | exact WM | dj | lia]|].
      split; [eapply pd4_seg_munch; [exact S286 | exact MU | exact WM | dj | lia]|].
      split; [exact Z0 | exact Z8]. }
    intros c3 W3.
    apply (WCH Q (0xea7c4 + 5916) ADS_CTOR (pd4R2 ff R) (pd4R3 ff R) None (pd4P2 ff pos) (pd4P3 ff pos) 0 c3 W3).
    { intros R2 F2 fc2 m2 XSc2 s2 LB2 (A18 & A24 & K22 & K23) RC2 (DU & FP & FC & RW32 & S76 & S92 & S286 & Z0 & Z8) HI2 SL2 _.
      destruct (WGEO XSc2 s2 LB2 m2 HI2) as (GW1 & GW2 & GL & GH & GS1 & GS2 & GD1 & GD2).
      pose proof RC2 as (C2 & C3 & C4 & C8 & C9 & C19 & C20).
      pose proof SL2 as (_ & SLb & _).
      assert (F48 : fldA m2 (wS1 e + 48) 8 (ff + 2224)).
      { apply pd4_slot48 in SLb. replace (wS1 e + 48) with (wS1 e + 24 + 24) by ring. apply w_fld_of_cells8; [exact SLb | lia]. }
      destruct (wd_d2_ea7c4 R2 F2 fc2 m2 ff (wS1 e) (ff + 3376) pos) as (R' & M' & MS & MU & WM & POST);
        [unfold wd_d2_pre; pd4_cj|].
      pd4_split POST.
      assert (S84 : d4_seg M' (ff / 8 + 2147450964) 3 (0 mod 256)) by (pd4_segof M' (ff / 8 + 2147450964) 3 3%nat 0 GW2 WM).
      exists R', M'. eexists.
      split; [exact MS|]. split; [exact MU|]. split; [exact WM|]. split; [pd4_fa_flw|]. split; [pd4_fa_tt|].
      split; [unfold bp_rc; pd4_rgs POST|]. split; [unfold pd4R3, pd4K; pd4_rgs POST|].
      unfold pd4P3.
      split; [eapply d4_U_munch; [exact DU | exact MU | exact WM | pd4_fa_free]|].
      split; [eapply (pd4_rwt _ _ _ _ _ 8); [exact RW32 | exact MU | exact WM | reflexivity | dj]|].
      split; [eapply pd4_seg_munch; [exact S76 | exact MU | exact WM | dj | lia]|].
      split; [rewrite SHE; replace (ff / 8 + 2147450880 + 84) with (ff / 8 + 2147450964) by ring; exact S84|].
      split; [eapply pd4_seg_munch; [exact S92 | exact MU | exact WM | dj | lia]|].
      split; [eapply pd4_seg_munch; [exact S286 | exact MU | exact WM | dj | lia]|].
      split; [eapply fld_munch; [exact Z0 | exact MU | dj | lia | lia]|].
      split; [eapply fld_munch; [exact Z8 | exact MU | dj | lia | lia]|].
      split; [replace (ff + 608 + 16) with (ff + 624) by ring; assumption|].
      split; assumption. }
    intros c4 W4.
    assert (W4' : wsr H ds_repA e ff fp mo0 w c LBs s LB m ADS_CTOR (pd4R3 ff R) None (pd4P3s ff pos) 0 c4).
    { eapply pd4_wsr_imp; [exact W4|]. intros XSc' s' LB' m' HI' P3m.
      destruct (WGEO XSc' s' LB' m' HI') as (GW1 & _).
      split; [exact P3m|]. split; [exact GW1|]. split; eapply w_junk; try eassumption; lia. }
    apply (WCT Q (pd4R3 ff R) (pd4R4 ff R) (pd4P3s ff pos) (pd4P4 ff) 0 c4 (0xea7c4 + 6000) (ff + 2288) (ff + 608)
      (ff + 3376) (ff + 672) (ff + 736) (-1) W4').
    { intros Ra (A1 & A10 & A11 & A12 & A13 & A14 & A15 & _).
      split; [exact A1|]. split; [exact A10|]. split; [exact A11|]. split; [exact A12|]. split; [exact A13|].
      split; [rewrite A14; reflexivity | exact A15]. }
    { reflexivity. }
    { lia. }
    { unfold PM_RESERVE; lia. }
    { lia. }
    { lia. }
    { lia. }
    { intros m4 ((DU & RW32 & S76 & S84 & S92 & S286 & Z0 & Z8 & Z16 & F672 & F736) & W4096 & (j1 & J1) & (j2 & J2)).
      assert (AD1 : addressable m4 (ff + 608) 24) by (eapply d4_addr9; try lia; exact S76).
      assert (AD2 : addressable m4 (ff + 672) 24) by (eapply d4_addr10; try lia; exact S84).
      assert (AD3 : addressable m4 (ff + 736) 24) by (eapply d4_addr11; try lia; exact S92).
      assert (AD5 : addressable m4 (ff + 3376) 48) by (eapply d4_addr_cons; try lia; exact DU).
      destruct (DSOBJ m4 S286) as [O0 I0].
      destruct (WOBJ m4 608 24 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(apply pd4_al8; [exact B64 | reflexivity]) AD1) as [O1 I1].
      destruct (WOBJ m4 672 24 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(apply pd4_al8; [exact B64 | reflexivity]) AD2) as [O2 I2].
      destruct (WOBJ m4 736 24 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(apply pd4_al8; [exact B64 | reflexivity]) AD3) as [O3 I3].
      destruct (WOBJ m4 3376 48 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(apply pd4_al8; [exact B64 | reflexivity]) AD5) as [O5 I5].
      exists [Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 pos], j1, j2.
      split; [exact O0|]. split; [eapply LbB_PmMagW.wr_at_sub; [exact W4096 | lia | lia | lia]|]. split; [exact I0|].
      split; [exact O1|].
      split; [eapply w_u64arr3; [exact Z0 | exact Z8 | exact Z16 | eapply LbB_PmMagW.wr_at_sub; [exact W4096 | lia | lia | lia]
                                 | lia | lia | lia]|].
      split; [reflexivity|]. split; [exact I1|].
      split; [exact O2|]. split; [eapply w_str; [exact F672 | eapply LbB_PmMagW.wr_at_sub; [exact W4096 | lia | lia | lia] | exact J1]|].
      split; [exact I2|].
      split; [exact O3|]. split; [eapply w_str; [exact F736 | eapply LbB_PmMagW.wr_at_sub; [exact W4096 | lia | lia | lia] | exact J2]|].
      split; [exact I3|].
      split; [exact O5|]. split; [exact RW32|].
      intros a Ha. rewrite DSS in Ha. repeat split; lia. }
    { intros Ra Rb (A1 & A10 & A11 & A12 & A13 & A14 & A15 & A18 & A25 & A26 & K22 & K23) KP. unfold pd4R4, pd4K. pd4_rgs KP. }
    { intros m4 m5 ((DU & RW32 & S76 & S84 & S92 & S286 & Z0 & Z8 & Z16 & F672 & F736) & _) WK.
      destruct (WKC _ _ _ WK) as (LBk & XS & XP & XC).
      assert (XCs : forall a, sh ff <= a < sh ff + 512 -> xclient H LBk (wS1 e) ([(ff + 2288, ff + 2288 + DS_SIZE)] ++ XS) a).
      { intros a Ha. apply XC; [right; lia | apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil]]. }
      unfold pd4P4.
      split; [eapply d4_U_xpres; [exact XP | intros a Ha; apply XCs; lia | exact DU]|].
      split; [eapply d4_seg_xpres; [exact XP | intros a Ha; apply XCs; lia | exact S286]|].
      split; [apply (WFK _ m4 m5 (ff + 672) 1%nat 0 WK);
              [left; lia | apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil] | apply pd4_fld2_1; exact F672]|].
      apply (WFK _ m4 m5 (ff + 736) 1%nat 0 WK);
        [left; lia | apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil] | apply pd4_fld2_1; exact F736]. }
    intros c5 W5.
    apply (WCH Q (0xea7c4 + 6000) APUT_CSEQ (pd4R4 ff R) (pd4R5 ff R) _ (pd4P4 ff) (pd4P5 ff) 0 c5 W5).
    { intros R4 F4 fc4 m4 XSc4 s4 LB4 (A18 & A25 & A26 & K22 & K23) RC4 (DU & S286 & F672 & F736) HI4 SL4 _.
      destruct (WGEO XSc4 s4 LB4 m4 HI4) as (GW1 & GW2 & GL & GH & GS1 & GS2 & GD1 & GD2).
      pose proof RC4 as (C2 & C3 & C4 & C8 & C9 & C19 & C20).
      destruct (wd_d3_ea7c4 R4 F4 fc4 m4 ff) as (R' & M' & MS & MU & WM & POST); [unfold wd_d3_pre; pd4_cj|].
      pd4_split POST.
      assert (T76 : d4_seg M' (ff / 8 + 2147450956) 3 (18446744073709551608 mod 256))
        by (pd4_segof M' (ff / 8 + 2147450956) 3 3%nat 18446744073709551608 GW2 WM).
      assert (T84 : d4_seg M' (ff / 8 + 2147450964) 3 (18446744073709551608 mod 256))
        by (pd4_segof M' (ff / 8 + 2147450964) 3 3%nat 18446744073709551608 GW2 WM).
      assert (T92 : d4_seg M' (ff / 8 + 2147450972) 3 (18446744073709551608 mod 256))
        by (pd4_segof M' (ff / 8 + 2147450972) 3 3%nat 18446744073709551608 GW2 WM).
      exists R', M'. eexists.
      split; [exact MS|]. split; [exact MU|]. split; [exact WM|]. split; [pd4_fa_flw|]. split; [pd4_fa_wf|].
      split; [unfold bp_rc; pd4_rgs POST|]. split; [unfold pd4R5, pd4K; pd4_rgs POST|].
      unfold pd4P5.
      split; [eapply d4_U_munch; [exact DU | exact MU | exact WM | pd4_fa_free]|].
      split; [eapply pd4_seg_munch; [exact S286 | exact MU | exact WM | dj | lia]|].
      split; [rewrite SHE; replace (ff / 8 + 2147450880 + 76) with (ff / 8 + 2147450956) by ring; exact T76|].
      split; [rewrite SHE; replace (ff / 8 + 2147450880 + 84) with (ff / 8 + 2147450964) by ring; exact T84|].
      rewrite SHE; replace (ff / 8 + 2147450880 + 92) with (ff / 8 + 2147450972) by ring; exact T92. }
    intros c6 W6.
    apply (WCS Q (pd4R5 ff R) (pd4R6 ff R) (pd4P5 ff) (pd4P5 ff) 0 c6 (0xea7c4 + 6116) (ff + 2288) (-1) 0 148032 46 W6).
    { intros Ra (A1 & A10 & A11 & A12 & _). pd4_cj. }
    { reflexivity. }
    { lia. }
    { unfold ds_cost, PM_RESERVE; lia. }
    { lia. }
    { lia. }
    { intros m6 (DU & S286 & _). exact (DSOBJ m6 S286). }
    { lia. }
    { unfold AIMG_LO; lia. }
    { unfold AIMG_TOP; lia. }
    { lit_acc. }
    { lit_bytes. }
    { lia. }
    { intros Ra Rb (A1 & A10 & A11 & A12 & A18 & A21 & K22 & K23) KP _. unfold pd4R6, pd4K. pd4_rgs KP. }
    { exact P5KEEP. }
    intros c7 W7.
    apply (WCH Q (0xea7c4 + 6116) ADS_DTOR (pd4R6 ff R) (pd4R7 ff R) _ (pd4P5 ff) (pd4P5 ff) _ c7 W7).
    { intros R6 F6 fc6 m6 XSc6 s6 LB6 (A18 & A21 & K22 & K23) RC6 P5m HI6 SL6 SES.
      pose proof RC6 as (C2 & C3 & C4 & C8 & C9 & C19 & C20).
      destruct SES as (DB & DR & _ & _).
      pose proof DSL as [_ DE _ _ _ _].
      pose proof (pd4_fld4 _ _ _ (DE _ _ _ _ _ _ DR)) as FE.
      destruct (wd_d4_ea7c4 R6 F6 fc6 m6 ff) as (R' & M' & MS & POST).
      { unfold wd_d4_pre. split; [exact A18|]. split; [replace (ff + 2648) with (ff + 2288 + DS_ERR_OFF) by lia; exact FE|]. lia. }
      pd4_split POST. subst M'.
      exists R', m6, []. split; [exact MS|]. split; [apply munch_refl|]. split; [intros x Hx; exact Hx|].
      split; [apply Forall_nil|]. split; [apply Forall_nil|].
      split; [unfold bp_rc; pd4_rgs POST|]. split; [unfold pd4R7, pd4K; pd4_rgs POST|]. exact P5m. }
    intros c8 W8.
    apply (WDT Q (pd4R7 ff R) (pd4R8 R) (pd4P5 ff) (pd4P5 ff) _ c8 (0xea7c4 + 6128) (ff + 2288) (-1) (0 + 46) W8).
    { intros Ra (A1 & A10 & _). split; assumption. }
    { reflexivity. }
    { lia. }
    { unfold ds_cost, PM_RESERVE; lia. }
    { unfold PO_PF; pd4_inl. }
    { lia. }
    { lia. }
    { intros m8 (DU & S286 & _). exact (DSOBJ m8 S286). }
    { intros Ra Rb (A1 & A10 & A21 & A24 & K22 & K23) KP. unfold pd4R8, pd4K. pd4_rgs KP. }
    { exact P5KEEP. }
    intros c9 W9.
    apply (WCH Q (0xea7c4 + 6128) BP_LEXIT (pd4R8 R) (pd4R9 R) None (pd4P5 ff) (pd4P9 ff) _ c9 W9).
    { intros R8 F8 fc8 m8 XSc8 s8 LB8 (A21 & A24 & K22 & K23) RC8 (DU & S286 & S76 & S84 & S92) HI8 SL8 _.
      destruct (WGEO XSc8 s8 LB8 m8 HI8) as (GW1 & GW2 & GL & GH & GS1 & GS2 & GD1 & GD2).
      pose proof RC8 as (C2 & C3 & C4 & C8 & C9 & C19 & C20).
      destruct (wd_d5_ea7c4 R8 F8 fc8 m8 ff) as (R' & M' & MS & MU & WM & POST); [unfold wd_d5_pre; pd4_cj|].
      pd4_split POST.
      assert (T286 : d4_seg M' (ff / 8 + 2147451166) 50 (18446744073709551608 mod 256))
        by (pd4_segof M' (ff / 8 + 2147451166) 50 50%nat 18446744073709551608 GW2 WM).
      exists R', M'. eexists.
      split; [exact MS|]. split; [exact MU|]. split; [exact WM|]. split; [pd4_fa_flw|]. split; [pd4_fa_tt|].
      split; [unfold bp_rc; pd4_rgs POST|]. split; [unfold pd4R9, pd4K; pd4_rgs POST|].
      unfold pd4P9.
      split; [eapply d4_U_munch; [exact DU | exact MU | exact WM | pd4_fa_free]|].
      split; [rewrite SHE; replace (ff / 8 + 2147450880 + 286) with (ff / 8 + 2147451166) by ring; exact T286|].
      split; [eapply pd4_seg_munch; [exact S76 | exact MU | exact WM | dj | lia]|].
      split; [eapply pd4_seg_munch; [exact S84 | exact MU | exact WM | dj | lia]|].
      eapply pd4_seg_munch; [exact S92 | exact MU | exact WM | dj | lia]. }
    intros c10 W10.
    unfold bp_klexit in KX.
    lazymatch type of KX with
    | bp_kexit _ _ _ _ _ _ _ ?RX _ _ =>
      apply (WEX Q BP_LEXIT (pd4R9 R) RX (pd4P9 ff) _ c10 D4L (bp_slots H) (-1) W10)
    end.
    { unfold ds_cost, PM_RESERVE; lia. }
    { exact PL. }
    { intros m10 (DU & S286 & S76 & S84 & S92). eapply d4_shad_of; try lia; assumption. }
    { intros m10 SLm _. exact SLm. }
    { intros R10 (A24 & K22 & K23). split; [cbv beta; split; [rewrite K22; exact R22 | rewrite K23; exact R23]
                                           | rewrite A24; exact pd4_wm1]. }
    { lia. }
    exact KX.
  Qed.
End D4.
