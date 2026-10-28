(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5 PmFloatXSpecs_u5 PmFloatXTu_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import MState Mem Exec Frame Cells Step Arr FP.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Bridge Require Import BrRegs BrBase BrXfer BrMem.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.TUX Require Import G3PureX_u5 FiWalkX_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX CutHeap2V.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5 ParseBridges2_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require Import SmallPure.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncSums_u5 EncKit_u5 EncSinkBridges_u5 EncTail_u5 EncPure_u5 EncSinkBridgesU.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmFloatX Require Import FxSums. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmFloatX Require Import FxKitX_u5 DumpBufX_u5 WdBrX_u5 DtoaTrueXHU FxKitXU.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Cut_fi_u64_xsrc_T_u5 Cut_fi_u64_xsrc_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module FIUU.
Import PMES.
Module G := Cut_fi_u64_xsrc_u5.
Module GT := Cut_fi_u64_xsrc_T_u5.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation uv := PB.uv.
Lemma uv_add_lit' : forall E e z, PB.uv E (EAlu Instr.ALU_ADD e (ELit z)) = (PB.uv E e + z) mod 2 ^ 64.
Proof. exact DBX.uv_add_lit. Qed.
Definition RETPC : Z := 0x3ebc0.
Definition S2E : expr := EVar 32.
Definition F0 : list SGP.region := [(EVar 2, -8816, ELit 8816)].
Definition SPE : expr := EAlu Instr.ALU_ADD (EVar 2) (ELit (-320)).
Definition KC1 : expr := EAlu Instr.ALU_ADD (EVar 33) (ELit (-1)).      (* [comment removed for export] *)
Definition KK1 : expr := EAlu Instr.ALU_ADD (EVar 48) (ELit (-1)).      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition KEXIT : kentry := KRange (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 2) (EVar 48)) (ELit (-296))) (EAlu Instr.ALU_ADD (EVar 2) (ELit (-295)))) 1 1.

Lemma heap_ok3 : CH2.heap_chk3 GT.NF G.HDECL G.BLS G.CPS G.TAGS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.

Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.
Definition ret_cut (i k : nat) : nat := match CH2.ret_of G.RETS i k with Some j => j | None => 0%nat end.
Definition sinkj (f : CC.cutpoint -> SR.post_spec -> CC.cutpoint -> CA.blocks -> CA.blocks -> option CH2.cinfo) (i k : nat) (c : CC.cutpoint) (ps : SR.post_spec) : bool :=
  let j := ret_cut i k in
  (negb (Nat.eqb j 0) && match nth_error G.CPS j with Some cj => isSome (f c ps cj (nth i G.BLS []) (nth j G.BLS [])) | None => false end)%bool.
(* [comment removed for export] *)
Definition kind (i k : nat) : nat := (match i, k with | 0, 0 => 7 | 1, 0 => 2 | 2, 0 => 6 | 2, 1 => 7 | _, _ => 0 end)%nat.
Definition goto_chk (i j : nat) (s : CC.subst) (cells : list kentry) : bool := (match i, j with | 0%nat, 1%nat => expr_eqb (CC.slook s 48) KC1 | 2%nat, 1%nat => (expr_eqb (CC.slook s 48) KK1 && CC.has_cell cells (KRange KK1 0 19))%bool | _, _ => false end)%bool.
Definition exit_a0 (i : nat) (ps : SR.post_spec) : bool := match i with 2%nat => CL.ps_reg_is ps 10 (EVar 33) | _ => false end.

Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  let cells := SR.ps_cells ps in
  (SP.F_sub (CC.cp_F c) F0 && Nat.leb 49 (CC.cp_nx c)) &&
  match t with
  | CC.TGoto j s => (Nat.eqb (kind i k) 7 && goto_chk i j s cells)%bool
  | CC.TOther pc =>
      if Z.eqb pc PML.PC_STR_PUSH_BACK then (Z.eqb (SR.ps_pc ps) pc && sinkj (ESBU.pushb_chk GT.NF G.HDECL S2E 0) i k c ps && Nat.eqb (kind i k) 2)%bool
      else (PB.exit_base_chk GT.NF RETPC c ps && exit_a0 i ps && CC.has_cell cells KEXIT && CC.has_cell cells (KRange (EVar 48) 0 19) && Nat.eqb (kind i k) 6)%bool
  end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition phase (i : nat) (c k p : Z) : Prop := match i with | 0%nat => p = 0 | 1%nat => p = c - 1 - k | 2%nat => p = c - k | _ => False end.

Definition REGS0 : list expr := Eval vm_compute in CC.cp_regs G.cp0.
Definition KNOW0 : list kentry := Eval vm_compute in CC.cp_know G.cp0.
Lemma regs0 : CC.cp_regs G.cp0 = REGS0. Proof. vm_compute. reflexivity. Qed.
Lemma know0 : CC.cp_know G.cp0 = KNOW0. Proof. vm_compute. reflexivity. Qed.

Section FromIntOk.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  CatSim.msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis PUSHB_OK : str_push_back_x_specU L HI.

Theorem from_integer_u64_x_ok : from_integer_u64_x_specU L HI.
Proof.
  intros v LBo cr sp r SK S2 kx bx rep. unfold PML.cps_heap.
  intros fx R M model K HH Hmo HKnil Hfp (Hentry & (Ha0 & Hv & Ha1) & HskS2 & Hsk1 & Hsk2 & Hapsk & Hsink & Hobj & Himg & Hcred & Hroom) Hcont.
  destruct Hentry as (Hra & Hraok & Hsp & Htp & Hstk). destruct Hstk as (S1 & S2'' & S3 & S4 & S5).
  unfold FROMINT_SCR, STRX_SCR, PMS.STR_SCR, PMS.OPNEW_SCR, PML.HEAP_STACK in *.
  change (320 + (256 + (16 + 8224))) with 8816 in *.
  pose proof (PmLayout.ly_segs L LAY) as LS. pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI.
  pose proof (PmLayout.ly_errno L LAY) as LER.
  pose proof Hobj as (OS1 & OS2 & OS3). unfold PML.apart in Hapsk.
  set (len0 := len (PML.srep_chars rep)).
  assert (ROOM : len0 + 20 <= CLU) by exact Hroom.
  assert (CLO : 0x7fff7f800000 <= hl_ceil L) by (unfold hl_ceil; lia).
  assert (SCRV : CH.hd_scr G.HDECL = 8816) by reflexivity.
  assert (STKF : sp mod 16 = 0 /\ hl_ceil L + CH.hd_scr G.HDECL <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47)
    by (rewrite SCRV; unfold hl_ceil; repeat split; lia).
  assert (SPR : hl_ceil L + 8816 <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47) by (unfold hl_ceil; repeat split; lia).
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (rewrite SCRV; lia).
  assert (NF32 : (32 <= GT.NF)%nat) by (unfold GT.NF; lia).
  set (W := [(S2, 24)]).
  assert (W_OK : forall (w : L5.range) (a : Z), In w W -> L5.in_rng w a -> CH2.wclient L sp a).
  { intros w a [<-|[]] Hin; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; (split; [lia | left; lia]). }
  assert (IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img G.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_alloc_static L a /\ ~ in_errno L a).
  { intros rg a []. }
  assert (DEF0 : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)).
  { rewrite SCRV. intros j Hj. apply S5. lia. }
  assert (W_S2 : In (S2, 24) W) by (left; reflexivity).
  set (CredV := ESBU.CredV L kx bx).
  set (gB := ESBU.gB []).
  assert (GBL : forall g1, gB g1 = PML.srep_blocks (ESBU.s_rep g1)) by (intros g1; unfold gB, ESBU.gB; apply app_nil_r).
  assert (CREDIE : forall g i j E E' cr1, CredV g i E cr1 -> CredV g j E' cr1) by (intros g i j E E' cr1 HC; exact HC).
  assert (KIMG : forall LBx a, 0x10000 <= a < PML.IMG_RO_HI -> L5C.kept L LBx sp (CH.hd_scr G.HDECL) W a).
  { intros LBx a Ha. unfold PML.IMG_RO_HI in Ha. apply L5C.kept_static; [rewrite ILO, IHI; lia | intros X; pose proof (PmLayout.ly_static L LAY a X); lia | rewrite ILO; lia | rewrite IHI; lia | rewrite LER; lia|].
    intros w [<-|[]]; unfold L5.in_rng; cbn [fst snd]; lia. }
  assert (HBLK : forall b, In b (LBo ++ PML.srep_blocks rep) -> block_range L (fst b) (snd b)).
  { intros b Hb. destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hwf & _). apply (Hwf b Hb). }
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (MAIN : forall (c : Z) (fx1 : FPState) (R1 : bvmap 5 word) (M1 : mem),
     1 <= c <= 20 ->
     let E0 := Env (reg_ev R (fun v0 => Z_to_bv 64 (nth (v0 - 32) [S2; c] 0))) (fun _ => []) in
     CC.At RSEGS G.cp0 (DTXHU.EX E0 R1) R1 M1 -> PML.fp_ok fx1 ->
     (forall x : word, ~ (sp - 8816 <= bv_unsigned x < sp) -> M1 x = M x) -> L5.defined M1 (sp - 8816) 8816 ->
     srealizes RSEGS SCFG (@PML.cfg fx1 R1 (CC.cp_pc G.cp0) M1 model) K).
  { intros c fx1 R1 M1 Hc E0 HAt1 Hfp1 FR1 DALL1.
    set (E1 := DTXHU.EX E0 R1) in HAt1.
    assert (EV : forall x : reg, ev E0 (ridx x) = getr R x) by (intros x; apply CL5.ev_reg).
    assert (EV1 : forall x : reg, ev E1 (ridx x) = getr R x).
    { intros x. unfold E1. rewrite DTXHU.EX_lo by (pose proof (ridx_range x); lia). apply EV. }
    assert (V2 : ev E1 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV1 2%bv)).
    assert (V4 : ev E1 4 = Z_to_bv 64 PML.TP) by (rewrite <- Htp; exact (EV1 4%bv)).
    assert (V10 : ev E1 10 = Z_to_bv 64 v) by (rewrite <- Ha0; exact (EV1 10%bv)).
    assert (V11 : ev E1 11 = Z_to_bv 64 SK) by (rewrite <- Ha1; exact (EV1 11%bv)).
    assert (V32 : ev E1 32 = Z_to_bv 64 S2) by reflexivity.
    assert (V33 : ev E1 33 = Z_to_bv 64 c) by reflexivity.
    assert (U2 : bv_unsigned (ev E1 2) = sp) by (rewrite V2; apply u64_of_Z; lia).
    assert (U10 : bv_unsigned (ev E1 10) = v) by (rewrite V10; apply u64_of_Z; lia).
    assert (U11 : bv_unsigned (ev E1 11) = SK) by (rewrite V11; apply u64_of_Z; lia).
    assert (U32 : bv_unsigned (ev E1 32) = S2) by (rewrite V32; apply u64_of_Z; lia).
    assert (U33 : bv_unsigned (ev E1 33) = c) by (rewrite V33; apply u64_of_Z; lia).
    assert (TP0 : ev E1 4 = Z_to_bv 64 (hl_tp L)) by (rewrite V4, (PmLayout.ly_tp L LAY); reflexivity).
    assert (CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CH2.in_reg E1 rg a -> CH2.sclient L LBo sp a)).
    { intros rg [<-|[]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CH2.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot] in Ha.
      rewrite U11 in Ha. rewrite u64_of_Z in Ha by lia. split; [lia | left; lia]. }
    assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CH2.in_reg E1 rg a -> exists w : L5.range, In w W /\ L5.in_rng w a)).
    { intros rg [<-|[]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CH2.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot] in Ha.
      rewrite U32 in Ha. rewrite u64_of_Z in Ha by lia. exists (S2, 24). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia]. }
    assert (OADDR : estart E1 (SA S2E 0) = S2) by (unfold estart, S2E; cbn [a_base a_off edenot]; rewrite U32; lia).
    assert (FRZ1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 8816 <= a < sp) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha Hn'. apply FR1. rewrite u64_of_Z by lia. exact Hn'. }
    assert (GR1 : mem_grows M M1).
    { intros x Hx. pose proof (bv_unsigned_in_range _ x) as Rx. unfold bv_modulus in Rx.
      destruct (Z_lt_le_dec (bv_unsigned x) (sp - 8816)) as [Hlo|Hlo]; [rewrite (FR1 x) by lia; exact Hx|].
      destruct (Z_lt_le_dec (bv_unsigned x) sp) as [Hhi|Hhi]; [|rewrite (FR1 x) by lia; exact Hx].
      pose proof (DALL1 (bv_unsigned x - (sp - 8816)) ltac:(lia)) as D. replace (sp - 8816 + (bv_unsigned x - (sp - 8816))) with (bv_unsigned x) in D by lia.
      rewrite Z_to_bv_bv_unsigned in D. exact D. }
    set (XIv := fun (g1 : ESBU.sghost) (i : nat) (E : env) (M2 : mem) => ESBU.sink_inv M2 S2 g1 /\ phase i c (uv E (EVar 48)) (ESBU.s_len g1 - len0)).
    assert (AGE : forall i cp E E', nth_error G.CPS i = Some cp -> env_agree GT.NF E1 E -> env_agree (CC.cp_nx cp) E E' -> env_agree GT.NF E1 E').
    { intros i cp E E' Hcp H1 H2. eapply CC.env_agree_trans; [exact H1 | eapply CC.env_agree_le; [exact H2 | exact (G.NF_le i cp Hcp)]]. }
    assert (BRG : forall g1 M0c i E (M2 : mem) m1, CH2V.heap_ambV L HI GT.NF E1 model LBo sp G.HDECL W G.BLS ESBU.sghost gB CredV g1 M0c i E M2 m1 ->
                    (forall b, In b (PML.srep_blocks (ESBU.s_rep g1)) -> block_range L (fst b) (snd b)) /\ env_agree GT.NF E1 E /\
                    exists cr1, hi_heap HI (CH2.den E (nth i G.BLS []) ++ LBo ++ gB g1) cr1 M2 (m_vmmaps m1) /\ CredV g1 i E cr1).
    { intros g1 M0c i E M2 m1 (_ & _ & HagE & (cr1 & HH1 & HC1) & _). split; [|split; [exact HagE | exists cr1; split; [exact HH1 | exact HC1]]]. intros b Hb.
      destruct (hio_wf L SCFG HI HIok _ _ _ _ HH1) as (Hwf & _). apply (Hwf b). unfold CH2.cur, CH2V.LBr. apply in_or_app. right. apply in_or_app. right. rewrite GBL. exact Hb. }
    assert (IMGC : forall g1 M0c i E (M2 : mem) m1, CH2V.okV L M LBo sp G.HDECL W M0c ->
                    CH2V.heap_ambV L HI GT.NF E1 model LBo sp G.HDECL W G.BLS ESBU.sghost gB CredV g1 M0c i E M2 m1 -> PML.img_ro M2).
    { intros g1 M0c i E M2 m1 (O1 & _) (_ & _ & _ & _ & Hfr & _) a Ha. rewrite (Hfr a (KIMG _ a Ha)). rewrite (O1 a (KIMG _ a Ha)). exact (Himg a Ha). }
    assert (OUTF : forall (F : list SGP.region) E' a, SP.F_sub F F0 = true -> env_agree GT.NF E1 E' -> 0 <= a < 2 ^ 64 -> ~ (sp - 8816 <= a < sp) -> SGP.outside E' F (Z_to_bv 64 a)).
    { intros F E' a HF Hag Ha N1. unfold SGP.outside. apply Forall_forall. intros [[rb rlo] rlen] Hin.
      pose proof (SP.F_sub_in _ _ _ HF Hin) as Hin0. rewrite L5.unsigned_lit by lia.
      unfold F0 in Hin0. cbn [In] in Hin0. destruct Hin0 as [X|[]]; injection X as <- <- <-.
      rewrite (PB.estart_agree GT.NF E1 E' (EVar 2) (-8816) Hag eq_refl). unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite U2. rewrite (u64_of_Z 8816) by lia. lia. }
    assert (SINKAG : forall g1 (M2 M' : mem), (forall b, In b (PML.srep_blocks (ESBU.s_rep g1)) -> block_range L (fst b) (snd b)) ->
                     (forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 8816 <= a < sp) -> ~ in_errno L a -> M' (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)) ->
                     ESBU.sink_inv M2 S2 g1 -> ESBU.sink_inv M' S2 g1).
    { intros g1 M2 M' HB HFR (HS & HL). split; [|exact HL].
      assert (AG : forall a k, 0 <= a -> a + k <= 2 ^ 64 -> (a + k <= sp - 8816 \/ sp <= a) -> (a + k <= hl_errno L \/ hl_errno L + 4 <= a) -> L5C.agree_on M2 M' a k).
      { intros a k H0 H1 H2 H3 q Hq. apply HFR; [lia | lia | unfold in_errno; lia]. }
      destruct SPR as (P1 & P2 & P3).
      apply (EK.sink_at_agree M2 M' S2 (ESBU.s_rep g1)); [lia | lia | apply AG; rewrite ?LER; unfold hl_ceil in *; lia | | exact HS].
      destruct (ESBU.s_rep g1) as [s|cap p s] eqn:Hrep; [exact I|].
      destruct (HB (p, cap) ltac:(left; reflexivity)) as (R0 & R1' & R2 & R3 & R4). cbn [fst snd] in *. rewrite ILO, IHI in R1'.
      split; [lia|]. split; [unfold hl_ceil in *; lia|]. apply AG; rewrite ?LER; unfold hl_ceil in *; lia. }
    assert (STRETCH : forall g1 M0c i cp kk ps t E R2 (M2 : mem) m1 E' R' (M' : mem), CH2.is_leaf G.CPS G.TAGS i cp kk ps t -> CC.At (hl_segs L) cp E R2 M2 ->
                        CH2V.okV L M LBo sp G.HDECL W M0c ->
                        CH2V.heap_ambV L HI GT.NF E1 model LBo sp G.HDECL W G.BLS ESBU.sghost gB CredV g1 M0c i E M2 m1 -> XIv g1 i E M2 ->
                        env_agree (CC.cp_nx cp) E E' -> CC.leaf_facts (hl_segs L) cp ps E' R' M2 M' ->
                        ESBU.sink_inv M' S2 g1 /\ env_agree GT.NF E1 E' /\ PML.img_ro M').
    { intros g1 M0c i cp kk ps t E R2 M2 m1 E' R' M' IL HAt OKV HA HX Hag HLF.
      pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. unfold leaf_chk in X. apply andb_prop in X as [XF _]. apply andb_prop in XF as [XF _].
      destruct IL as (tags & Hcp & _). destruct (BRG _ _ _ _ _ _ HA) as (HB & HagE & _). pose proof (AGE i cp E E' Hcp HagE Hag) as HagE'.
      destruct HX as (HX1 & HX2). pose proof (CC.lf_frame _ _ _ _ _ _ _ HLF) as FR.
      split; [|split; [exact HagE' |]].
      - apply (SINKAG g1 M2 M' HB); [|exact HX1]. intros a Ha N1 N2. apply FR. exact (OUTF (CC.cp_F cp) E' a XF HagE' Ha N1).
      - apply (EK.img_ro_agree M2 M'); [|exact (IMGC g1 M0c i E M2 m1 OKV HA)]. intros a Ha. unfold PML.IMG_RO_HI in Ha.
        apply FR. apply (OUTF (CC.cp_F cp) E' a XF HagE'); unfold hl_ceil in *; lia. }
    assert (UVK : forall (cp : CC.cutpoint) E E' v0, env_agree (CC.cp_nx cp) E E' -> (v0 < CC.cp_nx cp)%nat -> uv E' (EVar v0) = uv E (EVar v0)).
    { intros cp E E' v0 Hag Hv0. apply (PB.uv_agree (CC.cp_nx cp) E E' (EVar v0) Hag). cbn [APC.expr_vars_lt]. apply Nat.ltb_lt. exact Hv0. }
    assert (UF33 : forall E', env_agree GT.NF E1 E' -> uv E' (EVar 33) = c).
    { intros E' Hag. rewrite (PB.uv_agree GT.NF E1 E' (EVar 33) Hag) by (cbn [APC.expr_vars_lt]; apply Nat.ltb_lt; unfold GT.NF; lia). unfold PB.uv. cbn [edenot]. exact U33. }
    assert (UF2 : forall E', env_agree GT.NF E1 E' -> uv E' (EVar 2) = sp).
    { intros E' Hag. rewrite (PB.uv_agree GT.NF E1 E' (EVar 2) Hag) by (cbn [APC.expr_vars_lt]; apply Nat.ltb_lt; unfold GT.NF; lia). unfold PB.uv. cbn [edenot]. exact U2. }
    assert (HK' : forall cp ps E' R' (M2 M' : mem), CC.leaf_facts (hl_segs L) cp ps E' R' M2 M' -> know_ok RSEGS E' M' (SR.ps_cells ps)).
    { intros cp ps E' R' M2 M' HLF. rewrite <- LS. unfold know_ok. apply Forall_forall. exact (CC.lf_cells _ _ _ _ _ _ _ HLF). }
    (* [comment removed for export] *)
    assert (UVKK1 : forall E' (M' : mem) cells, know_ok RSEGS E' M' cells -> CC.has_cell cells (KRange KK1 0 19) = true ->
              1 <= uv E' (EVar 48) /\ uv E' KK1 = uv E' (EVar 48) - 1).
    { intros E' M' cells HK HC. pose proof (PB.has_ok E' M' _ _ HK HC) as X. cbn [kentry_ok] in X. fold (PB.uv E' KK1) in X.
      assert (E48 : uv E' KK1 = (uv E' (EVar 48) + (-1)) mod 2 ^ 64) by (unfold KK1; apply uv_add_lit').
      pose proof (PB.uv_range E' (EVar 48)) as R48.
      destruct (Z.eq_dec (uv E' (EVar 48)) 0) as [Z0|Z0].
      - exfalso. rewrite E48, Z0 in X. change ((0 + -1) mod 2 ^ 64) with 18446744073709551615 in X. lia.
      - rewrite E48. rewrite Z.mod_small by lia. lia. }
    assert (UVKC1 : forall E', env_agree GT.NF E1 E' -> uv E' KC1 = c - 1).
    { intros E' Hag. unfold KC1. rewrite uv_add_lit'. rewrite (UF33 E' Hag). apply Z.mod_small. lia. }
    unfold PML.cfg. rewrite <- LS. rewrite <- LS in HAt1.
    eapply (CH2V.cert_sound3V L HI HIok (PB.LYI_ L LAY) (PB.LYE_ L LAY) (PmLayout.ly_ro L LAY) GT.NF E1 M model LBo sp G.HDECL W G.BLS ESBU.sghost gB CredV XIv STKF SCRP NF32 U2 W_OK WRS_OK
              G.CPS K PML.fp_ok G.TAGS) with (i := 0%nat) (E := E1).
    - rewrite LS. exact FPM.
    - rewrite LS. exact G.plans.
    - exact G.tags_ok.
    - exact heap_ok3.
    - (* [comment removed for export] *) intros g1 i cp kk ps j sg IL E E' R' M2 M' cr1 _ _ _ HC. exact HC.
    - (* [comment removed for export] *)
      intros g1 M0c OKV i cp kk ps j sg IL E R2 E' R' M2 M' m1 HAt HA Hag HLF HX.
      destruct (STRETCH g1 M0c i cp kk ps _ E R2 M2 m1 E' R' M' IL HAt OKV HA HX Hag HLF) as (HINV & HagE' & _).
      pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. unfold leaf_chk in X. apply andb_prop in X as [XF X]. apply andb_prop in XF as [_ XN]. apply Nat.leb_le in XN.
      apply andb_prop in X as [Xk XG].
      destruct HX as (_ & HP). split; [exact HINV|].
      assert (O48 : uv (CC.env_over GT.NF sg E') (EVar 48) = uv E' (CC.slook sg 48)) by reflexivity.
      rewrite O48.
      assert (A48 : uv E' (EVar 48) = uv E (EVar 48)) by (apply (UVK cp E E' 48%nat Hag); lia).
      pose proof (HK' cp ps E' R' M2 M' HLF) as HKc.
      unfold goto_chk in XG. unfold phase in HP |- *. clear - HP Xk XG HKc A48 HagE' UVKK1 UVKC1 Hc.
      do 3 (destruct i as [|i]; [destruct kk as [|[|kk]]; cbn [kind] in Xk; try discriminate Xk;
        repeat (lazymatch type of XG with (match ?jj with _ => _ end = true) => destruct jj as [|jj] end); try discriminate XG;
        first [ (apply expr_eqb_eq in XG; rewrite XG, (UVKC1 E' HagE'); lia)
              | (apply andb_prop in XG as [XG XC]; apply expr_eqb_eq in XG; destruct (UVKK1 E' M' _ HKc XC) as [K1 K2]; rewrite XG, K2, A48; rewrite A48 in K1; lia) ] |]).
      destruct kk as [|[|kk]]; discriminate Xk.
    - (* [comment removed for export] *)
      intros i cp kk ps pc IL g1 M0c OKV.
      pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. unfold leaf_chk in X. apply andb_prop in X as [XF X]. apply andb_prop in XF as [XF XN].
      apply Nat.leb_le in XN.
      assert (XILEAF : forall E R2 (M2 : mem) m1 E' R' (M' : mem), CC.At (hl_segs L) cp E R2 M2 ->
                 CH2V.heap_ambV L HI GT.NF E1 model LBo sp G.HDECL W G.BLS ESBU.sghost gB CredV g1 M0c i E M2 m1 -> XIv g1 i E M2 -> env_agree (CC.cp_nx cp) E E' ->
                 CC.leaf_facts (hl_segs L) cp ps E' R' M2 M' -> ESBU.sink_inv M' S2 g1).
      { intros E R2 M2 m1 E' R' M' HAt HA HX Hag HLF. exact (proj1 (STRETCH g1 M0c i cp kk ps _ E R2 M2 m1 E' R' M' IL HAt OKV HA HX Hag HLF)). }
      set (j := ret_cut i kk) in *.
      assert (HRET : forall f, sinkj f i kk cp ps = true -> CH2.ret_of G.RETS i kk = Some j /\ exists cj, nth_error G.CPS j = Some cj /\ isSome (f cp ps cj (nth i G.BLS []) (nth j G.BLS [])) = true).
      { intros f Hs. unfold sinkj in Hs. apply andb_prop in Hs as [Hs1 Hs2]. fold j in Hs1, Hs2.
        split; [unfold j, ret_cut in *; destruct (CH2.ret_of G.RETS i kk) as [j0|]; [reflexivity | discriminate Hs1]|].
        destruct (nth_error G.CPS j) as [cj|]; [|discriminate]. exists cj. split; [reflexivity | exact Hs2]. }
      destruct (Z.eqb_spec pc PML.PC_STR_PUSH_BACK) as [->|Hne1].
      + (* [comment removed for export] *)
        apply andb_prop in X as [X Xi]. apply andb_prop in X as [X2 X3]. apply Z.eqb_eq in X2.
        destruct (HRET _ X3) as (Hret & cj & Hcj & X3b). clear X3.
        destruct (ESBU.pushb_chk GT.NF G.HDECL S2E 0 cp ps cj (nth i G.BLS []) (nth j G.BLS [])) as [ci|] eqn:Hchk; [|discriminate].
        assert (XILEAF' : forall E R2 (M2 : mem) m1 E' R' (M' : mem), CC.At (hl_segs L) cp E R2 M2 ->
                   CH2V.heap_ambV L HI GT.NF E1 model LBo sp G.HDECL W G.BLS ESBU.sghost gB CredV g1 M0c i E M2 m1 -> XIv g1 i E M2 -> env_agree (CC.cp_nx cp) E E' ->
                   CC.leaf_facts (hl_segs L) cp ps E' R' M2 M' -> ESBU.sink_inv M' S2 g1 /\ ESBU.s_len g1 + 1 <= CLU).
        { intros E R2 M2 m1 E' R' M' HAt HA HX Hag HLF. split; [exact (XILEAF E R2 M2 m1 E' R' M' HAt HA HX Hag HLF)|].
          destruct HX as (_ & HP). pose proof (PB.uv_range E (EVar 48)) as R48. clear - HP Xi R48 ROOM Hc.
          do 3 (destruct i as [|i]; [destruct kk as [|[|kk]]; cbn [kind] in Xi; first [discriminate Xi | (cbn [phase] in HP; lia)] |]). destruct kk as [|[|kk]]; discriminate Xi. }
        apply (ESBU.pushb_leaf_ok L HI HIok LAY GT.NF E1 M model LBo sp G.HDECL W G.BLS [] kx bx XIv STKF SCRP NF32 U2 TP0 W_OK CRS_OK WRS_OK IMG_OK G.CPS G.TAGS G.RETS K HKnil DEF0
                 S2 Hobj W_S2 S2E 0 eq_refl OADDR PUSHB_OK i cp kk ps j cj ci g1 M0c OKV IL Hret Hcj X2 Hchk XILEAF').
        intros E E' R' M2 M' E2 M3 g' HX HagE' Hag HLF Hag2 Hnx HINV2 G1.
        split; [exact HINV2|]. destruct HX as (_ & HP). rewrite G1.
        assert (A48 : uv E2 (EVar 48) = uv E (EVar 48)).
        { rewrite (UVK cp E' E2 48%nat (CC.env_agree_le _ _ _ _ Hag2 Hnx) ltac:(lia)). apply (UVK cp E E' 48%nat Hag). lia. }
        rewrite A48. subst j. unfold ret_cut. unfold phase in HP |- *. clear - HP Xi.
        do 3 (destruct i as [|i]; [destruct kk as [|[|kk]]; cbn [kind CH2.ret_of G.RETS find Nat.eqb andb] in *; first [discriminate Xi | lia] |]). destruct kk as [|[|kk]]; discriminate Xi.
      + (* [comment removed for export] *)
        apply andb_prop in X as [X Xi]. apply andb_prop in X as [X XI48]. apply andb_prop in X as [X XE]. apply andb_prop in X as [X1 XA0].
        intros fx' E R2 M2 m1 E' R' M' HAt [HAmb HX] HFP Hag HLF _.
        destruct (STRETCH g1 M0c i cp kk ps _ E R2 M2 m1 E' R' M' IL HAt OKV HAmb HX Hag HLF) as (HINV & HagE'0 & _).
        assert (DEFC : L5.defined M0c (sp - 8816) 8816) by (rewrite <- SCRV; exact (CH2V.okV_def0 L M LBo sp G.HDECL W M0c OKV)).
        apply (PB.exit_ret L HI HIok LAY GT.NF E1 M0c model (CH2V.LBr LBo ESBU.sghost gB g1) sp G.HDECL W G.BLS (CredV g1) STKF SCRP NF32 U2 W_OK WRS_OK G.CPS G.TAGS K (XIv g1)
                 (CH2V.okV_def0 L M LBo sp G.HDECL W M0c OKV) (fun _ => 0) (fun _ => 0)
                 8816 ltac:(rewrite SCRV; lia) ltac:(unfold hl_ceil; lia) DEFC R EV1 r Hra Hraok heap_ok3 RETPC i cp kk ps pc ret_at IL X1 fx' E R2 M2 m1 E' R' M' HAt HAmb Hag HLF).
        intros HRP HPR HA' HagE'. destruct HA' as (Hmo1 & Hbv1 & HagE1 & (cr1 & HH1 & HC1) & _ & _).
        destruct HX as (_ & HPH).
        assert (HP2 : L5C.hpres L LBo sp 8816 W M M').
        { rewrite <- SCRV. apply (CH2V.hpres_rebase L GT.NF M LBo sp G.HDECL W ESBU.sghost gB NF32 g1 M0c M' OKV). rewrite SCRV. exact HPR. }
        (* [comment removed for export] *)
        pose proof (HK' cp ps E' R' M2 M' HLF) as HKc.
        pose proof (PB.has_ok E' M' _ _ HKc XE) as KX. unfold KEXIT in KX. cbn [kentry_ok] in KX.
        assert (K0 : uv E (EVar 48) = 0).
        { rewrite <- (UVK cp E E' 48%nat Hag) by lia. cbn [edenot] in KX. rewrite u_sltu64 in KX.
          rewrite !u_add64, !u_lit64 in KX. unfold two64 in KX.
          assert (E2' : bv_unsigned (ev E' 2) = sp) by (destruct HagE'0 as [AG _]; rewrite <- (AG 2%nat) by (unfold GT.NF; lia); exact U2).
          rewrite E2' in KX.
          pose proof (PB.has_ok E' M' _ _ HKc XI48) as K19. cbn [kentry_ok edenot] in K19.
          unfold PB.uv. cbn [edenot]. set (k0 := bv_unsigned (ev E' 48)) in *.
          destruct (Z.ltb_spec (((sp + k0) mod 2 ^ 64 + -296 mod 2 ^ 64) mod 2 ^ 64) ((sp + -295 mod 2 ^ 64) mod 2 ^ 64)) as [LT|GE]; [|lia].
          change (-296 mod 2 ^ 64) with 18446744073709551320 in LT. change (-295 mod 2 ^ 64) with 18446744073709551321 in LT.
          destruct (Z_lt_le_dec k0 1) as [S|S]; [lia|]. exfalso.
          rewrite (Z.mod_small (sp + k0)) in LT by (unfold hl_ceil in *; lia).
          replace ((sp + k0 + 18446744073709551320) mod 2 ^ 64) with (sp + k0 - 296) in LT.
          2:{ apply (Z.mod_unique _ _ 1); unfold hl_ceil in *; lia. }
          replace ((sp + 18446744073709551321) mod 2 ^ 64) with (sp - 295) in LT.
          2:{ apply (Z.mod_unique _ _ 1); unfold hl_ceil in *; lia. }
          lia. }
        set (pay := ESBU.s_len g1 - len0).
        assert (HPAY : pay = match i with 5%nat => c + 1 | _ => c end /\ 1 <= pay <= 20).
        { unfold phase in HPH. rewrite K0 in HPH. subst pay. clear - HPH Xi Hc. do 3 (destruct i as [|i]; [destruct kk as [|[|kk]]; cbn [kind] in Xi; first [discriminate Xi | lia] |]). destruct kk as [|[|kk]]; discriminate Xi. }
        destruct HPAY as [HPv HPr].
        assert (Ga0 : PML.a0 R' pay).
        { unfold exit_a0 in XA0. unfold PML.a0. rewrite HPv. clear HPv HPr.
          do 3 (destruct i as [|i]; [ first [ discriminate XA0
            | (pose proof (CL.ps_reg_is_sound (hl_segs L) cp ps E' R' M2 M' 10 _ HLF XA0) as G10;
               replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) in G10 by (apply bv_eq; reflexivity); rewrite G10;
               apply PB.edenot_of_uv; first [ exact (UF33 E' HagE'0) | (rewrite uv_add_lit', (UF33 E' HagE'0); apply Z.mod_small; lia) ]) ] |]).
          destruct kk; discriminate Xi. }
        apply (Hcont fx' R' M' m1 (LBo ++ PML.srep_blocks (ESBU.s_rep g1)) cr1 LBo W HFP); [| exact HRP | exact HP2 | exact Hbv1 |].
        -- exists (ESBU.s_rep g1), pay. destruct HINV as [Hs Hl].
           split; [exact HPr|]. split; [exact Ga0|]. split; [exact Hs|]. split; [unfold pay, len0 in *; lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. exact HC1.
        -- unfold CH2.cur, CH2V.LBr in HH1. rewrite GBL in HH1.
           assert (Hnil : CH2.den E (nth i G.BLS []) = []) by (clear - Xi; do 3 (destruct i as [|i]; [reflexivity|]); destruct kk as [|[|kk]]; discriminate Xi).
           rewrite Hnil in HH1. exact HH1.
    - reflexivity.
    - exact HAt1.
    - (* [comment removed for export] *)
      apply (CH2V.amb3V_intro L HI GT.NF E1 M model LBo sp G.HDECL W G.BLS ESBU.sghost gB CredV XIv (ESBU.SG rep len0) M 0%nat E1 M1 model
               (CH2V.okV_refl L M LBo sp G.HDECL W DEF0)).
      split.
      + apply (CH2.amb_pure_step L HI HIok (PB.LYI_ L LAY) (PB.LYE_ L LAY) (PmLayout.ly_ro L LAY) GT.NF E1 M model (CH2V.LBr LBo ESBU.sghost gB (ESBU.SG rep len0)) sp G.HDECL W G.BLS
                 (CredV (ESBU.SG rep len0)) STKF SCRP NF32 W_OK 0%nat 0%nat E1 E1 M M1 model).
        * split; [exact Hmo|]. split; [apply L5C.model_but_vm_refl|]. split; [apply CC.env_agree_refl|].
          split; [|split; [intros a _; reflexivity | intros a _ _ Hd; exact Hd]].
          exists cr. split; [|exact Hcred].
          unfold CH2.cur, CH2V.LBr. rewrite (GBL (ESBU.SG rep len0)). cbn [ESBU.s_rep nth G.BLS GT.BL0 CH2.den map app]. exact HH.
        * intros a Hfs. apply FR1. intros Hin. apply Hfs. left. rewrite SCRV. exact Hin.
        * exact GR1.
        * apply CC.env_agree_refl.
        * reflexivity.
        * intros cr1 HC. exact HC.
      + split; [|unfold phase; cbn [ESBU.s_len]; lia].
        split; [|reflexivity]. cbn [ESBU.s_rep].
        apply (EK.sink_at_agree M M1 S2 rep); [lia | lia | intros q Hq; apply FRZ1; unfold hl_ceil in *; lia | | exact Hsink].
        destruct rep as [s|cap p s] eqn:Hrep; [exact I|].
        destruct (HBLK (p, cap) ltac:(apply in_or_app; right; left; reflexivity)) as (R0 & R1' & R2 & R3 & R4). cbn [fst snd] in R0, R1', R2, R3, R4. rewrite ILO, IHI in R1'.
        split; [lia|]. split; [unfold hl_ceil in *; lia|]. intros q Hq. apply FRZ1; unfold hl_ceil in *; lia.
    - exact Hfp1. }
  (* [comment removed for export] *)
  assert (UG : forall (c : Z) (R' : bvmap 5 word), 0 <= c < 2 ^ 64 ->
            let E1 := DTXHU.EX (Env (reg_ev R (fun v0 => Z_to_bv 64 (nth (v0 - 32) [S2; c] 0))) (fun _ => [])) R' in
            (forall x : reg, ev E1 (ridx x) = getr R x) /\
            bv_unsigned (ev E1 2) = sp /\ bv_unsigned (ev E1 10) = v /\ bv_unsigned (ev E1 11) = SK /\ bv_unsigned (ev E1 32) = S2 /\ bv_unsigned (ev E1 33) = c /\
            ev E1 32 = Z_to_bv 64 S2 /\ ev E1 33 = Z_to_bv 64 c).
  { intros c R' Hc E1.
    assert (EV1 : forall x : reg, ev E1 (ridx x) = getr R x) by (intros x; unfold E1; rewrite DTXHU.EX_lo by (pose proof (ridx_range x); lia); apply CL5.ev_reg).
    split; [exact EV1|].
    split; [rewrite (EV1 2%bv : ev E1 2 = _), Hsp; apply u64_of_Z; lia|].
    split; [rewrite (EV1 10%bv : ev E1 10 = _); unfold PML.a0 in Ha0; rewrite Ha0; apply u64_of_Z; lia|].
    split; [rewrite (EV1 11%bv : ev E1 11 = _); unfold PML.a1 in Ha1; rewrite Ha1; apply u64_of_Z; lia|].
    split; [cbn [ev DTXHU.EX nth Nat.ltb Nat.leb Nat.sub reg_ev]; apply u64_of_Z; lia|].
    split; [cbn [ev DTXHU.EX nth Nat.ltb Nat.leb Nat.sub reg_ev]; apply u64_of_Z; lia|].
    split; reflexivity. }
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  destruct Hmo as (Hh & Hl & Hmat).
  unfold PML.a0, PML.a1 in Ha0, Ha1.
  unfold PML.cfg. eapply TWBX.cj_evt_srz; [exact Hh | exact Hl | |].
  { unfold canon_regs. rewrite Hsp. rewrite Ha0, Ha1.
    eapply (fiu_entry (getr R 1) (getr R 3) (getr R 4) (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22)
                    (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) _ _ sp SK M).
    - unfold hl_ceil in *. lia.
    - lia.
    - lia.
    - apply TWBX.stk_of_defined; [replace (sp - (sp - 8816)) with 8816 by lia; exact S5 | unfold hl_ceil in *; lia | lia].
    - apply TWBX.mem_inv_of_clear. intros a Ha. apply Himg. unfold PML.IMG_RO_HI. lia.
    - reflexivity. }
  assert (FSPv : FiWalkX_u5.FSP sp = sp - 320) by reflexivity.
  Ltac reg_case RG Ha0 Ha1 :=
    first [ reflexivity
          | (rewrite <- RG; reflexivity)
          | (rewrite <- RG; etransitivity; [|symmetry; first [exact Ha1 | exact Ha0]]; reflexivity) ].
  intros ms1 ms1' HP EQV.
  destruct HP as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & cnt & jl & bsb & -> & Hcnt & HM).
  destruct HM as (FR0 & BB & BBL & FRS & ST & MU & WM & MI).
  destruct (ms_eqv_MS_inv _ _ _ _ _ _ _ EQV) as [Ems REQ]. rewrite Ems. set (R' := ms_regs ms1') in *.
  pose proof (fun x => getr_eqv _ _ x REQ) as RG. cbv beta in RG.
  lazymatch goal with |- srealizes _ _ (mkCfg (MS _ ?F' (Z_to_bv 64 ?pcv) ?fc' None _ _) _) _ =>
    change (mkCfg (MS R' F' (Z_to_bv 64 pcv) fc' None m' (seg_rom rsegs)) model) with (@PML.cfg (mkFP F' fc') R' (CC.cp_pc G.cp0) m' model) end.
  assert (DALL : L5.defined m' (sp - 8816) 8816).
  { pose proof (TWBX.stk_defined _ _ _ ST ltac:(unfold hl_ceil in *; lia) ltac:(rewrite FSPv; lia)) as DST. rewrite FSPv in DST.
    pose proof (TWBX.rw_defined _ _ _ FR0 ltac:(rewrite FSPv; unfold hl_ceil in *; lia)) as D0. rewrite FSPv in D0. cbn [cells_size csize Nat.add] in D0. change (Z.of_nat 25) with 25 in D0.
    pose proof (TWBX.u8arr_defined _ _ _ BB ltac:(unfold FiWalkX_u5.BUF; rewrite FSPv; unfold hl_ceil in *; lia)) as DB. rewrite BBL in DB. unfold FiWalkX_u5.BUF in DB. rewrite FSPv in DB.
    change (Z.of_nat 255) with 255 in DB.
    pose proof (TWBX.rw_defined _ _ _ FRS ltac:(rewrite FSPv; unfold hl_ceil in *; lia)) as DS. rewrite FSPv in DS. cbn [cells_size csize Nat.add] in DS. change (Z.of_nat 40) with 40 in DS.
    intros q Hq.
    destruct (Z_lt_le_dec q 8496); [apply DST; lia|].
    destruct (Z_lt_le_dec q 8521); [replace (sp - 8816 + q) with (sp - 320 + (q - 8496)) by lia; apply D0; lia|].
    destruct (Z_lt_le_dec q 8776); [replace (sp - 8816 + q) with (sp - 320 + 25 + (q - 8521)) by lia; apply DB; lia|].
    replace (sp - 8816 + q) with (sp - 320 + 280 + (q - 8776)) by lia. apply DS. lia. }
  assert (FRw : forall x : word, ~ (sp - 8816 <= bv_unsigned x < sp) -> m' x = M x) by (intros x Hx; apply MU; apply DTXHU.outside1; exact Hx).
  destruct (UG cnt R' ltac:(lia)) as (EV1 & U2 & U10 & U11 & U32 & U33 & V32 & V33).
  set (E1 := DTXHU.EX _ R') in EV1, U2, U10, U11, U32, U33, V32, V33.
  assert (HskS2' : PML.u64 m' SK S2).
  { apply (EK.u64_agree M m' SK S2); [| lia | lia | exact HskS2]. intros q Hq. apply FRw. rewrite u64_of_Z by lia. lia. }
  assert (GSP : getr R' (Z_to_bv 5 (Z.of_nat 2)) = edenot E1 SPE).
  { rewrite (PB.edenot_of_uv E1 _ (sp - 320)).
    - rewrite <- (RG (Z_to_bv 5 (Z.of_nat 2))). rewrite <- FSPv. reflexivity.
    - change (PB.uv E1 SPE = sp - 320). unfold SPE. rewrite uv_add_lit'. unfold PB.uv. cbn [edenot]. rewrite U2.
      rewrite Z.mod_small by (unfold hl_ceil in *; lia). lia. }
  apply (MAIN cnt _ R' m' ltac:(lia)); [| exact Hfp | exact FRw | exact DALL].
  fold E1. unfold CC.At. rewrite regs0, know0. split.
  - apply DTXHU.regs_ok_of. intros nn Hn.
    assert (Hn' : (nn = 1 \/ nn = 2 \/ nn = 3 \/ nn = 4 \/ nn = 5 \/ nn = 6 \/ nn = 7 \/ nn = 8 \/ nn = 9 \/ nn = 10 \/ nn = 11 \/ nn = 12 \/ nn = 13 \/ nn = 14 \/ nn = 15 \/ nn = 16
             \/ nn = 17 \/ nn = 18 \/ nn = 19 \/ nn = 20 \/ nn = 21 \/ nn = 22 \/ nn = 23 \/ nn = 24 \/ nn = 25 \/ nn = 26 \/ nn = 27 \/ nn = 28 \/ nn = 29 \/ nn = 30 \/ nn = 31)%nat) by lia.
    repeat destruct Hn' as [->|Hn']; try subst nn; cbn [nth REGS0];
      first [ exact GSP | reg_case RG Ha0 Ha1 | (cbn [edenot]; unfold E1; cbn [ev DTXHU.EX Nat.ltb Nat.leb nth DTXHU.CSV Nat.sub]; reflexivity)
            | (rewrite <- RG; cbn [edenot]; exact (eq_sym V33)) ].
  - unfold know_ok, KNOW0.
    repeat (apply Forall_cons); [.. | apply Forall_nil].
    + eapply CL5.kword64_intro with (A := SK) (z := S2); [ev_start | lia | lia | exact V32 | exact HskS2'].
    + e_range. + e_range.
    + e_align OS3.
    + e_range.
    + e_wr. + e_range. + e_align S1.
    + e_disj. + e_disj. + e_disj.
    + eapply (TWBX.kw8_of_cell E1 m' _ _ 32%nat); [exact FRS | reflexivity | unfold estart; cbn [a_base a_off edenot]; rewrite U2, FSPv; lia | rewrite FSPv; unfold hl_ceil in *; lia | rewrite FSPv; lia | exact (EV1 1%bv)].
    + eapply (TWBX.kw8_of_cell E1 m' _ _ 24%nat); [exact FRS | reflexivity | unfold estart; cbn [a_base a_off edenot]; rewrite U2, FSPv; lia | rewrite FSPv; unfold hl_ceil in *; lia | rewrite FSPv; lia | exact (EV1 8%bv)].
    + eapply (TWBX.kw8_of_cell E1 m' _ _ 16%nat); [exact FRS | reflexivity | unfold estart; cbn [a_base a_off edenot]; rewrite U2, FSPv; lia | rewrite FSPv; unfold hl_ceil in *; lia | rewrite FSPv; lia | exact (EV1 9%bv)].
    + eapply (TWBX.kw8_of_cell E1 m' _ _ 8%nat); [exact FRS | reflexivity | unfold estart; cbn [a_base a_off edenot]; rewrite U2, FSPv; lia | rewrite FSPv; unfold hl_ceil in *; lia | rewrite FSPv; lia | exact (EV1 18%bv)].
    + eapply (TWBX.kw8_of_cell E1 m' _ _ 0%nat); [exact FRS | reflexivity | unfold estart; cbn [a_base a_off edenot]; rewrite U2, FSPv; lia | rewrite FSPv; unfold hl_ceil in *; lia | rewrite FSPv; lia | exact (EV1 19%bv)].
    + e_unk. + e_unk. + e_unk.
Qed.
End FromIntOk.
End FIUU.
