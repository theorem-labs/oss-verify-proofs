(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core StreamSim. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5 PmEncSpecs2_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX CutHeap2V.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5 ParseBridges2_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require Import SmallPure.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmGrow Require Import GrowKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncSums_u5 EncKit_u5 EncKit2_u5 EncKit3_u5 EncSinkBridgesU EncSinkBridges2U EncTail2_u5 EncAppendK_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Cut_vbegin_tail_object_xsrc_T_u5 Cut_vbegin_tail_object_xsrc_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module EVBTOU.
Import PMES.
Module G := Cut_vbegin_tail_object_xsrc_u5.
Module GT := Cut_vbegin_tail_object_xsrc_T_u5.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Definition uv := PB.uv.
Definition RETPC : Z := 0x3c688.
Definition S2E : expr := EVar 32.
Definition F0 : list SGP.region := [(EVar 2, -8496, ELit 8496); (EVar 8, 272, ELit 8); (EVar 8, 288, ELit 4); (EVar 8, 296, ELit 8)].
Definition KEPT : list nat := [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.

Lemma heap_ok3 : CH2.heap_chk3 GT.NF G.HDECL G.BLS G.CPS G.TAGS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.

Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.
Definition sink_j (f : CC.cutpoint -> SR.post_spec -> CC.cutpoint -> CA.blocks -> CA.blocks -> option CH2.cinfo) (i k j : nat) (c : CC.cutpoint) (ps : SR.post_spec) : bool :=
  (match CH2.ret_of G.RETS i k with Some j' => Nat.eqb j' j | None => false end &&
   match nth_error G.CPS j with Some cj => isSome (f c ps cj (nth i G.BLS []) (nth j G.BLS [])) | None => false end)%bool.
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  let cells := SR.ps_cells ps in let regs := CA.ps_reglist ps in
  (SP.F_sub (CC.cp_F c) F0 && Nat.leb GT.NF (CC.cp_nx c) && CH2.blocks_eqb (nth i G.BLS []) [] &&
   CC.has_cell cells (KWord (SA (EVar 8) 288) 4 (EAlu ALU_ADD (EMd M_MUL (ELit 4) (EVar 33)) (ELit 4))) &&
   CC.has_cell cells (KWord (SA (EVar 8) 272) 8 (EVar 10)))%bool &&
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      if Z.eqb pc PML.PC_STR_APPEND then
        (Nat.eqb i 0 && Z.eqb (SR.ps_pc ps) PML.PC_STR_APPEND && sink_j (ESBU.sink_chk GT.NF G.HDECL S2E 0) i k 1 c ps &&
         expr_eqb (nth 11 regs (ELit 0)) (ELit TXT_OBRACE) && expr_eqb (nth 12 regs (ELit 0)) (ELit 1))%bool
      else
        (Nat.eqb i 1 && Z.eqb (SR.ps_pc ps) RETPC && CL.ps_keeps ps KEPT && CL.ps_reg_is ps 1 (EVar 40) &&
         CL.ps_reg_is ps 2 (EAlu ALU_ADD (EVar 2) (ELit 64)) && CL.ps_reg_is ps 10 (ELit 1) && CL.ps_reg_is ps 8 (EVar 41) &&
         CL.ps_reg_is ps 9 (EVar 42) && CL.ps_reg_is ps 18 (EVar 43))%bool
  end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true.
Proof. vm_compute. reflexivity. Qed.

Lemma kept_lt48 : forall y : reg, In (ridx y) KEPT -> (ridx y < 48)%nat.
Proof. intros y Hy. unfold KEPT in Hy. cbn [In] in Hy. intuition lia. Qed.
Lemma kept_in : forall r : reg, In (bv_unsigned r) [3; 19; 20; 21; 22; 23; 24; 25; 26; 27] -> In (ridx r) KEPT.
Proof. intros r H. unfold ridx, KEPT. cbn [In] in H. repeat (destruct H as [H|H]; [rewrite <- H; cbn; tauto|]). destruct H. Qed.
Lemma reg_of_leaf : forall segs c ps E' R' (M1 M' : mem) (x : bv 5) n e,
  CC.leaf_facts segs c ps E' R' M1 M' -> CL.ps_reg_is ps n e = true -> bv_unsigned x = Z.of_nat n -> getr R' x = edenot E' e.
Proof.
  intros segs c ps E' R' M1 M' x n e HLF Hchk Hx. pose proof (CL.ps_reg_is_sound segs c ps E' R' M1 M' n e HLF Hchk) as G0.
  replace x with (Z_to_bv 5 (Z.of_nat n)); [exact G0|]. apply bv_eq. rewrite Z_to_bv_unsigned, Hx. pose proof (bv_unsigned_in_range 5 x) as RG.
  unfold bv_wrap. rewrite Z.mod_small; [reflexivity|]. rewrite <- Hx. exact RG.
Qed.

Lemma objx_parts : forall (M : mem) V S2 dI dD, PMES2.enc_objx M V S2 dI dD ->
  PML.u32 M (V + O_INDENT) (4 * dI) /\ L5.defined M (V + O_COLUMN) 8 /\ PML.u32 M (V + O_DEPTH) dD.
Proof.
  intros M V S2 dI dD H. unfold PMES2.enc_objx in H.
  destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H1 & H2 & H3 & _).
  split; [exact H1|]. split; [exact H2 | exact H3].
Qed.

Lemma stack_mid_agree : forall (M M' : mem) V es c0 b capb, 0 <= b -> b + capb <= 2 ^ 64 -> 0 <= V -> V + ENC_SIZE <= 2 ^ 64 ->
  L5C.agree_on M M' (V + O_STACK) 8 -> L5C.agree_on M M' (V + O_STACK + 16) 8 -> L5C.agree_on M M' b capb ->
  PMES2.stack_mid M V es c0 b capb -> PMES2.stack_mid M' V es c0 b capb.
Proof.
  intros M M' V es c0 b capb HB HB2 HV HV2 A1 A2 AB (S1 & S3 & S4 & S5 & S6 & SC). unfold PMES2.stack_mid, ENC_SIZE, O_STACK in *.
  assert (D0 : 0 <= depth es) by (unfold depth; lia).
  split; [apply (EK.u64_agree M M'); [exact A1 | lia | lia | exact S1]|].
  split; [apply (EK.u64_agree M M'); [exact A2 | lia | lia | exact S3]|].
  split; [exact S4|]. split; [exact S5|]. split.
  - intros i Hi. specialize (S6 i Hi). assert (Hd : Z.of_nat i < depth es) by (unfold depth; lia).
    apply (EK.ctx_at_agree M M' (b + 32 * Z.of_nat i)); [lia | lia | apply (EK.agree_sub M M' _ _ _ _ AB); lia | exact S6].
  - apply (EK.ctx_at_agree M M' (b + 32 * depth es)); [lia | lia | apply (EK.agree_sub M M' _ _ _ _ AB); lia | exact SC].
Qed.

Section Tail.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis APPEND_OK : str_append_x_specU L HI.

Theorem tail_ok : PMES2.tail_spec L HI PMES2.BK_OBJECT.
Proof.
  intros LBo cr sp V S2 b capb kx bx r s0v s1v s2v s3v es rep. unfold PMES2.cps_seg.
  intros fx R M model K HH Hmo HKnil Hfp Hpre Hcont.
  change (PMES2.bk_arr PMES2.BK_OBJECT) with false in Hpre, Hcont.
  destruct Hpre as (Hsp & Htp & Hstk & Hsp16 & Hv8 & Hv10 & Hfr & Hraok & Hdfr & Hd272 & Hobj & Hmid & HD & Hsink & Hcred & Hroom & Hro & OV & OS & OAP).
  assert (D0 : 0 <= depth es) by (unfold depth; lia).
  unfold MAX_DEPTH in HD.
  pose proof (PmLayout.ly_segs L LAY) as LS. pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI.
  pose proof (PmLayout.ly_errno L LAY) as LER.
  destruct Hstk as (S1 & S2' & S3 & S4 & S5).
  unfold PMES2.TAIL_SCR, STRX_SCR, PMS.STR_SCR, PMS.OPNEW_SCR, PML.HEAP_STACK in S2', S5.
  unfold PMES2.FRAME in Hdfr. unfold PML.obj_on_stack, PMES2.FRAME, ENC_SIZE in OV, OS. unfold PML.apart, ENC_SIZE in OAP.
  destruct OV as (OV1 & OV2 & OV3). destruct OS as (OS1 & OS2 & OS3).
  destruct Hfr as (F56 & F48 & F40 & F32 & _).
  pose proof Hmid as (MS1 & MS3 & MS4 & (kq & Hkq & Hcap)
 & MS5 & MS6).
  pose proof Hobj as (H1 & H2 & H3 & (fl & H4 & H4') & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & (en & H18 & H18') & H19 & H20 & H21 & H22 & (dp & H23) & H24 & H25 & H26 & (H27 & H27') & (H28 & H28') & (H29 & H29') & (H30 & H30') & (H31 & H31') & (H32 & H32')).
  destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hwf & _).
  assert (INB : In (b, capb) (LBo ++ PML.srep_blocks rep ++ [(b, capb)])) by (apply in_or_app; right; apply in_or_app; right; left; reflexivity).
  destruct (Hwf _ INB) as ((B1 & B2 & B3 & B4 & B5) & _). cbn [fst snd] in B1, B2, B3, B4, B5. rewrite ILO, IHI in B2.
  destruct (EAK.u64_of_defined M (V + O_COLUMN) H25) as (col & Hcol0 & Hcol).
  set (E0 := Env (reg_ev R (fun v => Z_to_bv 64 (nth (v - 32) [S2; depth es; col; 0; 0; 0; 0; 0; r; s0v; s1v; s2v; s3v] 0))) (fun _ => [])).
  assert (EV : forall x : reg, ev E0 (ridx x) = getr R x) by (intros x; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 PML.TP) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V8 : ev E0 8 = Z_to_bv 64 V) by (rewrite <- Hv8; exact (EV 8%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 (b + 32 * (depth es + 1))) by (rewrite <- Hv10; exact (EV 10%bv)).
  assert (V32 : ev E0 32 = Z_to_bv 64 S2) by reflexivity.
  assert (V33 : ev E0 33 = Z_to_bv 64 (depth es)) by reflexivity.
  assert (V34 : ev E0 34 = Z_to_bv 64 col) by reflexivity.
  assert (V40 : ev E0 40 = Z_to_bv 64 r) by reflexivity.
  assert (V41 : ev E0 41 = Z_to_bv 64 s0v) by reflexivity.
  assert (V42 : ev E0 42 = Z_to_bv 64 s1v) by reflexivity.
  assert (V43 : ev E0 43 = Z_to_bv 64 s2v) by reflexivity.
  assert (V44 : ev E0 44 = Z_to_bv 64 s3v) by reflexivity.
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; lia).
  assert (U8 : bv_unsigned (ev E0 8) = V) by (rewrite V8; apply u64_of_Z; lia).
  assert (U10 : bv_unsigned (ev E0 10) = b + 32 * (depth es + 1)) by (rewrite V10; apply u64_of_Z; lia).
  assert (U32 : bv_unsigned (ev E0 32) = S2) by (rewrite V32; apply u64_of_Z; lia).
  assert (U33 : bv_unsigned (ev E0 33) = depth es) by (rewrite V33; apply u64_of_Z; lia).
  assert (U34 : bv_unsigned (ev E0 34) = col) by (rewrite V34; apply u64_of_Z; lia).
  assert (SCRV : CH.hd_scr G.HDECL = 8496) by reflexivity.
  assert (STKC : hl_ceil L + CH.hd_scr G.HDECL <= sp) by (rewrite SCRV; lia).
  pose proof (conj Hsp16 (conj STKC (conj S3 S4))) as STKF.
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (rewrite SCRV; lia).
  assert (NF32 : (32 <= GT.NF)%nat) by (unfold GT.NF; lia).
  assert (TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite V4, (PmLayout.ly_tp L LAY); reflexivity).
  set (W := PMES2.W_tail V S2).
  assert (W_OK : forall (w : L5.range) (a : Z), In w W -> L5.in_rng w a -> CH2.wclient L sp a).
  { intros w a [<-|[<-|[]]] Hin; unfold L5.in_rng, O_STACK in Hin; cbn [fst snd] in Hin; (split; [lia | left; lia]). }
  assert (CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> CH2.sclient L LBo sp a)).
  { intros rg [<-|[<-|[<-|[]]]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CH2.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot] in Ha.
    - rewrite U8 in Ha. rewrite u64_of_Z in Ha by lia. split; [lia | left; lia].
    - rewrite U8 in Ha. rewrite u64_of_Z in Ha by lia. split; [lia | left; lia].
    - rewrite U2 in Ha. rewrite u64_of_Z in Ha by lia. split; [lia | left; lia]. }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> exists w : L5.range, In w W /\ L5.in_rng w a)).
  { intros rg [<-|[<-|[]]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CH2.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot] in Ha.
    - rewrite U8 in Ha. rewrite u64_of_Z in Ha by lia. exists (V + O_STACK, 40). split; [left; reflexivity | unfold L5.in_rng, O_STACK; cbn [fst snd]; lia].
    - rewrite U32 in Ha. rewrite u64_of_Z in Ha by lia. exists (S2, 24). split; [right; left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia]. }
  assert (IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img G.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_alloc_static L a /\ ~ in_errno L a).
  { intros rg a [<-|[]] Ha. cbn [fst snd] in Ha. rewrite ILO, IHI. split; [lia|]. split.
    - intros Hs. apply (PmLayout.ly_static L LAY) in Hs. lia.
    - unfold in_errno. rewrite LER. lia. }
  assert (DEF0 : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)).
  { rewrite SCRV. intros j Hj. replace (sp - 8496 + j) with (sp - (256 + (16 + 8224)) + j) by lia. apply S5. lia. }
  assert (W_S2 : In (S2, 24) W) by (right; left; reflexivity).
  assert (OADDR : estart E0 (SA S2E 0) = S2) by (unfold estart, S2E; cbn [a_base a_off edenot]; rewrite U32; lia).
  assert (S2OBJ : PML.obj_on_stack L sp S2 24) by (unfold PML.obj_on_stack; repeat split; lia).
  set (GR := [(b, capb)]).
  set (gB := ESBU.gB GR).
  set (CredV := ESBU.CredV L kx bx).
  set (OBJK := fun (M1 : mem) => PML.img_ro M1 /\ (exists dI, PMES2.enc_objx M1 V S2 dI (depth es + 1)) /\ PMES2.stack_mid M1 V es (ECtx false 0 false) b capb).
  set (XIv := fun (g1 : ESBU.sghost) (i : nat) (E : env) (M1 : mem) =>
                (ESBU.sink_inv M1 S2 g1 /\ OBJK M1) /\ ESBU.s_len g1 = len (PML.srep_chars rep) + match i with 0%nat => 0 | _ => 1 end).
  assert (AGE : forall i c E E', nth_error G.CPS i = Some c -> env_agree GT.NF E0 E -> env_agree (CC.cp_nx c) E E' -> env_agree GT.NF E0 E').
  { intros i c E E' Hc HA1 HA2. eapply CC.env_agree_trans; [exact HA1 | eapply CC.env_agree_le; [exact HA2 | exact (G.NF_le i c Hc)]]. }
  assert (NILB : forall i E, CH2.den E (nth i G.BLS []) = []).
  { intros i E. destruct i as [|[|i]]; try reflexivity. destruct i; reflexivity. }
  assert (BRG : forall g1 M0c i E (M1 : mem) m1, CH2V.heap_ambV L HI GT.NF E0 model LBo sp G.HDECL W G.BLS ESBU.sghost gB CredV g1 M0c i E M1 m1 ->
                  (forall b0, In b0 (PML.srep_blocks (ESBU.s_rep g1)) -> block_range L (fst b0) (snd b0)) /\ env_agree GT.NF E0 E).
  { intros g1 M0c i E M1 m1 (_ & _ & HagE & (cr1 & HH1 & _) & _). unfold CH2.cur, CH2V.LBr in HH1. rewrite NILB in HH1. cbn [app] in HH1.
    split; [|exact HagE]. intros b0 Hb.
    destruct (hio_wf L SCFG HI HIok _ _ _ _ HH1) as (Hwf1 & _). apply (Hwf1 b0). apply in_or_app. right. unfold gB, ESBU.gB. apply in_or_app. left. exact Hb. }
  assert (OUTF : forall (F : list SGP.region) E' a, SP.F_sub F F0 = true -> env_agree GT.NF E0 E' -> 0 <= a < 2 ^ 64 ->
                   ~ (sp - 8496 <= a < sp) -> ~ (V + 272 <= a < V + 280) -> ~ (V + 288 <= a < V + 292) -> ~ (V + 296 <= a < V + 304) ->
                   SGP.outside E' F (Z_to_bv 64 a)).
  { intros F E' a HF Hag Ha N1 N2 N3 N4. unfold SGP.outside. apply Forall_forall. intros [[rb rlo] rlen] Hin.
    pose proof (SP.F_sub_in _ _ _ HF Hin) as Hin0. rewrite L5.unsigned_lit by lia.
    unfold F0 in Hin0. cbn [In] in Hin0. destruct Hin0 as [X|[X|[X|[X|[]]]]]; injection X as <- <- <-.
    - rewrite (PB.estart_agree GT.NF E0 E' (EVar 2) (-8496) Hag eq_refl). unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite U2. rewrite (u64_of_Z 8496) by lia. lia.
    - rewrite (PB.estart_agree GT.NF E0 E' (EVar 8) 272 Hag eq_refl). unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite U8. rewrite (u64_of_Z 8) by lia. lia.
    - rewrite (PB.estart_agree GT.NF E0 E' (EVar 8) 288 Hag eq_refl). unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite U8. rewrite (u64_of_Z 4) by lia. lia.
    - rewrite (PB.estart_agree GT.NF E0 E' (EVar 8) 296 Hag eq_refl). unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite U8. rewrite (u64_of_Z 8) by lia. lia. }
  assert (INVS : forall (F : list SGP.region) E' (M1 M' : mem) (g : ESBU.sghost), SP.F_sub F F0 = true -> env_agree GT.NF E0 E' ->
                   (forall a : word, SGP.outside E' F a -> M' a = M1 a) -> mem_grows M1 M' ->
                   (forall b0, In b0 (PML.srep_blocks (ESBU.s_rep g)) -> block_range L (fst b0) (snd b0)) ->
                   PML.u32 M' (V + O_INDENT) (4 * (depth es + 1)) ->
                   ESBU.sink_inv M1 S2 g /\ OBJK M1 -> ESBU.sink_inv M' S2 g /\ OBJK M').
  { intros F E' M1 M' g HF Hag HFR HG HBR Q288 [(HS & HL) (HR & (dI & HE) & HM)].
    assert (AG : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= sp - 8496 \/ sp <= a) -> (a + n <= V + 272 \/ V + 280 <= a) ->
                   (a + n <= V + 288 \/ V + 292 <= a) -> (a + n <= V + 296 \/ V + 304 <= a) -> L5C.agree_on M1 M' a n).
    { intros a n Q0 Q1 Q2 Q3 Q4 Q5 i Hi. apply HFR. apply (OUTF F E' i HF Hag); lia. }
    destruct (objx_parts M1 V S2 dI (depth es + 1) HE) as (HI1 & HC1 & HD1).
    split.
    - split; [|exact HL]. apply (EK.sink_at_agree M1 M' S2 (ESBU.s_rep g)); [lia | lia | apply AG; lia | | exact HS].
      destruct (ESBU.s_rep g) as [s|cap p s] eqn:Hrep; [exact I|].
      destruct (HBR (p, cap) ltac:(left; reflexivity)) as (R0 & R1 & R2 & R3 & R4). cbn [fst snd] in *.
      split; [lia|]. split; [lia|]. apply AG; lia.
    - split; [|split].
      + apply (EK.img_ro_agree M1 M'); [|exact HR]. intros a Ha. unfold PML.IMG_RO_HI in Ha. apply HFR. apply (OUTF F E' a HF Hag); lia.
      + exists (depth es + 1). apply (EK3.enc_objx_agree_d M1 M' V S2 dI (depth es + 1) (depth es + 1) (depth es + 1));
          [lia | unfold ENC_SIZE; lia | apply AG; unfold O_STACK; lia | apply AG; unfold O_COLON, O_DEPTH; lia | | exact Q288 | | exact HE].
        * intros j Hj. apply HG. apply HC1. exact Hj.
        * apply (EK.u32_agree M1 M'); [apply AG; unfold O_DEPTH; lia | unfold O_DEPTH; lia | unfold O_DEPTH; lia | exact HD1].
      + apply (stack_mid_agree M1 M' V es (ECtx false 0 false) b capb); [lia | lia | lia | unfold ENC_SIZE; lia | apply AG; unfold O_STACK; lia | apply AG; unfold O_STACK; lia | apply AG; lia | exact HM]. }
  assert (STRETCH : forall g1 M0c i c k ps t E R1 (M1 : mem) m1 E' R' (M' : mem), CH2.is_leaf G.CPS G.TAGS i c k ps t -> CC.At (hl_segs L) c E R1 M1 ->
                      CH2V.heap_ambV L HI GT.NF E0 model LBo sp G.HDECL W G.BLS ESBU.sghost gB CredV g1 M0c i E M1 m1 -> XIv g1 i E M1 ->
                      env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M1 M' ->
                      (ESBU.sink_inv M' S2 g1 /\ OBJK M') /\ env_agree GT.NF E0 E' /\
                      PML.u32 M' (V + O_INDENT) (4 * (depth es + 1)) /\ PML.u64 M' (V + O_STACK + 8) (b + 32 * (depth es + 1))).
  { intros g1 M0c i c k ps t E R1 M1 m1 E' R' M' IL HAt HA HX Hag HLF.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. unfold leaf_chk in X.
    apply andb_prop in X as [XC _]. apply andb_prop in XC as [XC X272]. apply andb_prop in XC as [XC X288].
    apply andb_prop in XC as [XC _]. apply andb_prop in XC as [XF _].
    destruct IL as (tags & Hc & _). destruct (BRG _ _ _ _ _ _ HA) as (HB & HagE). pose proof (AGE i c E E' Hc HagE Hag) as HagE'.
    assert (HK : know_ok RSEGS E' M' (SR.ps_cells ps)) by (rewrite <- LS; unfold know_ok; apply Forall_forall; exact (CC.lf_cells _ _ _ _ _ _ _ HLF)).
    assert (F8 : bv_unsigned (edenot E' (EVar 8)) = V) by (fold (PB.uv E' (EVar 8)); rewrite (PB.uv_agree GT.NF E0 E' (EVar 8) HagE' eq_refl); exact U8).
    assert (F10 : bv_unsigned (edenot E' (EVar 10)) = b + 32 * (depth es + 1)) by (fold (PB.uv E' (EVar 10)); rewrite (PB.uv_agree GT.NF E0 E' (EVar 10) HagE' eq_refl); exact U10).
    assert (F33 : bv_unsigned (edenot E' (EVar 33)) = depth es) by (fold (PB.uv E' (EVar 33)); rewrite (PB.uv_agree GT.NF E0 E' (EVar 33) HagE' eq_refl); exact U33).
    assert (Q288 : PML.u32 M' (V + O_INDENT) (4 * (depth es + 1))).
    { pose proof (PB2.kword32_elim E' M' _ _ (V + O_INDENT) (PB.has_ok E' M' _ _ HK X288)) as Y.
      assert (ES : estart E' (SA (EVar 8) 288) = V + O_INDENT) by (unfold estart, O_INDENT; cbn [a_base a_off]; rewrite F8; reflexivity).
      specialize (Y ES).
      assert (UV : PB.uv E' (EAlu ALU_ADD (EMd M_MUL (ELit 4) (EVar 33)) (ELit 4)) = 4 * (depth es + 1)).
      { cbn [edenot] in F33. apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia]. }
      rewrite UV in Y. exact Y. }
    assert (Q272 : PML.u64 M' (V + O_STACK + 8) (b + 32 * (depth es + 1))).
    { apply (CL5.kword64_elim RSEGS E' M' _ _ (V + O_STACK + 8) _ (PB.has_ok E' M' _ _ HK X272)); [unfold estart, O_STACK; cbn [a_base a_off]; rewrite F8; lia | exact F10]. }
    split; [|split; [exact HagE' | split; [exact Q288 | exact Q272]]].
    destruct HX as ((HS & HO) & _).
    exact (INVS (CC.cp_F c) E' M1 M' g1 XF HagE' (CC.lf_frame _ _ _ _ _ _ _ HLF) (CC.lf_grows _ _ _ _ _ _ _ HLF) HB Q288 (conj HS HO)). }
  assert (OBJK_RET : forall LBk spc scr (M1 M2 : mem), In (b, capb) LBk -> L5C.hpres L LBk spc scr [(S2, 24)] M1 M2 ->
                       L5C.stk (hl_sptop L) M2 spc scr -> 0 <= scr -> spc <= sp -> OBJK M1 -> OBJK M2).
  { intros LBk spc scr M1 M2 HIN HP HSTK Hscr Hspc (HR & (dI & HE) & HM).
    assert (KV : forall a, V <= a < V + 408 -> L5C.kept L LBk spc scr [(S2, 24)] a).
    { intros a Ha. apply (L5C.kept_stack_stk L LBk M2 spc scr); [exact HSTK | exact Hscr | lia | rewrite LER; lia |].
      intros w [<-|[]]. unfold L5.in_rng. cbn [fst snd]. lia. }
    assert (AV : forall a n0, V <= a -> a + n0 <= V + 408 -> L5C.agree_on M1 M2 a n0).
    { intros a n0 Q1 Q2 i Hi. apply (L5C.hpres_kept _ _ _ _ _ _ _ i HP). apply KV. lia. }
    assert (AB : L5C.agree_on M1 M2 b capb).
    { intros i Hi. apply (L5C.hpres_kept _ _ _ _ _ _ _ i HP). apply (L5C.kept_block L LBk spc scr _ b capb i HIN); [lia | lia | lia | rewrite LER; lia |].
      intros w [<-|[]]. unfold L5.in_rng. cbn [fst snd]. lia. }
    destruct (objx_parts M1 V S2 dI (depth es + 1) HE) as (HI1 & HC1 & HD1).
    split; [|split].
    - apply (EK.img_ro_agree M1 M2); [|exact HR]. intros a Ha. unfold PML.IMG_RO_HI in Ha. apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP).
      apply L5C.kept_static; [rewrite ILO, IHI; lia | intros Hs; apply (PmLayout.ly_static L LAY) in Hs; lia | rewrite ILO; lia | rewrite IHI; lia | rewrite LER; lia |].
      intros w [<-|[]]. unfold L5.in_rng. cbn [fst snd]. lia.
    - exists dI. apply (EK3.enc_objx_agree_d M1 M2 V S2 dI (depth es + 1) dI (depth es + 1));
        [lia | unfold ENC_SIZE; lia | apply AV; unfold O_STACK; lia | apply AV; unfold O_COLON, O_DEPTH; lia | | | | exact HE].
      + apply (L5C.defined_agree M1 M2 (V + O_COLUMN) 8); [apply AV; unfold O_COLUMN; lia | exact HC1].
      + apply (EK.u32_agree M1 M2); [apply AV; unfold O_INDENT; lia | unfold O_INDENT; lia | unfold O_INDENT; lia | exact HI1].
      + apply (EK.u32_agree M1 M2); [apply AV; unfold O_DEPTH; lia | unfold O_DEPTH; lia | unfold O_DEPTH; lia | exact HD1].
    - apply (stack_mid_agree M1 M2 V es (ECtx false 0 false) b capb); [lia | lia | lia | unfold ENC_SIZE; lia | apply AV; unfold O_STACK; lia | apply AV; unfold O_STACK; lia | exact AB | exact HM]. }
  unfold PML.cfg. change (PMES2.bk_tail PMES2.BK_OBJECT) with (CC.cp_pc G.cp0). rewrite <- LS.
  eapply (CH2V.cert_sound3V L HI HIok (PB.LYI_ L LAY) (PB.LYE_ L LAY) (PmLayout.ly_ro L LAY) GT.NF E0 M model LBo sp G.HDECL W G.BLS ESBU.sghost gB CredV XIv STKF SCRP NF32 U2 W_OK WRS_OK
            G.CPS K PML.fp_ok G.TAGS) with (i := 0%nat) (E := E0).
  - rewrite LS. exact FPM.
  - rewrite LS. exact G.plans.
  - exact G.tags_ok.
  - exact heap_ok3.
  - intros g1 i c kk ps j sg IL. exfalso. pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. unfold leaf_chk in X.
    apply andb_prop in X as [_ X]. discriminate X.
  - intros g1 M0c _ i c kk ps j sg IL. exfalso. pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. unfold leaf_chk in X.
    apply andb_prop in X as [_ X]. discriminate X.
  - intros i c kk ps pc IL g1 M0c OKV.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. unfold leaf_chk in X.
    apply andb_prop in X as [XC X]. apply andb_prop in XC as [XC X272]. apply andb_prop in XC as [XC X288].
    apply andb_prop in XC as [XC XB]. apply andb_prop in XC as [XF XN].
    destruct (Z.eqb pc PML.PC_STR_APPEND) eqn:E1.
    + apply Z.eqb_eq in E1. subst pc.
      apply andb_prop in X as [X X5]. apply andb_prop in X as [X X4]. apply andb_prop in X as [X X3]. apply andb_prop in X as [X1 X2].
      apply Nat.eqb_eq in X1. subst i. apply Z.eqb_eq in X2.
      unfold sink_j in X3. apply andb_prop in X3 as [X3a X3b].
      destruct (CH2.ret_of G.RETS 0 kk) as [j|] eqn:Hret; [|discriminate]. apply Nat.eqb_eq in X3a. subst j.
      destruct (nth_error G.CPS 1) as [cj|] eqn:Hcj; [|discriminate].
      destruct (ESBU.sink_chk GT.NF G.HDECL S2E 0 c ps cj (nth 0 G.BLS []) (nth 1 G.BLS [])) as [ci|] eqn:Hchk; [|discriminate].
      apply expr_eqb_eq in X4. apply expr_eqb_eq in X5.
      assert (XILEAF : forall E R1 (M1 : mem) m1 E' R' (M' : mem), CC.At (hl_segs L) c E R1 M1 ->
                 CH2V.heap_ambV L HI GT.NF E0 model LBo sp G.HDECL W G.BLS ESBU.sghost gB CredV g1 M0c 0%nat E M1 m1 -> XIv g1 0%nat E M1 ->
                 env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M1 M' -> ESBU.sink_inv M' S2 g1 /\ ESBU.s_len g1 + 1 <= CLU).
      { intros E R1 M1 m1 E' R' M' HAt HA HX Hag HLF.
        destruct (STRETCH g1 M0c 0%nat c kk ps _ E R1 M1 m1 E' R' M' IL HAt HA HX Hag HLF) as [[HS _] _].
        split; [exact HS|]. destruct HX as (_ & HL0). cbv iota in HL0. lia. }
      apply (ESB2U.append_leaf_ok2 L HI HIok LAY GT.NF E0 M model LBo sp G.HDECL W G.BLS GR kx bx XIv STKF SCRP NF32 U2 TP0 W_OK CRS_OK WRS_OK IMG_OK G.CPS G.TAGS G.RETS K HKnil DEF0
               S2 S2OBJ W_S2 S2E 0 eq_refl OADDR APPEND_OK 1 0%nat c kk ps 1%nat cj ci g1 M0c OKV IL Hret Hcj X2 Hchk XILEAF).
      * intros E R1 M1 m1 E' R' M' cr1 HAt HA HX Hag HLF CF HINV HH1.
        pose proof CF as [HA' HR Hreq HVR HKn HRA HSP Hstk' Htp' HagE' Hden Hmeas].
        destruct (STRETCH g1 M0c 0%nat c kk ps _ E R1 M1 m1 E' R' M' IL HAt HA HX Hag HLF) as [[_ (HRO & _)] _].
        assert (Ga1 : getr R' 11%bv = Z_to_bv 64 TXT_OBRACE).
        { rewrite (HR 11%bv). unfold sr_get. change (bv_eqb (11%bv : bv 5) 0) with false. cbv iota. change (ridx 11%bv) with 11%nat. rewrite Hreq. rewrite X4. reflexivity. }
        assert (Ga2 : getr R' 12%bv = Z_to_bv 64 1).
        { rewrite (HR 12%bv). unfold sr_get. change (bv_eqb (12%bv : bv 5) 0) with false. cbv iota. change (ridx 12%bv) with 12%nat. rewrite Hreq. rewrite X5. reflexivity. }
        exists TXT_OBRACE, [123].
        split; [exact Ga1|]. split; [exact Ga2|]. split; [reflexivity|].
        split; [apply (EK.lit_bytes M' TXT_OBRACE [123] HRO); [unfold TXT_OBRACE; lia | change (len [123]) with 1; unfold TXT_OBRACE, PML.IMG_RO_HI; lia | exact EK.txt_obrace]|].
        split; [right; left; split; [unfold TXT_OBRACE; lia | split; [change (len [123]) with 1; unfold TXT_OBRACE, PML.IMG_RO_HI; lia | exact HRO]]|].
        destruct HINV as (_ & HLN). destruct HX as (_ & HL0). cbv iota in HL0. rewrite HLN, HL0. change (len [123]) with 1. unfold CLU in Hroom. lia.
      * intros E R1 M1 m1 E' R' M' E2 M2 g' HAt HA HX HagE0' Hag HLF CF HP Hag2 Hnx HINV2 G1.
        destruct (STRETCH g1 M0c 0%nat c kk ps _ E R1 M1 m1 E' R' M' IL HAt HA HX Hag HLF) as [[_ HO] _].
        pose proof CF as [_ _ _ _ _ _ (Hsp' & Hc1 & Hs0 & Hc2) Hstk' _ _ _ _].
        assert (HSTK2 : L5C.stk (hl_sptop L) M2 (sp + CH2.ci_csp ci) ESBU.STR_SCR).
        { destruct Hstk' as (Q1 & Q2 & Q3 & Q4 & _). split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. exact (L5C.hpres_defined _ _ _ _ _ _ _ HP). }
        assert (HIN : In (b, capb) (CH2.den E' (nth 0 G.BLS []) ++ LBo ++ GR)) by (apply in_or_app; right; apply in_or_app; right; left; reflexivity).
        split; [split; [exact HINV2 | exact (OBJK_RET _ _ _ M' M2 HIN HP HSTK2 Hs0 ltac:(lia) HO)]|].
        destruct HX as (_ & HL0). cbv iota in HL0 |- *. rewrite G1, HL0. lia.
    + apply andb_prop in X as [X X18]. apply andb_prop in X as [X X9]. apply andb_prop in X as [X X8].
      apply andb_prop in X as [X X10]. apply andb_prop in X as [X X2r]. apply andb_prop in X as [X X1r]. apply andb_prop in X as [X XK].
      apply andb_prop in X as [X1 X2]. apply Nat.eqb_eq in X1. subst i. apply Z.eqb_eq in X2.
      intros fx' E R1 M1 m1 E' R' M' HAt [HAmb HX] HFP Hag HLF _.
      destruct (STRETCH g1 M0c 1%nat c kk ps _ E R1 M1 m1 E' R' M' IL HAt HAmb HX Hag HLF) as [[HINV HO] (HagE' & Q288 & Q272)].
      assert (REG : forall (x : bv 5) n e, CL.ps_reg_is ps n e = true -> bv_unsigned x = Z.of_nat n -> getr R' x = edenot E' e).
      { intros x n e Hc' Hx. exact (reg_of_leaf _ c ps E' R' M1 M' x n e HLF Hc' Hx). }
      assert (KEEP : forall y : reg, In (ridx y) KEPT -> getr R' y = getr R y).
      { intros y Hy. rewrite (CL.ps_keeps_sound (hl_segs L) c ps E0 E' R' M1 M' KEPT GT.NF y HLF XK HagE' Hy (kept_lt48 y Hy)). exact (EV y). }
      assert (AGV : forall n, (n < 48)%nat -> ev E' n = ev E0 n).
      { intros n Hn. destruct HagE' as [AG _]. symmetry. apply AG. unfold GT.NF. exact Hn. }
      assert (F2 : bv_unsigned (ev E' 2) = sp) by (rewrite AGV by lia; exact U2).
      assert (Gr : getr R' 1%bv = Z_to_bv 64 r) by (rewrite (REG 1%bv 1%nat _ X1r eq_refl); cbn [edenot]; rewrite AGV by lia; exact V40).
      assert (DEFC : L5.defined M0c (sp - 8496) 8496) by (rewrite <- SCRV; exact (CH2V.okV_def0 L M LBo sp G.HDECL W M0c OKV)).
      apply (ETL2.exit_ret2 L HI HIok LAY GT.NF E0 M0c model (CH2V.LBr LBo ESBU.sghost gB g1) sp G.HDECL W G.BLS (CredV g1) STKF SCRP NF32 U2 W_OK WRS_OK G.CPS G.TAGS K
               (CH2V.okV_def0 L M LBo sp G.HDECL W M0c OKV) 8496 ltac:(rewrite SCRV; lia) ltac:(lia) DEFC heap_ok3 RETPC 1%nat c kk ps pc r ret_at IL XN X2 Hraok
               fx' E R1 M1 m1 E' R' M' HAt HAmb Hag HLF Gr).
      intros HP HA' HagE1.
      destruct HA' as (Hmo1 & Hbv1 & HagEE & (cr1 & HH1 & HC1) & _ & _).
      assert (HP2 : L5C.hpres L LBo sp 8496 W M M').
      { rewrite <- SCRV. apply (CH2V.hpres_rebase L GT.NF M LBo sp G.HDECL W ESBU.sghost gB NF32 g1 M0c M' OKV). rewrite SCRV. exact HP. }
      destruct HINV as (Hsink2 & Hlen2). destruct HX as (_ & HL1). cbv iota in HL1.
      destruct HO as (_ & (dI & HE) & HM).
      destruct (objx_parts M' V S2 dI (depth es + 1) HE) as (_ & HC' & HD').
      pose proof HM as (HM1 & HM3 & _).
      apply (Hcont fx' R' M' m1 (LBo ++ gB g1) cr1 LBo W HFP); [| exact HP2 | exact Hbv1 |].
      * exists (ESBU.s_rep g1).
        split.
        { rewrite (REG 2%bv 2%nat _ X2r eq_refl). rewrite <- (Z_to_bv_bv_unsigned _ (edenot E' _)). f_equal. unfold PMES2.FRAME.
          apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia]. }
        split; [rewrite (KEEP 4%bv ltac:(cbn; tauto)); exact Htp|].
        split; [unfold PML.a0; rewrite (REG 10%bv 10%nat _ X10 eq_refl); reflexivity|].
        split; [intros y Hy; apply KEEP; apply kept_in; exact Hy|].
        split; [rewrite (REG 8%bv 8%nat _ X8 eq_refl); cbn [edenot]; rewrite AGV by lia; exact V41|].
        split; [rewrite (REG 9%bv 9%nat _ X9 eq_refl); cbn [edenot]; rewrite AGV by lia; exact V42|].
        split; [rewrite (REG 18%bv 18%nat _ X18 eq_refl); cbn [edenot]; rewrite AGV by lia; exact V43|].
        split; [intros Hf; discriminate Hf|].
        split.
        { unfold enc_inv. cbn [g_es g_len g_rep g_sb g_scap]. rewrite EK2.depth_cons.
          split; [|split; [|split; [|split]]].
          - rewrite PMES2.enc_objx_eq. apply (EK3.enc_objx_agree_d M' M' V S2 dI (depth es + 1) (depth es + 1) (depth es + 1));
              [lia | unfold ENC_SIZE; lia | intros j _; reflexivity | intros j _; reflexivity | exact HC' | exact Q288 | exact HD' | exact HE].
          - apply (EK3.stack_mid_cons M' M' V es (ECtx false 0 false) b capb); [lia | lia | exact HM1 | exact Q272 | exact HM3 | intros j _; reflexivity | exact HM].
          - exact Hsink2.
          - rewrite Hlen2, HL1. reflexivity.
          - unfold MAX_DEPTH. lia. }
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. exact HC1.
      * unfold CH2.cur, CH2V.LBr in HH1. rewrite NILB in HH1. exact HH1.
  - reflexivity.
  - rewrite LS.
    assert (Hds : L5.defined M (sp - 8496) 8496) by (rewrite <- SCRV; exact DEF0).
    assert (W288 : edenot E0 (APC.escale 4 (EVar 33)) = Z_to_bv 64 (4 * depth es)).
    { apply PB.edenot_of_uv. rewrite PB.uv_escale. unfold PB.uv. cbn [edenot]. rewrite U33. apply Z.mod_small. lia. }
    assert (D288 : L5.defined M (V + 288) 4) by (apply (EK3.defined_of_u32 M (V + 288) (4 * depth es) H24); lia).
    assert (D296 : L5.defined M (V + 296) 8) by exact H25.
    assert (D272 : L5.defined M (V + 272) 8) by (unfold O_STACK in Hd272; replace (V + 272) with (V + 264 + 8) by lia; exact Hd272).
    pose proof Hro as Hro'. unfold PML.img_ro, L5.img_clear in Hro'.
    split; [exact (regs_ok_id R _ _)|]. unfold know_ok, G.cp0. cbn [CC.cp_know].
    repeat (apply Forall_cons); [.. | apply Forall_nil].
    + eapply CL5.kword64_intro with (A := V + 8) (z := S2); [ev_start | lia | lia | exact V32 | exact H2].
    + eapply PB2.kword8_intro with (A := V + 36) (z := 4); [ev_start | lia | lia | reflexivity | lia | exact H11].
    + eapply PB.kword32_intro with (A := V + 288) (z := 4 * depth es); [ev_start | lia | lia | exact W288 | exact H24].
    + e_range.
    + e_wr.
    + e_wr.
    + eapply CL5.kword64_intro with (A := V + 296) (z := col); [ev_start | lia | lia | exact V34 | exact Hcol].
    + e_range.
    + e_wr.
    + eapply CL5.kword64_intro with (A := V + 336) (z := TXT_OBRACE); [ev_start | lia | lia | reflexivity | exact H29].
    + eapply CL5.kword64_intro with (A := V + 344) (z := 1); [ev_start | lia | lia | reflexivity | replace (V + 344) with (V + O_OBRACE + 8) by (unfold O_OBRACE; lia); exact H29'].
    + eapply CL5.kword64_intro with (A := sp + 56) (z := r); [ev_start | lia | lia | exact V40 | exact F56].
    + eapply CL5.kword64_intro with (A := sp + 48) (z := s0v); [ev_start | lia | lia | exact V41 | exact F48].
    + eapply CL5.kword64_intro with (A := sp + 40) (z := s1v); [ev_start | lia | lia | exact V42 | exact F40].
    + eapply CL5.kword64_intro with (A := sp + 32) (z := s2v); [ev_start | lia | lia | exact V43 | exact F32].

    + e_range. + e_align OV3.
    + e_range. + e_align OS3.
    + e_range.
    + eapply CL5.kalign_intro; [lin_eval; rw_atoms; reflexivity | lia | lia |].
      apply Z.mod_divide; [lia|]. apply Z.mod_divide in B3; [|lia]. destruct B3 as [q Hq]. exists (2 * q + 4 * (depth es + 1)). lia.

    + e_unk. + e_wr. + e_unk.
    + e_range. + e_align Hsp16.
    + e_disj. + e_disj. + e_disj.
    + cbn [kentry_ok]. split; [lia|]. split; [lia|]. intros j Hj. apply Hro'. unfold PML.IMG_RO_HI. lia.
  - apply (CH2V.amb3V_intro L HI GT.NF E0 M model LBo sp G.HDECL W G.BLS ESBU.sghost gB CredV XIv (ESBU.SG rep (len (PML.srep_chars rep))) M 0%nat E0 M model
             (CH2V.okV_refl L M LBo sp G.HDECL W DEF0)).
    split.
    + split; [exact Hmo|]. split; [apply L5C.model_but_vm_refl|]. split; [apply CC.env_agree_refl|].
      split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
      exists cr. split; [unfold CH2.cur, CH2V.LBr; rewrite NILB; exact HH|]. exact Hcred.
    + split; [split; [split; [exact Hsink | reflexivity] |] | cbv iota; cbn [ESBU.s_len]; lia].
      split; [exact Hro|]. split; [exists (depth es); exact Hobj | exact Hmid].
  - exact Hfp.
Qed.
End Tail.
End EVBTOU.
