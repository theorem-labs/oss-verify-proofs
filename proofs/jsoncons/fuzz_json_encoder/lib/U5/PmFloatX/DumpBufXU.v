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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX CutHeap2V.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5 ParseBridges2_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require Import SmallPure.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncSums_u5 EncKit_u5 EncSinkBridges_u5 EncTail_u5 EncSinkBridgesU.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Cut_db_xsrc_T_u5 Cut_db_xsrc_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module DBXU.
Import PMES.
Module G := Cut_db_xsrc_u5.
Module GT := Cut_db_xsrc_T_u5.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Definition uv := PB.uv.
Definition RETPC : Z := 0x441c0.
Definition S2E : expr := EVar 32.
Definition F0W (w : Z) : list SGP.region := [(EVar 2, -w, ELit w)].
Definition F0 : list SGP.region := F0W 8608.
Definition SCRT : Z := 8608.      (* [comment removed for export] *)

Lemma heap_ok3 : CH2.heap_chk3 GT.NF G.HDECL G.BLS G.CPS G.TAGS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.

Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.
(* [comment removed for export] *)
Definition sink_j (f : CC.cutpoint -> SR.post_spec -> CC.cutpoint -> CA.blocks -> CA.blocks -> option CH2.cinfo) (i k j : nat) (c : CC.cutpoint) (ps : SR.post_spec) : bool :=
  (match CH2.ret_of G.RETS i k with Some j' => Nat.eqb j' j | None => false end &&
   match nth_error G.CPS j with Some cj => isSome (f c ps cj (nth i G.BLS []) (nth j G.BLS [])) | None => false end)%bool.
(* [comment removed for export] *)
Definition ret_cut (i k : nat) : nat := match i, k with 2%nat, _ => 9%nat | 1%nat, 1%nat => 3%nat | 1%nat, 2%nat => 4%nat | 1%nat, 3%nat => 5%nat | 1%nat, 6%nat => 6%nat | 1%nat, 9%nat => 7%nat | 1%nat, _ => 8%nat | _, _ => 10%nat end.
(* [comment removed for export] *)
Definition is_tail (i : nat) : bool := match i with 6%nat | 8%nat | 10%nat => true | _ => false end.
Definition is_after_push (i : nat) : bool := match i with 3%nat | 4%nat | 5%nat | 7%nat | 9%nat => true | _ => false end.

Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  let cells := SR.ps_cells ps in
  (SP.F_sub (CC.cp_F c) F0 && (Nat.leb 50 (CC.cp_nx c) || Nat.eqb i 0)) &&
  match t with
  | CC.TGoto j s =>
      match i, j with
      | 0%nat, 1%nat => expr_eqb (CC.slook s 48) (EVar 11) && expr_eqb (CC.slook s 49) (ELit 1)
      | 1%nat, 1%nat => expr_eqb (CC.slook s 48) (EAlu Instr.ALU_ADD (EVar 48) (ELit (-1))) && expr_eqb (CC.slook s 49) (EVar 49) &&
                                      PB.prove (CC.cp_know c) (KRange (EVar 48) 1 99)
      | 1%nat, 2%nat => expr_eqb (CC.slook s 48) (EVar 48) && (expr_eqb (CC.slook s 49) (EVar 49) || expr_eqb (CC.slook s 49) (ELit 0))
      | _, 1%nat => is_after_push i && expr_eqb (CC.slook s 48) (EAlu Instr.ALU_ADD (EVar 48) (ELit (-1))) && PB.prove (CC.cp_know c) (KRange (EVar 48) 1 99)
      | _, _ => false
      end
  | CC.TOther pc =>
      if Z.eqb pc PML.PC_STR_PUSH_BACK then
        if is_tail i then
          (Z.eqb (SR.ps_pc ps) PML.PC_STR_PUSH_BACK && ETL.tail_base_chk GT.NF c ps && CL.ps_reg_is ps 10 (EVar 32) && CL.ps_reg_is ps 11 (ELit 48))%bool
        else
          (Z.eqb (SR.ps_pc ps) PML.PC_STR_PUSH_BACK && sink_j (ESBU.pushb_chk GT.NF G.HDECL S2E 0) i k (ret_cut i k) c ps &&
           match i with 1%nat | 2%nat => true | 9%nat => PB.prove cells (KRange (EVar 48) 1 99) | _ => false end)%bool
      else
        (PB.exit_base_chk GT.NF RETPC c ps && PB.prove cells (KRange (EVar 48) 1 99) &&
         match i with
         | 1%nat => PB.prove cells (KRange (EVar 49) 0 0)
         | _ => is_after_push i end)%bool
  end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition phase (n : Z) (i : nat) (E : env) (p : Z) : Prop :=
  match i with
  | 0%nat => p = 0
  | 1%nat => 0 <= p <= n - uv E (EVar 48) /\ (uv E (EVar 49) = 1 \/ 1 <= p)
  | 2%nat => 0 <= p <= n - uv E (EVar 48)
  | 3%nat | 4%nat | 5%nat | 7%nat | 9%nat => 1 <= p <= n + 1 - uv E (EVar 48)
  | 6%nat | 8%nat | 10%nat => 1 <= p <= n + 1
  | _ => False
  end.

Lemma after_push_phase : forall n i E p, is_after_push i = true -> phase n i E p -> 1 <= p <= n + 1 - uv E (EVar 48).
Proof. intros n i E p A H. destruct i as [|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]; try discriminate A; exact H. Qed.

Lemma uv_add_lit : forall E e z, uv E (EAlu Instr.ALU_ADD e (ELit z)) = (uv E e + z) mod 2 ^ 64.
Proof.
  intros. pose proof (PB.uv_eaddz E e z) as H. unfold APC.eaddz, PB.uv in H. rewrite AX2S.mkAlu_denot in H. unfold uv, PB.uv. cbn [edenot] in H |- *. exact H.
Qed.
Lemma uv_lit1 : forall E z, 0 <= z < 2 ^ 64 -> uv E (ELit z) = z.
Proof. intros. unfold uv, PB.uv. cbn [edenot]. apply u64_of_Z; lia. Qed.

Section DumpBufOk.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis PUSHB_OK : str_push_back_x_specU L HI.

(* [comment removed for export] *)
Section Stretch.
Variables (E0 : env) (sp S2 : Z).
Variable WIN : Z.
Hypothesis U2 : bv_unsigned (ev E0 2) = sp.
Hypothesis WIN0 : 0 <= WIN.
Hypothesis SPR : hl_ceil L + WIN <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47.
Hypothesis S2OBJ : PML.obj_on_stack L sp S2 24.

Lemma out_F0 : forall (F : list SGP.region) E' a, SP.F_sub F (F0W WIN) = true -> env_agree GT.NF E0 E' -> 0 <= a < 2 ^ 64 ->
  ~ (sp - WIN <= a < sp) -> SGP.outside E' F (Z_to_bv 64 a).
Proof.
  intros F E' a HF Hag Ha N1. unfold SGP.outside. apply Forall_forall. intros [[rb rlo] rlen] Hin.
  pose proof (SP.F_sub_in _ _ _ HF Hin) as Hin0. rewrite L5.unsigned_lit by lia.
  destruct SPR as (P1 & P2 & P3).
  unfold F0W in Hin0. cbn [In] in Hin0. destruct Hin0 as [X|[]]; injection X as <- <- <-.
  rewrite (PB.estart_agree GT.NF E0 E' (EVar 2) (-WIN) Hag eq_refl). unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite U2. rewrite (u64_of_Z WIN) by lia. lia.
Qed.

Lemma sink_stretch : forall (F : list SGP.region) E' (M M' : mem) g, SP.F_sub F (F0W WIN) = true -> env_agree GT.NF E0 E' ->
  (forall a : word, SGP.outside E' F a -> M' a = M a) ->
  (forall b, In b (PML.srep_blocks (ESBU.s_rep g)) -> block_range L (fst b) (snd b)) ->
  ESBU.sink_inv M S2 g -> ESBU.sink_inv M' S2 g.
Proof.
  intros F E' M M' g HF Hag HFR HB (HS & HL).
  destruct S2OBJ as (O1 & O2 & O3). destruct SPR as (P1 & P2 & P3).
  assert (AG : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= sp - WIN \/ sp <= a) -> L5C.agree_on M M' a n).
  { intros a n H0 H1 H2 i Hi. apply HFR. apply (out_F0 F E' i HF Hag); lia. }
  split; [|exact HL].
  apply (EK.sink_at_agree M M' S2 (ESBU.s_rep g)); [lia | lia | apply AG; lia | | exact HS].
  destruct (ESBU.s_rep g) as [s|cap p s] eqn:Hrep; [exact I|].
  destruct (HB (p, cap) ltac:(left; reflexivity)) as (R0 & R1 & R2 & R3 & R4). cbn [fst snd] in *.
  split; [lia|]. split; [lia|]. apply AG; unfold hl_ceil in *; lia.
Qed.
End Stretch.

Theorem dump_buffer_x_ok : PMFXT.dump_buffer_x_specU L HI.
Proof.
  intros buf n dp bs LBo cr sp r SK S2 kx bx rep. unfold PML.cps_heap.
  intros fx R M model K HH Hmo HKnil Hfp (Hentry & (Ha0 & Ha1 & Ha2 & Hdp & Ha3 & Hn & (S2' & HskS2' & HS2' & Hrd)) & HskS2 & Hsk1 & Hsk2 & Hapsk & Hsink & Hobj & Himg & Hcred & Hroom) Hcont.
  destruct Hentry as (Hra & Hraok & Hsp & Htp & Hstk). destruct Hstk as (S1 & S2'' & S3 & S4 & S5).
  unfold PMFXT.DB_SCR, PMFXT.STRX_SCR, STRX_SCR, PMS.STR_SCR, PMS.OPNEW_SCR, PML.HEAP_STACK in *.
  pose proof (PmLayout.ly_segs L LAY) as LS. pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI.
  pose proof (PmLayout.ly_errno L LAY) as LER.
  (* [comment removed for export] *)
  pose proof Hobj as (OS1 & OS2 & OS3).
  assert (ES2 : S2' = S2).
  { unfold PML.u64, L5.u64_at, word_to_le_bytes in HskS2, HskS2'. rewrite HskS2 in HskS2'.
    pose proof (f_equal (fun o => match o with Some l => bytes_le_to_Z l | None => 0 end) HskS2') as E. cbn beta iota in E. rewrite !u64_of_Z in E by lia. rewrite !bytes_le_to_Z_of_le_bytes in E by lia.
    change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in E. rewrite !Z.mod_small in E by lia. exact (eq_sym E). }
  subst S2'.
  destruct Hrd as (Hbs & Hbdef & Hblen & Hb1 & Hb2 & Hb3 & Hb4). unfold PML.apart in Hb3, Hb4, Hapsk.
  set (len0 := len (PML.srep_chars rep)).
  set (E0 := Env (reg_ev R (fun v => Z_to_bv 64 (nth (v - 32) [S2] 0))) (fun _ => [])).
  assert (EV : forall x : reg, ev E0 (ridx x) = getr R x) by (intros x; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 PML.TP) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 buf) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (V11 : ev E0 11 = Z_to_bv 64 n) by (rewrite <- Ha1; exact (EV 11%bv)).
  assert (V12 : ev E0 12 = Z_to_bv 64 dp) by (rewrite <- Ha2; exact (EV 12%bv)).
  assert (V13 : ev E0 13 = Z_to_bv 64 SK) by (rewrite <- Ha3; exact (EV 13%bv)).
  assert (V32 : ev E0 32 = Z_to_bv 64 S2) by reflexivity.
  assert (CLO : 0x7fff7f800000 <= hl_ceil L) by (unfold hl_ceil; lia).
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; lia).
  assert (U10 : bv_unsigned (ev E0 10) = buf) by (rewrite V10; apply u64_of_Z; lia).
  assert (U11 : bv_unsigned (ev E0 11) = n) by (rewrite V11; apply u64_of_Z; lia).
  assert (U12 : bv_unsigned (ev E0 12) = dp) by (rewrite V12; apply u64_of_Z; lia).
  assert (U13 : bv_unsigned (ev E0 13) = SK) by (rewrite V13; apply u64_of_Z; lia).
  assert (U32 : bv_unsigned (ev E0 32) = S2) by (rewrite V32; apply u64_of_Z; lia).
  assert (SCRV : CH.hd_scr G.HDECL = 8608) by reflexivity.
  assert (STKF : sp mod 16 = 0 /\ hl_ceil L + CH.hd_scr G.HDECL <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47)
    by (rewrite SCRV; unfold hl_ceil; repeat split; lia).
  assert (SPR : hl_ceil L + 8608 <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47) by (unfold hl_ceil; repeat split; lia).
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (rewrite SCRV; lia).
  assert (NF32 : (32 <= GT.NF)%nat) by (unfold GT.NF; lia).
  assert (TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite V4, (PmLayout.ly_tp L LAY); reflexivity).
  set (W := [(S2, 24)]).
  assert (W_OK : forall (w : L5.range) (a : Z), In w W -> L5.in_rng w a -> CH2.wclient L sp a).
  { intros w a [<-|[]] Hin; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; (split; [lia | left; lia]). }
  assert (CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> CH2.sclient L LBo sp a)).
  { intros rg [<-|[<-|[]]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CH2.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot] in Ha.
    - rewrite U10, U11 in Ha. split; [lia | left; lia].
    - rewrite U13 in Ha. rewrite u64_of_Z in Ha by lia. split; [lia | left; lia]. }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> exists w : L5.range, In w W /\ L5.in_rng w a)).
  { intros rg [<-|[]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CH2.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot] in Ha.
    rewrite U32 in Ha. rewrite u64_of_Z in Ha by lia. exists (S2, 24). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia]. }
  assert (IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img G.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_alloc_static L a /\ ~ in_errno L a).
  { intros rg a []. }
  assert (DEF0 : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)).
  { rewrite SCRV. intros j Hj. apply S5. lia. }
  assert (W_S2 : In (S2, 24) W) by (left; reflexivity).
  assert (OADDR : estart E0 (SA S2E 0) = S2) by (unfold estart, S2E; cbn [a_base a_off edenot]; rewrite U32; lia).
  set (XIv := fun (g1 : ESBU.sghost) (i : nat) (E : env) (M1 : mem) => ESBU.sink_inv M1 S2 g1 /\ phase n i E (ESBU.s_len g1 - len0)).
  set (CredV := ESBU.CredV L kx bx).
  set (gB := ESBU.gB []).
  assert (GBL : forall g1, gB g1 = PML.srep_blocks (ESBU.s_rep g1)) by (intros g1; unfold gB, ESBU.gB; apply app_nil_r).
  (* [comment removed for export] *)
  assert (AGE : forall i c E E', nth_error G.CPS i = Some c -> env_agree GT.NF E0 E -> env_agree (CC.cp_nx c) E E' -> env_agree GT.NF E0 E').
  { intros i c E E' Hc H1 H2. eapply CC.env_agree_trans; [exact H1 | eapply CC.env_agree_le; [exact H2 | exact (G.NF_le i c Hc)]]. }
  assert (BRG : forall g1 M0c i E (M1 : mem) m1, CH2V.heap_ambV L HI GT.NF E0 model LBo sp G.HDECL W G.BLS ESBU.sghost gB CredV g1 M0c i E M1 m1 ->
                  (forall b, In b (PML.srep_blocks (ESBU.s_rep g1)) -> block_range L (fst b) (snd b)) /\ env_agree GT.NF E0 E /\
                  exists cr1, hi_heap HI (CH2.den E (nth i G.BLS []) ++ LBo ++ gB g1) cr1 M1 (m_vmmaps m1) /\ CredV g1 i E cr1).
  { intros g1 M0c i E M1 m1 (_ & _ & HagE & (cr1 & HH1 & HC1) & _). split; [|split; [exact HagE | exists cr1; split; [exact HH1 | exact HC1]]]. intros b Hb.
    destruct (hio_wf L SCFG HI HIok _ _ _ _ HH1) as (Hwf & _). apply (Hwf b). unfold CH2.cur, CH2V.LBr. apply in_or_app. right. apply in_or_app. right. rewrite GBL. exact Hb. }
  assert (STRETCH : forall g1 M0c i c k ps t E R1 (M1 : mem) m1 E' R' (M' : mem), CH2.is_leaf G.CPS G.TAGS i c k ps t -> CC.At (hl_segs L) c E R1 M1 ->
                      CH2V.heap_ambV L HI GT.NF E0 model LBo sp G.HDECL W G.BLS ESBU.sghost gB CredV g1 M0c i E M1 m1 -> XIv g1 i E M1 ->
                      env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M1 M' ->
                      ESBU.sink_inv M' S2 g1 /\ env_agree GT.NF E0 E').
  { intros g1 M0c i c k ps t E R1 M1 m1 E' R' M' IL HAt HA HX Hag HLF.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. unfold leaf_chk in X. apply andb_prop in X as [XF _]. apply andb_prop in XF as [XF _].
    destruct IL as (tags & Hc & _). destruct (BRG _ _ _ _ _ _ HA) as (HB & HagE & _). pose proof (AGE i c E E' Hc HagE Hag) as HagE'.
    split; [|exact HagE']. destruct HX as (HX1 & _).
    exact (sink_stretch E0 sp S2 8608 U2 ltac:(lia) SPR Hobj (CC.cp_F c) E' M1 M' g1 XF HagE' (CC.lf_frame _ _ _ _ _ _ _ HLF) HB HX1). }
  (* [comment removed for export] *)
  assert (UVK : forall (c : CC.cutpoint) E E' v, env_agree (CC.cp_nx c) E E' -> (50 <= CC.cp_nx c)%nat -> (v < 50)%nat -> uv E' (EVar v) = uv E (EVar v)).
  { intros c E E' v Hag Hnx Hv. unfold uv. apply (PB.uv_agree (CC.cp_nx c) E E' (EVar v) Hag). cbn [APC.expr_vars_lt]. apply Nat.ltb_lt. lia. }
  assert (PHB : forall i E p, phase n i E p -> p <= n + 1).
  { intros i E p HP. pose proof (PB.uv_range E (EVar 48)) as R48. fold uv in R48. clear - HP R48 Hn.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]; cbn [phase] in HP; try contradiction; lia. }
  unfold PML.cfg. change PMFX.PC_DUMP_BUFFER with (CC.cp_pc G.cp0). rewrite <- LS.
  eapply (CH2V.cert_sound3V L HI HIok (PB.LYI_ L LAY) (PB.LYE_ L LAY) (PmLayout.ly_ro L LAY) GT.NF E0 M model LBo sp G.HDECL W G.BLS ESBU.sghost gB CredV XIv STKF SCRP NF32 U2 W_OK WRS_OK
            G.CPS K PML.fp_ok G.TAGS) with (i := 0%nat) (E := E0).
  - rewrite LS. exact FPM.
  - rewrite LS. exact G.plans.
  - exact G.tags_ok.
  - exact heap_ok3.
  - (* [comment removed for export] *) intros g1 i c kk ps j sg IL E E' R' M1 M' cr1 _ _ _ HC. exact HC.
  - (* [comment removed for export] *)
    intros g1 M0c OKV i c kk ps j sg IL E R1 E' R' M1 M' m1 HAt HA Hag HLF HX.
    destruct (STRETCH g1 M0c i c kk ps _ E R1 M1 m1 E' R' M' IL HAt HA HX Hag HLF) as [HINV HagE'].
    pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. unfold leaf_chk in X. apply andb_prop in X as [XF X]. apply andb_prop in XF as [_ XN].
    destruct HX as (_ & HP). split; [exact HINV|].
    assert (O48 : uv (CC.env_over GT.NF sg E') (EVar 48) = uv E' (CC.slook sg 48)) by reflexivity.
    assert (O49 : uv (CC.env_over GT.NF sg E') (EVar 49) = uv E' (CC.slook sg 49)) by reflexivity.
    assert (U11' : uv E' (EVar 11) = n) by (unfold uv; rewrite (PB.uv_agree GT.NF E0 E' (EVar 11) HagE' eq_refl); exact U11).
    destruct i as [|[|i]]; destruct j as [|[|[|j]]]; try discriminate X.
    + (* [comment removed for export] *)
      apply andb_prop in X as [Xa Xb]. apply expr_eqb_eq in Xa. apply expr_eqb_eq in Xb.
      unfold phase in HP |- *. rewrite O48, O49, Xa, Xb, U11'. rewrite (uv_lit1 E' 1) by lia. lia.
    + (* [comment removed for export] *)
      apply andb_prop in X as [X Xc]. apply andb_prop in X as [Xa Xb]. apply expr_eqb_eq in Xa. apply expr_eqb_eq in Xb.
      assert (XN' : (50 <= CC.cp_nx c)%nat) by (apply orb_prop in XN as [XN|XN]; [apply Nat.leb_le; exact XN | discriminate XN]).
      destruct HAt as [_ HKN]. rewrite LS in HKN.
      unfold phase in HP |- *. rewrite O48, O49, Xa, Xb. rewrite (UVK c E E' 49%nat Hag XN' ltac:(lia)).
      rewrite uv_add_lit. rewrite (UVK c E E' 48%nat Hag XN' ltac:(lia)).
      (* [comment removed for export] *)
      pose proof (PB.prove_ok E M1 _ _ HKN Xc) as HK48. cbn [kentry_ok] in HK48. fold (PB.uv E (EVar 48)) in HK48. fold uv in HK48.
      rewrite Z.mod_small by lia. lia.
    + (* [comment removed for export] *)
      apply andb_prop in X as [Xa Xb]. apply expr_eqb_eq in Xa.
      assert (XN' : (50 <= CC.cp_nx c)%nat) by (apply orb_prop in XN as [XN|XN]; [apply Nat.leb_le; exact XN | discriminate XN]).
      unfold phase in HP |- *. rewrite O48, Xa. rewrite (UVK c E E' 48%nat Hag XN' ltac:(lia)). lia.
    + (* [comment removed for export] *)
      apply andb_prop in X as [X Xc]. apply andb_prop in X as [XA Xa]. apply expr_eqb_eq in Xa. pose proof (after_push_phase n (S (S i)) E _ XA HP) as HP'.
      assert (XN' : (50 <= CC.cp_nx c)%nat) by (apply orb_prop in XN as [XN|XN]; [apply Nat.leb_le; exact XN | discriminate XN]).
      destruct HAt as [_ HKN]. rewrite LS in HKN.
      unfold phase. rewrite O48, Xa.
      rewrite uv_add_lit. rewrite (UVK c E E' 48%nat Hag XN' ltac:(lia)).
      pose proof (PB.prove_ok E M1 _ _ HKN Xc) as HK48. cbn [kentry_ok] in HK48. fold (PB.uv E (EVar 48)) in HK48. fold uv in HK48.
      rewrite Z.mod_small by lia. lia.
  - (* [comment removed for export] *)
    intros i c kk ps pc IL g1 M0c OKV.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. unfold leaf_chk in X. apply andb_prop in X as [XF X]. apply andb_prop in XF as [XF XN].
    assert (XILEAF : forall E R1 (M1 : mem) m1 E' R' (M' : mem), CC.At (hl_segs L) c E R1 M1 ->
               CH2V.heap_ambV L HI GT.NF E0 model LBo sp G.HDECL W G.BLS ESBU.sghost gB CredV g1 M0c i E M1 m1 -> XIv g1 i E M1 -> env_agree (CC.cp_nx c) E E' ->
               CC.leaf_facts (hl_segs L) c ps E' R' M1 M' -> ESBU.sink_inv M' S2 g1).
    { intros E R1 M1 m1 E' R' M' HAt HA HX Hag HLF. exact (proj1 (STRETCH g1 M0c i c kk ps _ E R1 M1 m1 E' R' M' IL HAt HA HX Hag HLF)). }
    assert (HK' : forall E' R' (M1 M' : mem), CC.leaf_facts (hl_segs L) c ps E' R' M1 M' -> know_ok RSEGS E' M' (SR.ps_cells ps)).
    { intros E' R' M1 M' HLF. rewrite <- LS. unfold know_ok. apply Forall_forall. exact (CC.lf_cells _ _ _ _ _ _ _ HLF). }
    destruct (Z.eqb_spec pc PML.PC_STR_PUSH_BACK) as [->|Hne].
    + destruct (is_tail i) eqn:TL.
      * (* [comment removed for export] *)
        apply andb_prop in X as [X Y1]. apply andb_prop in X as [X Y10]. apply andb_prop in X as [X2 Y2]. apply Z.eqb_eq in X2.
        intros fx' E R1 M1 m1 E' R' M' HAt [HAmb HX] HFP Hag HLF _.
        assert (DEFC : L5.defined M0c (sp - 8608) 8608) by (rewrite <- SCRV; exact (CH2V.okV_def0 L M LBo sp G.HDECL W M0c OKV)).
        destruct (ETL.tail_leaf L HI HIok LAY GT.NF E0 M0c model (CH2V.LBr LBo ESBU.sghost gB g1) sp G.HDECL W G.BLS (CredV g1) STKF SCRP NF32 U2 W_OK WRS_OK G.CPS G.TAGS
                    (CH2V.okV_def0 L M LBo sp G.HDECL W M0c OKV) 8608 ltac:(rewrite SCRV; lia) ltac:(unfold hl_ceil; lia) DEFC R EV heap_ok3
                    i c kk ps PML.PC_STR_PUSH_BACK IL Y2 E R1 M1 m1 E' R' M' HAt HAmb Hag HLF) as (HRP & KEEP & HP & HA' & HagE').
        destruct (STRETCH g1 M0c i c kk ps _ E R1 M1 m1 E' R' M' IL HAt HAmb HX Hag HLF) as [HINV _].
        destruct HX as [_ HPH].
        destruct (BRG _ _ _ _ _ _ HA') as (HB & _ & cr1 & HH1 & HC1).
        assert (Hnil : CH2.den E (nth i G.BLS []) = []) by (destruct i as [|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]; try discriminate TL; reflexivity).
        rewrite Hnil in HH1. cbn [app] in HH1. rewrite GBL in HH1.
        assert (HP2 : L5C.hpres L LBo sp 8608 W M M').
        { rewrite <- SCRV. apply (CH2V.hpres_rebase L GT.NF M LBo sp G.HDECL W ESBU.sghost gB NF32 g1 M0c M' OKV). rewrite SCRV. exact HP. }
        destruct HA' as (Hmo1 & Hbv1 & _).
        assert (Ga0 : getr R' 10%bv = Z_to_bv 64 S2).
        { pose proof (CL.ps_reg_is_sound (hl_segs L) c ps E' R' M1 M' 10 (EVar 32) HLF Y10) as G10.
          replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) in G10 by (apply bv_eq; reflexivity). rewrite G10. cbn [edenot].
          destruct HagE' as [AG _]. rewrite <- AG by (unfold GT.NF; lia). exact V32. }
        assert (Ga1 : getr R' 11%bv = Z_to_bv 64 48).
        { pose proof (CL.ps_reg_is_sound (hl_segs L) c ps E' R' M1 M' 11 (ELit 48) HLF Y1) as G11.
          replace (Z_to_bv 5 (Z.of_nat 11)) with (11%bv : bv 5) in G11 by (apply bv_eq; reflexivity). rewrite G11. reflexivity. }
        pose proof HINV as [Hsink1 Hlen1]. pose proof (PHB _ _ _ HPH) as HPB.
        rewrite X2, LS.
        apply (PUSHB_OK (LBo ++ PML.srep_blocks (ESBU.s_rep g1)) cr1 S2 48 sp r (ESBU.s_rep g1) fx' R' M' m1 K HH1 Hmo1 HKnil HFP).
        { split; [split; [rewrite (KEEP 1%bv ltac:(left; reflexivity)); exact Hra | split; [exact Hraok | split; [rewrite (KEEP 2%bv ltac:(right; left; reflexivity)); exact Hsp |
                   split; [rewrite (KEEP 4%bv ltac:(right; right; right; left; reflexivity)); exact Htp|]]]]|].
          - unfold STRX_SCR, PMS.STR_SCR, PMS.OPNEW_SCR, PML.HEAP_STACK. split; [exact S1|]. split; [unfold hl_ceil in *; lia|]. split; [lia|]. split; [lia|].
            intros j Hj. replace (sp - (256 + (16 + 8224)) + j) with (sp - 8608 + (j + 112)) by lia. apply (L5C.hpres_defined _ _ _ _ _ _ _ HP2). lia.
          - split; [exact Ga0|]. split; [exact Ga1|]. split; [lia|]. split; [exact Hsink1|].
            split; [destruct (ESBU.s_rep g1) as [s0|cap0 p0 s0]; cbn [rep_live PML.srep_blocks]; [exact I | apply in_or_app; right; left; reflexivity]|].
            split; [exact Hobj|]. intros HNF. apply (EK.grow_okU L (PmLayout.ly_kpm L LAY) (PmLayout.ly_bov L LAY) cr1 (ESBU.s_rep g1) kx bx _ HC1 (EK.rep8_of_sink _ _ _ Hsink1));
              [unfold len; lia | lia | exact HNF]. }
        intros fx2 R2 M2 model2 LB' cr' LBk Wc HFP2 (rep' & Hgrown & HWc) HRP2 HPc Hbv2 HH2. subst Wc.
        assert (Hrep8 : match ESBU.s_rep g1 with PML.SShort _ => True | PML.SLong cap _ _ => 8 <= cap /\ cap mod 8 = 0 end).
        { destruct Hsink1 as (Hs1 & _ & Hs3). destruct (ESBU.s_rep g1) as [s0|cap0 p0 s0]; [exact I|]. cbn [rep_ok PML.str_at] in *. destruct Hs1 as (_ & Hm & _). split; [lia | exact Hm]. }
        assert (Hcl : len (PML.srep_chars (ESBU.s_rep g1) ++ [48]) <= CLU) by (unfold len in Hlen1 |- *; rewrite length_app; cbn [length]; lia).
        pose proof (EK.grown_screditU L (PmLayout.ly_kpm L LAY) (PmLayout.ly_bov L LAY) _ _ _ _ _ _ _ _ _ _ kx bx Hgrown Hrep8 Hcl HC1) as HC'.
        assert (Hdrop : lb_drop (ESBU.s_rep g1) (LBo ++ PML.srep_blocks (ESBU.s_rep g1)) = LBo).
        { pose proof (ESBU.den_app_nodup L HI HIok LBo [] [] (ESBU.s_rep g1) cr1 M' (m_vmmaps m1)) as D. cbn [app] in D. rewrite !app_nil_r in D. apply D. exact HH1. }
        assert (FACTS : sink_at M2 S2 rep' /\ len (PML.srep_chars rep') = ESBU.s_len g1 + 1 /\ LBk = LBo /\ Permutation LB' (LBo ++ PML.srep_blocks rep')).
        { destruct Hgrown as [(F & -> & Hs & -> & _ & ->)|(NFt & p' & Gx)].
          - split; [exact Hs|]. split; [destruct (ESBU.s_rep g1); cbn [same_rep PML.srep_chars] in *; unfold len in *; rewrite length_app; cbn [length]; lia|].
            split; [exact Hdrop|]. destruct (ESBU.s_rep g1); cbn [same_rep PML.srep_blocks]; apply Permutation_refl.
          - cbv zeta in Gx. destruct Gx as (-> & Hs & FB & -> & _ & ->). split; [exact Hs|].
            split; [cbn [PML.srep_chars]; unfold len in *; rewrite length_app; cbn [length]; lia|]. split; [exact Hdrop|].
            rewrite Hdrop. cbn [PML.srep_blocks]. apply Permutation_cons_append. }
        destruct FACTS as (Hsink2 & Hlen2 & -> & Hperm).
        apply (Hcont fx2 R2 M2 model2 (LBo ++ PML.srep_blocks rep') cr' LBo W HFP2); [| exact (L5.regs_preserved_trans _ _ _ HRP HRP2) | |
               exact (L5C.model_but_vm_trans _ _ _ Hbv1 Hbv2) | exact (CH2V.hi_heap_perm L HI HIok _ _ _ _ _ HH2 Hperm)].
        -- exists rep', (ESBU.s_len g1 + 1 - len0).
           assert (HPH' : 1 <= ESBU.s_len g1 - len0 <= n + 1) by (destruct i as [|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]; try discriminate TL; cbn [phase] in HPH; exact HPH).
           split; [lia|]. split; [exact I|]. split; [exact Hsink2|]. split; [unfold len0 in *; lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
           exact HC'.
        -- apply (ETL.hpres_comp L LBo sp 8608 (256 + (16 + 8224)) W M M' M2); [lia | unfold hl_ceil in *; lia | lia | rewrite LER; lia | lia | exact HP2 | exact HPc].
      * (* [comment removed for export] *)
        apply andb_prop in X as [X Xi]. apply andb_prop in X as [X2 X3]. apply Z.eqb_eq in X2.
        unfold sink_j in X3. apply andb_prop in X3 as [X3a X3b].
        destruct (CH2.ret_of G.RETS i kk) as [j|] eqn:Hret; [|discriminate]. apply Nat.eqb_eq in X3a.
        destruct (nth_error G.CPS (ret_cut i kk)) as [cj|] eqn:Hcj; [|discriminate].
        destruct (ESBU.pushb_chk GT.NF G.HDECL S2E 0 c ps cj (nth i G.BLS []) (nth (ret_cut i kk) G.BLS [])) as [ci|] eqn:Hchk; [|discriminate].
        subst j.
        assert (XN' : (50 <= CC.cp_nx c)%nat).
        { apply orb_prop in XN as [XN|XN]; [apply Nat.leb_le; exact XN|]. apply Nat.eqb_eq in XN. subst i. discriminate Xi. }
        assert (XILEAF' : forall E R1 (M1 : mem) m1 E' R' (M' : mem), CC.At (hl_segs L) c E R1 M1 ->
                   CH2V.heap_ambV L HI GT.NF E0 model LBo sp G.HDECL W G.BLS ESBU.sghost gB CredV g1 M0c i E M1 m1 -> XIv g1 i E M1 -> env_agree (CC.cp_nx c) E E' ->
                   CC.leaf_facts (hl_segs L) c ps E' R' M1 M' -> ESBU.sink_inv M' S2 g1 /\ ESBU.s_len g1 + 1 <= CLU).
        { intros E R1 M1 m1 E' R' M' HAt HA HX Hag HLF. split; [exact (XILEAF E R1 M1 m1 E' R' M' HAt HA HX Hag HLF)|].
          destruct HX as [_ HP]. pose proof (PHB _ _ _ HP). lia. }
        apply (ESBU.pushb_leaf_ok L HI HIok LAY GT.NF E0 M model LBo sp G.HDECL W G.BLS [] kx bx XIv STKF SCRP NF32 U2 TP0 W_OK CRS_OK WRS_OK IMG_OK G.CPS G.TAGS G.RETS K HKnil DEF0
                 S2 Hobj W_S2 S2E 0 eq_refl OADDR PUSHB_OK i c kk ps (ret_cut i kk) cj ci g1 M0c OKV IL Hret Hcj X2 Hchk XILEAF').
        intros E E' R' M1 M' E2 M2 g' HX HagE' Hag HLF Hag2 Hnx HINV2 G1.
        split; [exact HINV2|]. destruct HX as [_ HP]. rewrite G1.
        assert (E48 : uv E2 (EVar 48) = uv E (EVar 48)).
        { unfold uv. rewrite (PB.uv_agree (CH2.ci_nx ci) E' E2 (EVar 48) Hag2) by (cbn [APC.expr_vars_lt]; apply Nat.ltb_lt; lia).
          apply (PB.uv_agree (CC.cp_nx c) E E' (EVar 48) Hag). cbn [APC.expr_vars_lt]. apply Nat.ltb_lt. lia. }
        pose proof (PB.uv_range E (EVar 48)) as R48. fold uv in R48.
        destruct i as [|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]; try discriminate Xi; cbn [phase] in HP.
        -- (* [comment removed for export] *)
           destruct kk as [|[|[|[|[|[|[|[|[|[|kk]]]]]]]]]]; cbn [ret_cut phase]; rewrite ?E48; lia.
        -- (* [comment removed for export] *)
           cbn [ret_cut phase]. rewrite E48. lia.
        -- (* [comment removed for export] *)
           cbn [ret_cut phase].
           pose proof (PB.prove_ok E' M' _ _ (HK' E' R' M1 M' HLF) Xi) as HK48. cbn [kentry_ok] in HK48. fold (PB.uv E' (EVar 48)) in HK48. fold uv in HK48.
           rewrite (UVK c E E' 48%nat Hag XN' ltac:(lia)) in HK48. lia.
    + (* [comment removed for export] *)
      apply andb_prop in X as [X Xi]. apply andb_prop in X as [X1 XK].
      intros fx' E R1 M1 m1 E' R' M' HAt [HAmb HX] HFP Hag HLF _.
      destruct (STRETCH g1 M0c i c kk ps _ E R1 M1 m1 E' R' M' IL HAt HAmb HX Hag HLF) as [HINV HagE'0].
      assert (DEFC : L5.defined M0c (sp - 8608) 8608) by (rewrite <- SCRV; exact (CH2V.okV_def0 L M LBo sp G.HDECL W M0c OKV)).
      apply (PB.exit_ret L HI HIok LAY GT.NF E0 M0c model (CH2V.LBr LBo ESBU.sghost gB g1) sp G.HDECL W G.BLS (CredV g1) STKF SCRP NF32 U2 W_OK WRS_OK G.CPS G.TAGS K (XIv g1)
               (CH2V.okV_def0 L M LBo sp G.HDECL W M0c OKV) (fun _ => 0) (fun _ => 0)
               8608 ltac:(rewrite SCRV; lia) ltac:(unfold hl_ceil; lia) DEFC R EV r Hra Hraok heap_ok3 RETPC i c kk ps pc ret_at IL X1 fx' E R1 M1 m1 E' R' M' HAt HAmb Hag HLF).
      intros HRP HP HA' HagE'. destruct HA' as (Hmo1 & Hbv1 & HagE1 & (cr1 & HH1 & HC1) & _ & _).
      destruct HX as [_ HPH].
      assert (HP2 : L5C.hpres L LBo sp 8608 W M M').
      { rewrite <- SCRV. apply (CH2V.hpres_rebase L GT.NF M LBo sp G.HDECL W ESBU.sghost gB NF32 g1 M0c M' OKV). rewrite SCRV. exact HP. }
      pose proof (HK' E' R' M1 M' HLF) as HK.
      pose proof (PB.prove_ok E' M' _ _ HK XK) as HK48. cbn [kentry_ok] in HK48. fold (PB.uv E' (EVar 48)) in HK48. fold uv in HK48.
      assert (XN' : (50 <= CC.cp_nx c)%nat).
      { apply orb_prop in XN as [XN|XN]; [apply Nat.leb_le; exact XN|]. apply Nat.eqb_eq in XN. subst i. discriminate Xi. }
      assert (E48 : uv E' (EVar 48) = uv E (EVar 48)) by (exact (UVK c E E' 48%nat Hag XN' ltac:(lia))).
      assert (HPAY : 1 <= ESBU.s_len g1 - len0 <= n).
      { destruct i as [|[|i]]; try discriminate Xi.
        - cbn [phase] in HPH. pose proof (PB.prove_ok E' M' _ _ HK Xi) as HK49. cbn [kentry_ok] in HK49. fold (PB.uv E' (EVar 49)) in HK49. fold uv in HK49.
          rewrite (UVK c E E' 49%nat Hag XN' ltac:(lia)) in HK49. lia.
        - pose proof (after_push_phase n (S (S i)) E _ Xi HPH) as HPH'. lia. }
      apply (Hcont fx' R' M' m1 (LBo ++ PML.srep_blocks (ESBU.s_rep g1)) cr1 LBo W HFP); [| exact HRP | exact HP2 | exact Hbv1 |].
      * exists (ESBU.s_rep g1), (ESBU.s_len g1 - len0). destruct HINV as [Hs Hl].
        split; [lia|]. split; [exact I|]. split; [exact Hs|]. split; [unfold len0 in *; lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. exact HC1.
      * unfold CH2.cur, CH2V.LBr in HH1. rewrite GBL in HH1.
        assert (Hnil : CH2.den E (nth i G.BLS []) = []) by (destruct i as [|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]; try discriminate Xi; reflexivity).
        rewrite Hnil in HH1. exact HH1.
  - reflexivity.
  - (* [comment removed for export] *)
    rewrite LS.
    assert (Hds : L5.defined M (sp - 8608) 8608) by (intros j Hj; apply S5; lia).
    pose proof Hsink as (Hst & HdS2 & Hrok).
    split; [exact (regs_ok_id R _ _)|]. unfold know_ok, G.cp0. cbn [CC.cp_know].
    repeat (apply Forall_cons); [.. | apply Forall_nil].
    + eapply CL5.kword64_intro with (A := SK) (z := S2); [ev_start | lia | lia | exact V32 | exact HskS2].
    + e_range.
    + e_range.
    + eapply CL5.kunk_intro; [ev_start | ev_len | lia | lia | lia | replace (buf + 0) with buf by lia; replace (0 + (1 * n + 0)) with n by lia; exact Hbdef].
    + e_range.
    + e_range.
    + e_range.
    + e_align OS3.
    + e_unk. + e_wr. + e_range. + e_align S1.
    + e_disj. + e_disj. + e_disj. + e_disj. + e_disj. + e_disj.
    + e_unk.
  - (* [comment removed for export] *)
    apply (CH2V.amb3V_intro L HI GT.NF E0 M model LBo sp G.HDECL W G.BLS ESBU.sghost gB CredV XIv (ESBU.SG rep len0) M 0%nat E0 M model
             (CH2V.okV_refl L M LBo sp G.HDECL W DEF0)).
    split; [|split; [split; [exact Hsink | reflexivity] | cbn [phase ESBU.s_len]; lia]].
    split; [exact Hmo|]. split; [apply L5C.model_but_vm_refl|]. split; [apply CC.env_agree_refl|].
    split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
    exists cr. split; [unfold CH2.cur, CH2V.LBr; cbn [nth G.BLS GT.BL0 CH2.den map app]; rewrite (GBL (ESBU.SG rep len0)); cbn [ESBU.s_rep]; exact HH|].
    exact Hcred.
  - exact Hfp.
Qed.
End DumpBufOk.
End DBXU.
Print Assumptions DBXU.dump_buffer_x_ok.
