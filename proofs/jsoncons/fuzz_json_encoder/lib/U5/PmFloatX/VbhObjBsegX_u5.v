(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5 PmEncSpecs2_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX CutHeap2V.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Cut_vbh_obj_bseg_xsrc_T_u5 Cut_vbh_obj_bseg_xsrc_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmGrow Require Import GrowKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5 ParseBridges2_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncSums_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmEnc Require Import EncSums2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncAppendK_u5 EncKit_u5 EncKit2_u5 EncKit3_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmFloatX Require Import VbmKitX_u5 VbhKitX_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module VBH_OB.
Import PML. Import PMES.
Module G := Cut_vbh_obj_bseg_xsrc_u5.   Module GT := Cut_vbh_obj_bseg_xsrc_T_u5.
Definition MALLOC : Z := PML.PC_MALLOC.  Definition FREE : Z := PML.PC_FREE.
Definition ENDPC : Z := Eval vm_compute in hd 0 GT.ENDS.
Definition KEPT : list nat := [2; 3; 4; 8; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Definition has := GK.has.
Ltac hcell a o := match goal with H : has _ (KWord (SA a o) _ _) = true |- _ => exact H end.
Ltac hblob := match goal with H : has _ (KBlob _ _ _) = true |- _ => exact H end.

Lemma heap_ok : CH2.heap_chk GT.NF G.HDECL G.BLS G.CPS GK.HULL_LO GK.HULL_HI G.TAGS G.RETS MALLOC FREE [] = true.
Proof. vm_compute. reflexivity. Qed.
Lemma no_goto : CH2.leaves_all G.CPS G.TAGS (fun _ _ _ _ t => match t with CC.TGoto _ _ => false | CC.TOther _ => true end) = true.
Proof. vm_compute. reflexivity. Qed.
Definition exit_chk (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) : bool :=
  let cells := SR.ps_cells ps in
  (CL.ps_at ps [ENDPC] && CL.ps_keeps ps KEPT && Nat.leb GT.NF (CC.cp_nx c) && Nat.eqb i 0
   && has cells (KWord (SA (EVar 8) 296) 8 (EAlu ALU_ADD (EVar 37) (ELit 2)))
   && CL.ps_reg_is ps 1 (ELit 247044) && CL.ps_reg_is ps 9 (EAlu ALU_ADD (EVar 8) (ELit 264)) && CL.ps_reg_is ps 10 (EVar 8) && CL.ps_reg_is ps 18 (EAlu ALU_ADD (EMd M_MUL (ELit 32) (EVar 33)) (EVar 34)) && has cells (KWord (SA (EVar 2) 31) 1 (ELit 0)) && has cells (KWord (SA (EAlu ALU_ADD (EMd M_MUL (ELit 32) (EVar 33)) (EVar 34)) (-32)) 4 (ELit 1)) && has cells (KWord (SA (EAlu ALU_ADD (EMd M_MUL (ELit 32) (EVar 33)) (EVar 34)) (-28)) 1 (ELit 0)) && has cells (KWord (SA (EAlu ALU_ADD (EMd M_MUL (ELit 32) (EVar 33)) (EVar 34)) (-26)) 1 (ELit 1)) && has cells (KWord (SA (EAlu ALU_ADD (EMd M_MUL (ELit 32) (EVar 33)) (EVar 34)) (-8)) 8 (EVar 36)) && has cells (KBlob (SA (EVar 34) 0) (EAlu ALU_ADD (EMd M_MUL (ELit 32) (EVar 33)) (ELit (-32))) 0) && CH2.blocks_eqb (nth i G.BLS []) [(EVar 34, EVar 35)])%bool.
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with CC.TGoto _ _ => false | CC.TOther pc => (negb (CH2.is_call MALLOC FREE [] pc) && exit_chk i c ps)%bool end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true.
Proof. vm_compute. reflexivity. Qed.
Lemma kept_lt48 : forall y : reg, In (ridx y) KEPT -> (ridx y < 48)%nat.
Proof. intros y Hy. unfold KEPT in Hy. cbn [In] in Hy. intuition lia. Qed.
Lemma kept_in : forall r : reg, In (bv_unsigned r) [2; 3; 4; 8; 19; 20; 21; 22; 23; 24; 25; 26; 27] -> In (ridx r) KEPT.
Proof. intros r H. unfold ridx, KEPT. cbn [In] in H. repeat (destruct H as [H|H]; [rewrite <- H; cbn; tauto|]). destruct H. Qed.
Lemma kept_in8 : forall r : reg, In (bv_unsigned r) [3; 19; 20; 21; 22; 23; 24; 25; 26; 27] -> In (ridx r) KEPT.
Proof. intros r H. unfold ridx, KEPT. cbn [In] in H. repeat (destruct H as [H|H]; [rewrite <- H; cbn; tauto|]). destruct H. Qed.
Lemma reg_of_leaf : forall segs c ps E' R' (M1 M' : PML.mem) (x : bv 5) n e,
  CC.leaf_facts segs c ps E' R' M1 M' -> CL.ps_reg_is ps n e = true -> bv_unsigned x = Z.of_nat n -> getr R' x = edenot E' e.
Proof.
  intros segs c ps E' R' M1 M' x n e HLF Hchk Hx. pose proof (CL.ps_reg_is_sound segs c ps E' R' M1 M' n e HLF Hchk) as G0.
  replace x with (Z_to_bv 5 (Z.of_nat n)); [exact G0|]. apply bv_eq. rewrite Z_to_bv_unsigned, Hx. pose proof (bv_unsigned_in_range 5 x) as RG.
  unfold bv_wrap. rewrite Z.mod_small; [reflexivity|]. rewrite <- Hx. exact RG.
Qed.

Section Seg.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps GK.RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom GK.RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom GK.RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.

Lemma seg_ok : forall (LBo : list (Z * Z)) (cr : credit) (spf V S2 b capb dI dD : Z) (rep : srep) (c0 : ectx) (r0 : estate),
  ec_arr c0 = true ->
  PMES2.cps_seg L HI 246924 PC_NEW_LINE spf 0 (LBo ++ srep_blocks rep ++ stack_blocks b capb) cr
    (fun R M => getr R 2%bv = Z_to_bv 64 spf /\ getr R 4%bv = Z_to_bv 64 TP /\ L5C.stk (hl_sptop L) M spf 0 /\ spf mod 16 = 0 /\ getr R 8%bv = Z_to_bv 64 V /\
                PMES2.enc_objx M V S2 dI dD /\ stack_at M V (c0 :: r0) b capb /\ depth (c0 :: r0) < MAX_DEPTH /\ obj_on_stack L (spf + 64) V ENC_SIZE /\ L5.defined M spf 32)
    (fun R M R' M' LB' cr' LBk W =>
       getr R' 1%bv = Z_to_bv 64 247044 /\ getr R' 2%bv = Z_to_bv 64 spf /\ getr R' 4%bv = Z_to_bv 64 TP /\ getr R' 8%bv = Z_to_bv 64 V /\ getr R' 9%bv = Z_to_bv 64 (V + O_STACK) /\
       a0 R' V /\ getr R' 18%bv = Z_to_bv 64 (b + 32 * depth (c0 :: r0)) /\ PMES2.regs_kept false R R' /\ u8 M' (spf + 31) 0 /\
       PMES2.enc_objx M' V S2 dI dD /\ stack_at M' V (set_nla c0 :: r0) b capb /\
       LB' = LBo ++ srep_blocks rep ++ stack_blocks b capb /\ LBk = LBo ++ srep_blocks rep /\ W = [(V + O_COLUMN, 8); (spf, 32)] /\ cr' = cr).
Proof.
  intros LBo cr spf V S2 b capb dI dD rep c0 r0 HARR. unfold PMES2.cps_seg.
  intros fx R M model K HH Hmo HKnil Hfp PRE Hcont.
  destruct PRE as (Hsp & Htp & Hstk & Hsp16 & Hs0 & HOBJ & I2 & Hdep & HOV & HdF).
  destruct Hstk as (SK1 & SK2 & SK3 & SK4 & SK5). destruct HOV as (OV1 & OV2 & OV3). unfold ENC_SIZE, MAX_DEPTH, O_STACK in *.
  pose proof (PmLayout.ly_segs L LAY) as LS. pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI. pose proof (PmLayout.ly_stack L LAY) as LSTK. unfold PML.HEAP_STACK in LSTK.
  pose proof (PmLayout.ly_errno L LAY) as LER.
  assert (CLO : 0x7fff7f800000 <= hl_ceil L) by lia. unfold PML.a0 in *.
  set (d := depth (c0 :: r0)) in *.
  assert (Hd1 : 1 <= d) by (unfold d, depth; cbn [length]; lia). assert (HdNN : 0 <= d) by lia.
  pose proof I2 as TT. destruct TT as (T1 & T2 & T3 & T4 & T5 & T6). fold d in T2, T4, T6. unfold O_STACK in T1, T2, T3. replace (V + 264 + 8) with (V + 272) in T2 by lia.
  set (LB := LBo ++ srep_blocks rep ++ stack_blocks b capb) in *.
  destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hwf & Hnd & Hcr0 & _).
  destruct T5 as [[Hc0 Hb0] | (kk & Hkk & Hcapk)]; [lia|].
  assert (Hpk : 2 ^ kk <= 2 ^ 10) by (apply Z.pow_le_mono_r; lia). change (2 ^ 10) with 1024 in Hpk. assert (Hp0 : 0 < 2 ^ kk) by (apply Z.pow_pos_nonneg; lia).
  assert (Hcap32 : 32 <= capb <= 32768) by nia. assert (Hcnz : capb <> 0) by lia.
  assert (SBK : stack_blocks b capb = [(b, capb)]) by (unfold stack_blocks; destruct (Z.eqb_spec capb 0); [lia | reflexivity]).
  assert (HinLB : In (b, capb) LB) by (unfold LB; rewrite SBK; apply in_or_app; right; apply in_or_app; right; left; reflexivity).
  destruct (Hwf _ HinLB) as ((P0 & P1 & P2 & P3 & P4) & Pdef & Pap). cbn [fst snd] in P0, P1, P2, P3, P4, Pdef, Pap. assert (PdefL : L5.defined M b capb) by exact Pdef.
  pose proof (EK3.stack_head M V c0 r0 b capb I2) as HC. destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
  rewrite HARR in C1. cbn [b2z] in C1.
  assert (Hdr : depth r0 = d - 1) by (unfold d; rewrite EK2.depth_cons; lia). rewrite Hdr in C1, C2, C3, C4, C6.
  replace (b + 32 * (d - 1)) with (b + 32 * d - 32) in C1, C2, C3, C4, C6 by lia.
  set (cnt := ec_count c0) in *.
  pose proof HOBJ as HOBJ0.
  destruct HOBJ as (_ & _ & _ & _ & _ & _ & _ & _ & E31 & E32 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ecol & _ & _ & ECOMMA & _).
  unfold O_SPLITS, O_COLUMN, O_COMMA, TXT_COMMA, sv_at in E31, E32, Ecol, ECOMMA.
  destruct ECOMMA as [E320 E328]. replace (V + 320 + 8) with (V + 328) in E328 by lia.
  replace (V + 28 + 3) with (V + 31) in E31 by lia. replace (V + 28 + 4) with (V + 32) in E32 by lia.
  destruct (EAK.u64_of_defined M (V + 296) Ecol) as (col & Hcol64 & Hcol).
  (* [comment removed for export] *)
  assert (Hdold : L5.defined M b (Z.of_nat (Z.to_nat (32 * d - 32)))) by (rewrite Z2Nat.id by lia; intros i Hi; apply Pdef; lia).
  destruct (EAK.bytes_of_defined M (Z.to_nat (32 * d - 32)) b ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia) Hdold) as (OLD & HOLDlen & HOLD).
  assert (HOLDZ : Z.of_nat (length OLD) = 32 * d - 32) by (rewrite HOLDlen; lia).
  set (E0 := Env (reg_ev R (fun v => Z_to_bv 64 (nth (v - 32) [0; d; b; capb; cnt; col] 0))) (fun id => nth id [map (fun z => Z_to_bv 8 z) OLD] [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 spf) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 PML.TP) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V8 : ev E0 8 = Z_to_bv 64 V) by (rewrite <- Hs0; exact (EV 8%bv)).
  assert (V33 : ev E0 33 = Z_to_bv 64 d) by reflexivity.
  assert (V34 : ev E0 34 = Z_to_bv 64 b) by reflexivity.
  assert (U2 : bv_unsigned (ev E0 2) = spf) by (rewrite V2; apply u64_of_Z; lia).
  assert (U8 : bv_unsigned (ev E0 8) = V) by (rewrite V8; apply u64_of_Z; lia).
  assert (U33 : bv_unsigned (ev E0 33) = d) by (rewrite V33; apply u64_of_Z; lia).
  assert (U34 : bv_unsigned (ev E0 34) = b) by (rewrite V34; apply u64_of_Z; lia).
  assert (V35 : ev E0 35 = Z_to_bv 64 capb) by reflexivity. assert (V36 : ev E0 36 = Z_to_bv 64 cnt) by reflexivity. assert (V37 : ev E0 37 = Z_to_bv 64 col) by reflexivity.
  assert (U35 : bv_unsigned (ev E0 35) = capb) by (rewrite V35; apply u64_of_Z; lia).
  assert (U36 : bv_unsigned (ev E0 36) = cnt) by (rewrite V36; apply u64_of_Z; lia).
  assert (U37 : bv_unsigned (ev E0 37) = col) by (rewrite V37; apply u64_of_Z; lia).
  assert (FR : forall E1, env_agree GT.NF E0 E1 -> bv_unsigned (ev E1 2) = spf /\ bv_unsigned (ev E1 8) = V /\ bv_unsigned (ev E1 33) = d /\ bv_unsigned (ev E1 34) = b /\ bv_unsigned (ev E1 35) = capb).
  { intros E1 [AG _]. rewrite <- !AG by (unfold GT.NF; lia). repeat split; assumption. }
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= 0x7fff7f800000) by (rewrite ILO, IHI; lia).
  assert (LYE : hl_img_lo L <= hl_errno L /\ hl_errno L + 4 <= hl_img_hi L) by (rewrite ILO, IHI, LER; lia).
  assert (SCRV : CH.hd_scr G.HDECL = 0) by reflexivity.
  assert (STKF : spf mod 16 = 0 /\ hl_ceil L + CH.hd_scr G.HDECL <= spf /\ spf <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47) by (rewrite SCRV; repeat split; lia).
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (rewrite SCRV; lia).
  assert (NF32 : (32 <= GT.NF)%nat) by (unfold GT.NF; lia).
  assert (TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite V4, (PmLayout.ly_tp L LAY); reflexivity).
  assert (HSTKE : hl_stack L = CH.hd_hstk G.HDECL) by (rewrite LSTK; reflexivity).
  assert (LSTK0 : 0 <= hl_stack L) by (rewrite LSTK; lia).
  set (Wm := [(V + 296, 8); (spf, 32)]).
  set (LBR := LBo ++ srep_blocks rep).
  assert (HHR : hi_heap HI ((b, capb) :: LBR) cr M (m_vmmaps model)).
  { apply (CH2V.hi_heap_perm L HI HIok _ _ _ _ _ HH). unfold LB, LBR. rewrite SBK. apply Permutation_sym. rewrite (app_assoc LBo (srep_blocks rep) [(b, capb)]). rewrite <- (app_nil_r (LBo ++ srep_blocks rep)) at 1. apply Permutation_middle. }
  assert (INR : forall b0, In b0 LBR -> In b0 LB) by (intros b0 Hb0; unfold LBR, LB in *; rewrite app_assoc; apply in_or_app; left; exact Hb0).
  assert (W_OK : forall (w : L5.range) (a : Z), In w Wm -> L5.in_rng w a -> CH2.wclient L spf a).
  { intros w a Hw Hin. destruct Hw as [<-|[<-|[]]]; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; (split; [lia | left; lia]). }
  assert (CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> CH2.sclient L LBR spf a)).
  { intros rg Hrg. unfold G.HDECL, GT.HDECL in Hrg. cbn [CH.hd_crs] in Hrg.
    repeat (destruct Hrg as [<-|Hrg]); [..|destruct Hrg]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CH2.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot] in Ha;
    rewrite U8 in Ha; rewrite u64_of_Z in Ha by lia; (split; [lia | left; lia]). }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> exists w : L5.range, In w Wm /\ L5.in_rng w a)).
  { intros rg Hrg. destruct Hrg as [<-|[<-|[]]]; split; try (vm_compute; reflexivity); intros a Ha; unfold CH2.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot] in Ha.
    - rewrite U8 in Ha. rewrite u64_of_Z in Ha by lia. exists (V + 296, 8). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia].
    - rewrite U2 in Ha. rewrite u64_of_Z in Ha by lia. exists (spf, 32). split; [right; left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia]. }
  assert (IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img G.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_alloc_static L a /\ ~ in_errno L a).
  { intros rg a [<-|[]] Ha. cbn [fst snd] in Ha. rewrite ILO, IHI. unfold in_errno. rewrite LER.
    split; [lia|]. split; [intros X; pose proof (PmLayout.ly_static L LAY a X); lia | lia]. }
  assert (FPM0 : forall (fx0 fx' : FPState) R0 pc M1 R' pc' M', msteps (hl_segs L) (@mkst fx0 R0 (Z_to_bv 64 pc) M1 (seg_rom (hl_segs L))) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom (hl_segs L))) -> PML.fp_ok fx0 -> PML.fp_ok fx')
    by (rewrite LS; exact FPM).
  assert (Hds : L5.defined M (spf - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)) by (rewrite SCRV; intros j Hj; lia).
  assert (ENDV : forall o, estart E0 (SA (EAlu ALU_ADD (EMd M_MUL (ELit 32) (EVar 33)) (EVar 34)) o) = b + 32 * d + o).
  { intros o. unfold estart. cbn [a_base a_off]. rewrite (CL5.u_lin E0 _ (b + 32 * d)); [lia | lin_eval; rw_atoms; lia | lia]. }
  unfold PML.cfg. change 246924 with (CC.cp_pc G.cp0). rewrite <- LS.
  eapply CH2.heap_cert_sound with (NF := GT.NF) (E0 := E0) (M0 := M) (model0 := model) (LBrest := LBR) (sp0 := spf) (d := G.HDECL)
    (W := Wm) (BLS := G.BLS) (Cred := fun _ _ cr' => cr' = cr) (CPS := G.CPS) (TAGS := G.TAGS) (RETS := G.RETS) (MALLOC := MALLOC) (FREE := FREE)
    (COPIES := []) (IMG_LO := GK.HULL_LO) (IMG_HI := GK.HULL_HI) (FPI := PML.fp_ok) (i := 0%nat) (E := E0) (HI := HI).
  - exact HIok.
  - exact LYI.
  - exact LYE.
  - exact (PmLayout.ly_ro L LAY).
  - exact LSTK0.
  - exact STKF.
  - exact SCRP.
  - exact HSTKE.
  - exact NF32.
  - exact U2.
  - exact TP0.
  - exact W_OK.
  - exact CRS_OK.
  - exact WRS_OK.
  - exact IMG_OK.
  - exact HKnil.
  - exact ILO.
  - exact IHI.
  - exact FPM0.
  - rewrite LS. exact G.plans.
  - exact G.tags_ok.
  - exact heap_ok.
  - exact (PmLayout.ly_malloc L LAY).
  - exact (PmLayout.ly_free L LAY).
  - intros pc [].
  - intros i c0' kk0 ps j sg IL. exfalso. pose proof (CH2.leaves_all_sound _ _ _ no_goto _ _ _ _ _ IL) as X. cbv beta iota in X. discriminate X.
  - intros i c0' kk0 ps j cj IL Hret Hcj E E' R' M1 M1' cr' HagE Hag HLF HC. exfalso.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. unfold leaf_chk in X. change (CH2.is_call MALLOC FREE [] MALLOC) with true in X. cbn [negb andb] in X. discriminate X.
  - intros i c0' kk0 ps pc j cj IL Hcall Hnm Hret Hcj. exfalso.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. unfold leaf_chk in X. rewrite Hcall in X. cbn [negb andb] in X. discriminate X.
  - (* [comment removed for export] *)
    intros i c0' kk0 ps pc IL Hnc.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. unfold leaf_chk in X. rewrite Hnc in X. cbn [negb andb] in X. unfold exit_chk in X.
    intros fx' E R1 M1 m1 E' R' M' HAt HAmb HFP Hag HLF _.
    pose proof (CH2.exit_amb L HI HIok LYI LYE (PmLayout.ly_ro L LAY) GT.NF E0 M model LBR spf G.HDECL Wm G.BLS (fun _ _ cr' => cr' = cr) STKF SCRP NF32 U2 W_OK WRS_OK
                  G.CPS GK.HULL_LO GK.HULL_HI G.TAGS G.RETS MALLOC FREE [] heap_ok i c0' kk0 ps pc IL Hnc E E' R1 R' M1 M' m1 HAt HAmb Hag HLF) as HA'.
    repeat (apply andb_prop in X as [X ?Y]).
    pose proof HA' as HA2. destruct HA' as (Hmo1 & Hbv1 & HagE1 & (cr1 & HH1 & HC1) & Hfr1 & Hdf1). subst cr1.
    match goal with H : Nat.leb GT.NF (CC.cp_nx c0') = true |- _ => apply Nat.leb_le in H; rename H into XNF end.
    match goal with H : Nat.eqb i 0 = true |- _ => apply Nat.eqb_eq in H; rename H into Xi end. subst i.
    match goal with H : CH2.blocks_eqb _ _ = true |- _ => apply CH2.blocks_eqb_eq in H; rename H into XBL end.
    assert (HagE' : env_agree GT.NF E0 E') by (eapply CC.env_agree_trans; [exact HagE1 | eapply CC.env_agree_le; [exact Hag | exact XNF]]).
    destruct (FR E' HagE') as (F2 & F8 & F33 & F34 & F35).
    rewrite LS in HLF.
    assert (CELL : forall X0, has (SR.ps_cells ps) X0 = true -> kentry_ok GK.RSEGS E' M' X0).
    { intros X0 HX. apply (CC.lf_cells _ _ _ _ _ _ _ HLF). exact (GK.has_In _ _ HX). }
    assert (REG : forall (x : bv 5) n e, CL.ps_reg_is ps n e = true -> bv_unsigned x = Z.of_nat n -> getr R' x = edenot E' e).
    { intros x n e Hc' Hx. exact (reg_of_leaf _ c0' ps E' R' M1 M' x n e HLF Hc' Hx). }
    assert (KEEP : forall y : reg, In (ridx y) KEPT -> getr R' y = getr R y).
    { intros y Hy. match goal with H : CL.ps_keeps ps KEPT = true |- _ => rewrite (CL.ps_keeps_sound GK.RSEGS c0' ps E0 E' R' M1 M' KEPT GT.NF y HLF H HagE' Hy (kept_lt48 y Hy)) end. exact (EV y). }
    pose proof (CH2.amb_hpres L HI LYI LYE GT.NF E0 M model LBR spf G.HDECL Wm G.BLS (fun _ _ cr' => cr' = cr) STKF NF32 0%nat E M' m1 HA2 Hds) as HP. rewrite SCRV in HP.
    assert (KST : forall a, spf <= a < 2 ^ 64 -> ~ (V + 296 <= a < V + 304) -> ~ (spf <= a < spf + 32) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha Hna Hnf. apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP). apply (L5C.kept_stack_stk L LBR M spf 0 Wm a); [repeat split; try lia; intros j Hj; lia | lia | lia | rewrite LER; lia |].
      unfold Wm. apply L5C.outside_cons; [unfold L5.in_rng; cbn [fst snd]; lia | apply L5C.outside_cons; [unfold L5.in_rng; cbn [fst snd]; lia | apply L5C.outside_nil]]. }
    apply Z.eqb_eq in X. unfold ENDPC in X. rewrite X, LS.
    assert (HH2 : hi_heap HI ((b, capb) :: LBR) cr M' (m_vmmaps m1)).
    { unfold CH2.cur in HH1. rewrite XBL in HH1. cbn [CH2.den map fst snd app] in HH1. cbn [edenot] in HH1. pose proof HagE1 as [AG1 _].
      rewrite <- (AG1 34%nat ltac:(unfold GT.NF; lia)), <- (AG1 35%nat ltac:(unfold GT.NF; lia)), U34, U35 in HH1. exact HH1. }
    assert (HH3 : hi_heap HI LB cr M' (m_vmmaps m1)).
    { apply (CH2V.hi_heap_perm L HI HIok _ _ _ _ _ HH2). unfold LB, LBR. rewrite SBK. rewrite (app_assoc LBo (srep_blocks rep) [(b, capb)]). rewrite <- (app_nil_r (LBo ++ srep_blocks rep)) at 1. apply Permutation_middle. }
    destruct (hio_wf L SCFG HI HIok _ _ _ _ HH3) as (Hwf2 & _). destruct (Hwf2 _ HinLB) as (_ & Qdef & _). cbn [fst snd] in Qdef.
    assert (AGV : forall a n, V <= a -> a + n <= V + 408 -> (a + n <= V + 296 \/ V + 304 <= a) -> L5C.agree_on M M' a n) by (intros a n Ha Hn Ho i1 Hi1; apply KST; lia).
    assert (HOBJ' : PMES2.enc_objx M' V S2 dI dD).
    { apply (EK3.enc_objx_agree M M' V S2 dI dD ltac:(lia) ltac:(unfold ENC_SIZE; lia)); unfold O_STACK, O_INDENT, O_COLON, O_COLUMN, ENC_SIZE.
      - apply AGV; lia. - apply AGV; lia. - apply AGV; lia.
      - intros i1 Hi1. apply (Hdf1 (V + 296 + i1) ltac:(lia)); [|exact (Ecol i1 Hi1)]. split; [right; left; lia | unfold in_errno; rewrite LER; lia].
      - exact HOBJ0. }
    assert (HSTK' : stack_at M' V (set_nla c0 :: r0) b capb).
    { pose proof I2 as (T1' & T2' & T3' & _). unfold O_STACK in T1', T2', T3'. fold d in T2'.
      apply (VBHK.stack_at_top_cells M M' V c0 (set_nla c0) r0 b capb); unfold O_STACK; [ | | | | | exact I2].
      - apply (EK.u64_agree M M'); [apply AGV; lia | lia | lia | exact T1'].
      - fold d. apply (EK.u64_agree M M'); [apply AGV; lia | lia | lia | exact T2'].
      - apply (EK.u64_agree M M'); [apply AGV; lia | lia | lia | exact T3'].
      - intros i0 Hi0.
        assert (HBL' : L5.bytes_at GK.RSEGS M' b OLD /\ elenZ E' (EAlu ALU_ADD (EMd M_MUL (ELit 32) (EVar 33)) (ELit (-32))) = Z.of_nat (length OLD)).
        { apply (CL5.kblob_elim GK.RSEGS E' M' _ _ 0%nat b OLD (CELL _ ltac:(hblob))); [unfold estart; cbn [a_base a_off edenot]; rewrite F34; lia|].
          destruct HagE' as [_ HB']. rewrite <- HB'. reflexivity. }
        destruct HBL' as [HBL' _].
        assert (Hlen : Z.of_nat (length r0) = d - 1) by (unfold d, depth; cbn [length]; lia).
        replace (b + 32 * Z.of_nat i0) with (b + Z.of_nat (32 * i0)) by lia.
        apply (VBK.ctx_at_xfer M M' b b _ OLD (32 * i0)%nat); [rewrite HOLDlen; lia | lia | rewrite HOLDZ; lia | lia | rewrite HOLDZ; lia | exact HOLD | exact HBL' | | ].
        + intros j Hj. replace (b + Z.of_nat (32 * i0) + j) with (b + (Z.of_nat (32 * i0) + j)) by lia. apply Qdef. lia.
        + replace (b + Z.of_nat (32 * i0)) with (b + 32 * Z.of_nat i0) by lia. replace (nth (length r0 - 1 - i0) r0 ctx0) with (nth (length (c0 :: r0) - 1 - i0) (c0 :: r0) ctx0) by (cbn [length]; replace (S (length r0) - 1 - i0)%nat with (S (length r0 - 1 - i0)) by lia; reflexivity). apply T6. cbn [length]. lia.
      - rewrite Hdr. replace (b + 32 * (d - 1)) with (b + 32 * d - 32) by lia. unfold ctx_at. cbn [ec_arr ec_nla ec_count set_nla]. rewrite HARR. cbn [b2z].
        split; [pose proof (PB2.kword32_elim E' M' _ _ (b + 32 * d - 32) (CELL _ ltac:(hcell (EAlu ALU_ADD (EMd M_MUL (ELit 32) (EVar 33)) (EVar 34)) (-32))) ltac:(rewrite (PB.estart_agree GT.NF E0 E' (EAlu ALU_ADD (EMd M_MUL (ELit 32) (EVar 33)) (EVar 34)) (-32) HagE' eq_refl), ENDV; lia)) as T; unfold PB.uv in T; cbn [edenot] in T; rewrite (u64_of_Z 1) in T by lia; exact T|].
        split; [exact (GK.kword8_elim E' M' _ _ (b + 32 * d - 32 + 4) 0 (CELL _ ltac:(hcell (EAlu ALU_ADD (EMd M_MUL (ELit 32) (EVar 33)) (EVar 34)) (-28))) ltac:(rewrite (PB.estart_agree GT.NF E0 E' (EAlu ALU_ADD (EMd M_MUL (ELit 32) (EVar 33)) (EVar 34)) (-28) HagE' eq_refl), ENDV; lia) ltac:(cbn [edenot]; apply u64_of_Z; lia))|].
        split; [exact (GK.kword8_elim E' M' _ _ (b + 32 * d - 32 + 6) 1 (CELL _ ltac:(hcell (EAlu ALU_ADD (EMd M_MUL (ELit 32) (EVar 33)) (EVar 34)) (-26))) ltac:(rewrite (PB.estart_agree GT.NF E0 E' (EAlu ALU_ADD (EMd M_MUL (ELit 32) (EVar 33)) (EVar 34)) (-26) HagE' eq_refl), ENDV; lia) ltac:(cbn [edenot]; apply u64_of_Z; lia))|].
        split; [apply (CL5.kword64_elim GK.RSEGS E' M' _ _ (b + 32 * d - 32 + 24) cnt (CELL _ ltac:(hcell (EAlu ALU_ADD (EMd M_MUL (ELit 32) (EVar 33)) (EVar 34)) (-8)))); [rewrite (PB.estart_agree GT.NF E0 E' (EAlu ALU_ADD (EMd M_MUL (ELit 32) (EVar 33)) (EVar 34)) (-8) HagE' eq_refl), ENDV; lia | cbn [edenot]; destruct HagE' as [AG _]; rewrite <- (AG 36%nat ltac:(unfold GT.NF; lia)); exact U36]|].
        split; [exact C5|]. intros j Hj. replace (b + 32 * d - 32 + j) with (b + (32 * d - 32 + j)) by lia. apply Qdef. lia. }
    apply (Hcont fx' R' M' m1 LB cr LBR Wm HFP); [| exact HP | exact Hbv1 | exact HH3].
    split; [rewrite (REG 1%bv 1%nat _ ltac:(eassumption) eq_refl); reflexivity|].
    split; [rewrite (KEEP 2%bv ltac:(cbn; tauto)); exact Hsp|].
    split; [rewrite (KEEP 4%bv ltac:(cbn; tauto)); exact Htp|].
    split; [rewrite (KEEP 8%bv ltac:(cbn; tauto)); exact Hs0|].
    split. { rewrite (REG 9%bv 9%nat _ ltac:(eassumption) eq_refl). rewrite <- (Z_to_bv_bv_unsigned _ (edenot E' _)). f_equal. apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia]. }
    split; [rewrite (REG 10%bv 10%nat (EVar 8) ltac:(eassumption) eq_refl); cbn [edenot]; rewrite <- (Z_to_bv_bv_unsigned _ (ev E' 8)), F8; reflexivity|].
    split. { rewrite (REG 18%bv 18%nat _ ltac:(eassumption) eq_refl). rewrite <- (Z_to_bv_bv_unsigned _ (edenot E' _)). f_equal. apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia]. }
    split; [intros y Hy; apply KEEP; apply kept_in8; exact Hy|].
    split; [exact (GK.kword8_elim E' M' _ _ (spf + 31) 0 (CELL _ ltac:(hcell (EVar 2) 31)) ltac:(unfold estart; cbn [a_base a_off edenot]; rewrite F2; lia) ltac:(cbn [edenot]; apply u64_of_Z; lia))|].
    split; [exact HOBJ'|]. split; [exact HSTK'|].
    split; [reflexivity|]. split; [unfold LBR, LB; reflexivity|]. split; [reflexivity | reflexivity].
  - reflexivity.
  - (* [comment removed for export] *)
    rewrite LS. split; [exact (regs_ok_id R _ _)|].
    unfold know_ok, G.cp0. cbn [CC.cp_know].
    repeat (apply Forall_cons); [.. | apply Forall_nil]; first
      [ eapply CL5.kword64_intro; [ev_start | lia | lia | | eassumption]; rewrite <- (Z_to_bv_bv_unsigned _ (edenot E0 _)); f_equal; try (apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia])
      | eapply PB2.kword8_intro; [ev_start | lia | lia | reflexivity | lia | first [exact E31 | exact E32]]
      | (eapply PB.kword32_intro; [rewrite ENDV; reflexivity | lia | lia | reflexivity | replace (b + 32 * d + -32) with (b + 32 * d - 32) by lia; exact C1])
      | (eapply PB2.kword8_intro; [rewrite ENDV; reflexivity | lia | lia | reflexivity | lia | replace (b + 32 * d + -28) with (b + 32 * d - 32 + 4) by lia; exact C2])
      | (eapply CL5.kword64_intro; [rewrite ENDV; reflexivity | lia | lia | exact V36 | replace (b + 32 * d + -8) with (b + 32 * d - 32 + 24) by lia; exact C4])
      | (eapply (CL5.kblob_intro GK.RSEGS E0 M _ _ 0%nat b OLD); [ev_start | apply CL5.elen_lin; [lin_eval; rw_atoms; lia | lia] | lia | lia | lia | reflexivity | exact HOLD | rewrite HOLDZ; intros i Hi; apply Pdef; lia])
      | e_align P2
      | e_range
      | e_align OV3 | e_align SK1
      | e_unk | e_wr | e_disj
      | idtac ].
    all: fail "entry knowledge left".
  - (* [comment removed for export] *)
    split; [exact Hmo|]. split; [apply L5C.model_but_vm_refl|]. split; [apply CC.env_agree_refl|].
    split; [|split; [reflexivity | intros a _ _ Hdd; exact Hdd]].
    exists cr. split; [|reflexivity]. unfold CH2.cur.
    replace (CH2.den E0 (nth 0 G.BLS [])) with [(b, capb)]; [exact HHR|]. unfold CH2.den. cbn [nth G.BLS GT.BL0 map fst snd edenot]. rewrite U34, U35. reflexivity.
  - exact Hfp.
Qed.
End Seg.
End VBH_OB.
