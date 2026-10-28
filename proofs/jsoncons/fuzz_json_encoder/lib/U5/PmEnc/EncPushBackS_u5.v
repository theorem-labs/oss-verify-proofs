(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Cut_str_push_back_x_sso_xsrc_T_u5 Cut_str_push_back_x_sso_xsrc_u5 Cut_str_push_back_x_sso_full_xsrc_T_u5 Cut_str_push_back_x_sso_full_xsrc_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutDemo Require Pm6Memmove_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmGrow Require Import GrowKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncSums_u5 EncOpNew_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module EPS.
Module S := Cut_str_push_back_x_sso_xsrc_u5.        Module ST := Cut_str_push_back_x_sso_xsrc_T_u5.
Module G := Cut_str_push_back_x_sso_full_xsrc_u5.   Module GT := Cut_str_push_back_x_sso_full_xsrc_T_u5.
Definition OPNEW : Z := PML.PC_OPNEW.
Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.
Definition MALLOC : Z := PML.PC_MALLOC.  Definition FREE : Z := PML.PC_FREE.  Definition MEMMOVE : Z := 0xbe44c.
Definition RET : Z := Eval vm_compute in hd 0 ST.ENDS.
Definition SCRT : Z := Eval vm_compute in CH.hd_scr S.HDECL.       (* [comment removed for export] *)
Definition CSAVED := CL5.CSAVED.
Definition has := GK.has.

Lemma heap_ok_s : CH2.heap_chk ST.NF S.HDECL S.BLS S.CPS GK.HULL_LO GK.HULL_HI S.TAGS S.RETS MALLOC FREE [MEMMOVE] = true.
Proof. vm_compute. reflexivity. Qed.
Lemma heap_ok_g : CH2.heap_chk GT.NF G.HDECL G.BLS G.CPS GK.HULL_LO GK.HULL_HI G.TAGS G.RETS MALLOC FREE [MEMMOVE] = true.
Proof. vm_compute. reflexivity. Qed.
Lemma no_goto_s : CH2.leaves_all S.CPS S.TAGS (fun _ _ _ _ t => match t with CC.TGoto _ _ => false | CC.TOther _ => true end) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma no_goto_g : CH2.leaves_all G.CPS G.TAGS (fun _ _ _ _ t => match t with CC.TGoto _ _ => false | CC.TOther _ => true end) = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition e_o := EVar 10.  Definition e_c := EVar 11.  Definition e_n := EVar 32.
Definition e_on : expr := EAlu ALU_ADD e_o e_n.

(* [comment removed for export] *)
Definition exit_s (c : CC.cutpoint) (ps : SR.post_spec) : bool :=
  let cells := SR.ps_cells ps in
  (CL.ps_at ps [RET] && CL.ps_keeps ps CSAVED && Nat.leb ST.NF (CC.cp_nx c)
   && has cells (KWord (SA e_o 0) 1 (EAlu ALU_ADD (EMd M_MUL (ELit 2) e_n) (ELit 2))) && has cells (KBlob (SA e_o 1) e_n 0)
   && has cells (KWord (SA e_on 1) 1 e_c) && has cells (KWord (SA e_on 2) 1 (ELit 0)))%bool.
Definition leaf_s (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with CC.TGoto _ _ => false | CC.TOther pc => (negb (CH2.is_call MALLOC FREE [MEMMOVE] pc) && Nat.eqb i 0 && exit_s c ps)%bool end.
Lemma leaf_s_ok : CH2.leaves_all S.CPS S.TAGS leaf_s = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition pre (i : nat) : bool := Nat.eqb i 0.
Definition hd_base (i : nat) : expr := fst (hd (ELit 0, ELit 0) (nth i G.BLS [])).
Definition hd_size (i : nat) : expr := snd (hd (ELit 0, ELit 0) (nth i G.BLS [])).
Definition exit_g (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) : bool :=
  let cells := SR.ps_cells ps in let pe := hd_base i in let ce := hd_size i in
  (CL.ps_at ps [RET] && CL.ps_keeps ps CSAVED && CH2.blocks_vars_lt (CC.cp_nx c) (nth i G.BLS []) && Nat.leb GT.NF (CC.cp_nx c)
   && negb (pre i) && match nth i G.BLS [] with [_] => true | _ => false end
   && has cells (KWord (SA e_o 0) 8 (ELit 49)) && has cells (KWord (SA e_o 8) 8 (ELit 23)) && has cells (KWord (SA e_o 16) 8 pe)
   && has cells (KBlob (SA pe 0) (ELit 22) 0) && has cells (KWord (SA pe 22) 1 e_c) && has cells (KWord (SA pe 23) 1 (ELit 0))
   && expr_eqb ce (ELit 48) && match pe with EVar v => Nat.leb GT.NF v | _ => false end)%bool.
Definition leaf_g (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      if CH2.is_call MALLOC FREE [MEMMOVE] pc then
        match CH2.ret_of G.RETS i k with
        | Some j => (negb (Z.eqb pc MALLOC) && negb (pre i) && negb (pre j))%bool
        | None => false
        end
      else if Z.eqb pc OPNEW then
        match CH2.ret_of G.RETS i k with
        | Some j =>
            match nth_error G.CPS j with
            | Some cj => (pre i && negb (pre j) && Z.eqb (SR.ps_pc ps) OPNEW && Nat.leb GT.NF (CC.cp_nx c) && expr_eqb (nth 10 (CA.ps_reglist ps) (ELit 0)) (ELit 48)
                          && isSome (EON.opnew_chk GT.NF G.HDECL c ps cj (nth i G.BLS []) (nth j G.BLS [])))%bool
            | None => false
            end
        | None => false
        end
      else exit_g i c ps
  end.
Lemma leaf_g_ok : CH2.leaves_all G.CPS G.TAGS leaf_g = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ret_at : CL.is_ret_at GK.RSEGS RET.
Proof. CL.solve_is_ret. Qed.

Section PushBackS.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps GK.RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom GK.RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom GK.RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.

(* [comment removed for export] *)
Lemma push_back_sso_in_x : forall (LB : list (Z * Z)) (cr : credit) (o c sp r : Z) (s : list Z),
  PML.cps_heap L HI PML.PC_STR_PUSH_BACK r sp PMS.STR_SCR LB cr
      (fun R M => Z.of_nat (length s) <= 21 /\ PML.entry L R M sp r PMS.STR_SCR /\ PML.a0 R o /\ PML.a1 R c /\ 0 <= c < 256 /\ PML.str_at M o (PML.SShort s) /\
                  L5.defined M o 24 /\ PML.obj_on_stack L sp o 24)
      (fun R M R' M' LB' cr' LBk W => (PML.str_at M' o (PML.SShort (s ++ [c])) /\ L5.defined M' o 24 /\ LB' = LB /\ cr' = cr /\ LBk = LB) /\ W = [(o, 24)]).
Proof.
  intros LB cr o c sp r s. unfold PML.cps_heap.
  intros fx R M model K HH Hmo HKnil Hfp (H21 & Hentry & Ha0 & Ha1 & Hc & Hstr & Hdo & Hobj) Hcont.
  destruct Hentry as (Hra & Hraok & Hsp & Htp & Hstk). destruct Hstk as (S1 & S2 & S3 & S4 & S5).
  unfold PMS.STR_SCR, PMS.OPNEW_SCR, PML.HEAP_STACK in *.
  destruct Hstr as (Hlen22 & Hb0 & Hbs & Hnul).
  destruct Hobj as (O1 & O2 & O3).
  set (n := Z.of_nat (length s)) in *.
  pose proof (PmLayout.ly_segs L LAY) as LS. pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI. pose proof (PmLayout.ly_stack L LAY) as LSTK. unfold PML.HEAP_STACK in LSTK.
  destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hwf & Hnd & _).
  set (E0 := Env (reg_ev R (fun v => Z_to_bv 64 (nth (v - 32) [n] 0))) (fun id => nth id [map (Z_to_bv 8) s] [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 PML.TP) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 o) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (V11 : ev E0 11 = Z_to_bv 64 c) by (rewrite <- Ha1; exact (EV 11%bv)).
  assert (V32 : ev E0 32 = Z_to_bv 64 n) by reflexivity.
  assert (CLO : 0x7fff7f800000 <= hl_ceil L) by lia.
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; lia).
  assert (U10 : bv_unsigned (ev E0 10) = o) by (rewrite V10; apply u64_of_Z; lia).
  assert (U11 : bv_unsigned (ev E0 11) = c) by (rewrite V11; apply u64_of_Z; lia).
  assert (U32 : bv_unsigned (ev E0 32) = n) by (rewrite V32; apply u64_of_Z; lia).
  assert (FR : forall E1, env_agree ST.NF E0 E1 ->
            bv_unsigned (ev E1 2) = sp /\ bv_unsigned (ev E1 10) = o /\ bv_unsigned (ev E1 11) = c /\
            bv_unsigned (ev E1 32) = n /\ eb E1 = eb E0).
  { intros E1 [A B]. rewrite <- !A by (unfold ST.NF; lia). repeat split; try assumption. symmetry. exact B. }
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= 0x7fff7f800000) by (rewrite ILO, IHI; lia).
  assert (LYE : hl_img_lo L <= hl_errno L /\ hl_errno L + 4 <= hl_img_hi L) by (rewrite ILO, IHI, (PmLayout.ly_errno L LAY); lia).
  assert (STKF : sp mod 16 = 0 /\ hl_ceil L + CH.hd_scr S.HDECL <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47)
    by (change (CH.hd_scr S.HDECL) with SCRT; unfold SCRT; repeat split; lia).
  assert (SCRP : 0 <= CH.hd_scr S.HDECL) by (change (CH.hd_scr S.HDECL) with SCRT; unfold SCRT; lia).
  assert (NF32 : (32 <= ST.NF)%nat) by (unfold ST.NF; lia).
  assert (W_OK : forall (w : L5.range) (a : Z), In w [(o, 24)] -> L5.in_rng w a -> CH2.wclient L sp a).
  { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. split; [lia | left; lia]. }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs S.HDECL) -> SGP.region_vars_lt ST.NF rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> exists w : L5.range, In w [(o, 24)] /\ L5.in_rng w a)).
  { intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CH2.in_reg, estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha.
    rewrite U10 in Ha. rewrite u64_of_Z in Ha by lia. exists (o, 24). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia]. }
  unfold PML.cfg. change PML.PC_STR_PUSH_BACK with (CC.cp_pc S.cp0). rewrite <- LS.
  eapply CH2.heap_cert_sound with (NF := ST.NF) (E0 := E0) (M0 := M) (model0 := model) (LBrest := LB) (sp0 := sp) (d := S.HDECL)
    (W := [(o, 24)]) (BLS := S.BLS) (Cred := fun _ _ cr' => cr' = cr) (CPS := S.CPS) (TAGS := S.TAGS) (RETS := S.RETS) (MALLOC := MALLOC) (FREE := FREE)
    (COPIES := [MEMMOVE]) (IMG_LO := GK.HULL_LO) (IMG_HI := GK.HULL_HI) (FPI := PML.fp_ok) (i := 0%nat) (E := E0) (HI := HI).
  - exact HIok.
  - exact LYI.
  - exact LYE.
  - exact (PmLayout.ly_ro L LAY).
  - rewrite LSTK. lia.
  - exact STKF.
  - exact SCRP.
  - rewrite LSTK. reflexivity.
  - exact NF32.
  - exact U2.
  - rewrite V4, (PmLayout.ly_tp L LAY). reflexivity.
  - exact W_OK.
  - intros rg [].
  - exact WRS_OK.
  - intros rg a [].
  - exact HKnil.
  - exact ILO.
  - exact IHI.
  - rewrite LS. exact FPM.
  - rewrite LS. exact S.plans.
  - exact S.tags_ok.
  - exact heap_ok_s.
  - exact (PmLayout.ly_malloc L LAY).
  - exact (PmLayout.ly_free L LAY).
  - intros pc [<-|[]]. exact (Pm6Memmove_u5.memmove_copy1 L LS).
  - intros i c0 kk ps j sg IL. exfalso. pose proof (CH2.leaves_all_sound _ _ _ no_goto_s _ _ _ _ _ IL) as X. cbv beta iota in X. discriminate X.
  - intros i c0 kk ps j cj IL. exfalso. pose proof (CH2.leaves_all_sound _ _ _ leaf_s_ok _ _ _ _ _ IL) as X. unfold leaf_s in X.
    change (CH2.is_call MALLOC FREE [MEMMOVE] MALLOC) with true in X. discriminate X.
  - intros i c0 kk ps pc j cj IL Hcall. exfalso. pose proof (CH2.leaves_all_sound _ _ _ leaf_s_ok _ _ _ _ _ IL) as X. unfold leaf_s in X. rewrite Hcall in X. discriminate X.
  - (* [comment removed for export] *)
    intros i c0 kk ps pc IL Hnc fx' E R1 M1 m1 E' R' M' HAt HAmb HFP Hag HLF _.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_s_ok _ _ _ _ _ IL) as X. unfold leaf_s in X. rewrite Hnc in X.
    apply andb_prop in X as [Xi X]. apply andb_prop in Xi as [_ Xi]. apply Nat.eqb_eq in Xi. subst i. unfold exit_s in X.
    pose proof (CH2.exit_amb L HI HIok LYI LYE (PmLayout.ly_ro L LAY) ST.NF E0 M model LB sp S.HDECL [(o, 24)] S.BLS (fun _ _ cr' => cr' = cr) STKF SCRP NF32 U2 W_OK WRS_OK
                  S.CPS GK.HULL_LO GK.HULL_HI S.TAGS S.RETS MALLOC FREE [MEMMOVE] heap_ok_s _ c0 kk ps pc IL Hnc E E' R1 R' M1 M' m1 HAt HAmb Hag HLF) as HA'.
    repeat (apply andb_prop in X as [X ?Y]).
    (* [comment removed for export] *)
    apply Z.eqb_eq in X. apply Nat.leb_le in Y3.
    pose proof HA' as HA2. destruct HA' as (Hmo1 & Hbv1 & HagE1 & (cr1 & HH1 & HC1) & Hfr1 & Hdf1). subst cr1.
    assert (HagE' : env_agree ST.NF E0 E') by (eapply CC.env_agree_trans; [exact HagE1 | eapply CC.env_agree_le; [exact Hag | exact Y3]]).
    destruct (FR E' HagE') as (F2 & F10 & F11 & F32 & FB).
    rewrite LS in HLF.
    assert (CELL : forall X0, has (SR.ps_cells ps) X0 = true -> kentry_ok GK.RSEGS E' M' X0).
    { intros X0 HX. apply (CC.lf_cells _ _ _ _ _ _ _ HLF). exact (GK.has_In _ _ HX). }
    assert (HH2 : hi_heap HI LB cr M' (m_vmmaps m1)).
    { unfold CH2.cur in HH1. change (nth 0 S.BLS []) with (@nil (expr * expr)) in HH1. exact HH1. }
    (* [comment removed for export] *)
    assert (UB0 : bv_unsigned (edenot E' (EAlu ALU_ADD (EMd M_MUL (ELit 2) e_n) (ELit 2))) = 2 * n + 2) by (apply CL5.u_lin; [unfold e_n; lin_eval; rw_atoms; lia | lia]).
    assert (UON : bv_unsigned (edenot E' e_on) = o + n) by (apply CL5.u_lin; [unfold e_on, e_o, e_n; lin_eval; rw_atoms; lia | lia]).
    assert (B0 : L5.u8_at GK.RSEGS M' o (2 * (n + 1))).
    { replace (2 * (n + 1)) with (2 * n + 2) by lia. apply (GK.kword8_elim E' M' _ _ o _ (CELL _ Y2)); [unfold estart, e_o; cbn [a_base a_off edenot]; rewrite F10; lia | exact UB0]. }
    assert (BS : L5.bytes_at GK.RSEGS M' (o + 1) s).
    { apply (CL5.kblob_elim GK.RSEGS E' M' _ _ 0%nat (o + 1) s (CELL _ Y1)); [unfold estart, e_o; cbn [a_base a_off edenot]; rewrite F10; lia | rewrite FB; reflexivity]. }
    assert (BC : L5.u8_at GK.RSEGS M' (o + 1 + n) c).
    { apply (GK.kword8_elim E' M' _ _ (o + 1 + n) c (CELL _ Y0)); [unfold estart; cbn [a_base a_off]; rewrite UON; lia | exact F11]. }
    assert (NUL : L5.u8_at GK.RSEGS M' (o + 1 + (n + 1)) 0).
    { apply (CL5.kword8_zero_elim GK.RSEGS E' M' _ _ (CELL _ Y)). unfold estart. cbn [a_base a_off]. rewrite UON. lia. }
    assert (LEN : Z.of_nat (length (s ++ [c])) = n + 1) by (rewrite length_app, Nat2Z.inj_add; reflexivity).
    assert (STR : PML.str_at M' o (PML.SShort (s ++ [c]))).
    { unfold PML.str_at, L5.lstr_short. rewrite LEN. split; [rewrite length_app; cbn [length]; lia|]. split; [exact B0|]. split; [|exact NUL].
      apply CL5.bytes_at_app; [exact BS|]. intros j Hj. cbn [length] in Hj. assert (j = 0%nat) by lia. subst j. cbn [nth]. rewrite Z.add_0_r. exact BC. }
    assert (DEF : L5.defined M' o 24).
    { intros j Hj. pose proof (Hdf1 (o + j) ltac:(lia)) as D. rewrite <- (Z_to_bv_bv_unsigned _ (Z_to_bv 64 (o + j))). rewrite u64_of_Z by lia.
      apply D; [| exact (Hdo j Hj)]. split; [right; left; split; lia | unfold in_errno; rewrite (PmLayout.ly_errno L LAY); lia]. }
    (* [comment removed for export] *)
    assert (KEEP : forall y : reg, In (ridx y) CSAVED -> getr R' y = getr R y).
    { intros y Hy. assert (Hy32 : (ridx y < ST.NF)%nat) by (unfold CSAVED, CL5.CSAVED in Hy; cbn [In] in Hy; unfold ST.NF; intuition lia).
      rewrite (CL.ps_keeps_sound GK.RSEGS c0 ps E0 E' R' M1 M' CSAVED ST.NF y HLF Y4 HagE' Hy Hy32). exact (EV y). }
    assert (HRP : regs_preserved R R') by (intros y Hy; apply KEEP; exact (CL5.csaved_in y Hy)).
    assert (Hra' : getr R' 1%bv = Z_to_bv 64 r) by (rewrite (KEEP 1%bv ltac:(left; reflexivity)); exact Hra).
    assert (Hds : L5.defined M (sp - CH.hd_scr S.HDECL) (CH.hd_scr S.HDECL)).
    { change (CH.hd_scr S.HDECL) with SCRT. unfold SCRT. intros j Hj. replace (sp - 8304 + j) with (sp - (256 + (16 + 8224)) + (j + 192)) by lia. apply S5. lia. }
    pose proof (CH2.amb_hpres L HI LYI LYE ST.NF E0 M model LB sp S.HDECL [(o, 24)] S.BLS (fun _ _ cr' => cr' = cr) STKF NF32 0%nat E M' m1 HA2 Hds) as HP0.
    change (CH.hd_scr S.HDECL) with SCRT in HP0.
    assert (HP : L5C.hpres L LB sp (256 + (16 + 8224)) [(o, 24)] M M').
    { apply (GK.hpres_scr L _ sp SCRT); [unfold SCRT; lia | exact S5 | lia | rewrite (PmLayout.ly_errno L LAY); lia | lia | lia | exact HP0]. }
    rewrite X, LS. eapply CL.ret_cps; [exact ret_at | exact (proj1 Hmo1) | exact (proj1 (proj2 Hmo1)) | |].
    { rewrite Hra'. apply Hoare.ret_ok_even. destruct Hraok as [R1' R2']. rewrite u64_of_Z by lia. exact R2'. }
    rewrite Hra'.
    apply (Hcont fx' R' M' m1 LB cr LB [(o, 24)] HFP); [| exact HRP | exact HP | exact Hbv1 | exact HH2].
    split; [|reflexivity]. split; [exact STR|]. split; [exact DEF|]. auto.
  - reflexivity.
  - (* [comment removed for export] *)
    rewrite LS.
    assert (Hds : L5.defined M (sp - 8304) 8304) by (intros i Hi; replace (sp - 8304 + i) with (sp - (256 + (16 + 8224)) + (i + 192)) by lia; apply S5; lia).
    assert (B0 : edenot E0 (EMd Instr.M_MUL (ELit 2) (EVar 32)) = Z_to_bv 64 (2 * n)).
    { rewrite <- (Z_to_bv_bv_unsigned _ (edenot E0 _)). f_equal. apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia]. }
    split; [exact (regs_ok_id R _ _)|]. unfold know_ok, S.cp0. cbn [CC.cp_know].
    repeat (apply Forall_cons); [.. | apply Forall_nil].
    + eapply GK.kword8_intro with (A := o) (z := 2 * n); [ev_start | lia | lia | exact B0 | lia | exact Hb0].
    + e_range. + e_range.
    + eapply CL5.kblob_intro with (bs := s) (A := o + 1); [ev_start | unfold elenZ; cbn [edenot]; exact U32 | lia | fold n; lia | lia | reflexivity | exact Hbs | fold n; intros j Hj; replace (o + 1 + j) with (o + (1 + j)) by lia; apply Hdo; lia].
    + e_unk. + e_wr. + e_range. + e_align O3.
    + e_unk. + e_wr. + e_range. + e_align S1.
    + e_disj.
  - (* [comment removed for export] *)
    split; [exact Hmo|]. split; [apply L5C.model_but_vm_refl|]. split; [apply CC.env_agree_refl|].
    split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
    exists cr. split; [|reflexivity]. unfold CH2.cur. change (nth 0 S.BLS []) with (@nil (expr * expr)). exact HH.
  - exact Hfp.
Qed.

Hypothesis OPNEWX : PMES.opnew_x_spec L HI.
Definition Cred (cr0 : credit) (i : nat) (E : env) (cr : credit) : Prop := cr = if pre i then cr0 else PMES.debit_k L cr0.

Lemma push_back_sso_full_x : forall (LB : list (Z * Z)) (cr : credit) (o c sp r : Z) (s : list Z),
  PML.cps_heap L HI PML.PC_STR_PUSH_BACK r sp PMS.STR_SCR LB cr
      (fun R M => Z.of_nat (length s) = 22 /\ PML.entry L R M sp r PMS.STR_SCR /\ PML.a0 R o /\ PML.a1 R c /\ 0 <= c < 256 /\ PML.str_at M o (PML.SShort s) /\
                  L5.defined M o 24 /\ PML.obj_on_stack L sp o 24 /\ hl_k_per_malloc L <= fst cr)
      (fun R M R' M' LB' cr' LBk W =>
         (exists p, PML.str_at M' o (PML.SLong 48 p (s ++ [c])) /\ L5.defined M' o 24 /\ L5C.fresh_block L LB M' p 48 /\
                    LB' = (p, 48) :: LB /\ cr' = PMES.debit_k L cr /\ LBk = LB) /\ W = [(o, 24)]).
Proof.
  intros LB cr o c sp r s. unfold PML.cps_heap.
  intros fx R M model K HH Hmo HKnil Hfp (H22 & Hentry & Ha0 & Ha1 & Hc & Hstr & Hdo & Hobj & Hcredit) Hcont.
  destruct Hentry as (Hra & Hraok & Hsp & Htp & Hstk). destruct Hstk as (S1 & S2 & S3 & S4 & S5).
  unfold PMS.STR_SCR, PMS.OPNEW_SCR, PML.HEAP_STACK in *.
  destruct Hstr as (Hlen22 & Hb0 & Hbs & Hnul).
  destruct Hobj as (O1 & O2 & O3).
  pose proof (PmLayout.ly_segs L LAY) as LS. pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI. pose proof (PmLayout.ly_stack L LAY) as LSTK. unfold PML.HEAP_STACK in LSTK.
  set (E0 := Env (reg_ev R (fun v => Z_to_bv 64 0)) (fun id => nth id [map (Z_to_bv 8) s] [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 PML.TP) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 o) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (V11 : ev E0 11 = Z_to_bv 64 c) by (rewrite <- Ha1; exact (EV 11%bv)).
  assert (CLO : 0x7fff7f800000 <= hl_ceil L) by lia.
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; lia).
  assert (U10 : bv_unsigned (ev E0 10) = o) by (rewrite V10; apply u64_of_Z; lia).
  assert (U11 : bv_unsigned (ev E0 11) = c) by (rewrite V11; apply u64_of_Z; lia).
  assert (FR : forall E1, env_agree GT.NF E0 E1 ->
            bv_unsigned (ev E1 2) = sp /\ bv_unsigned (ev E1 10) = o /\ bv_unsigned (ev E1 11) = c /\ eb E1 = eb E0).
  { intros E1 [A B]. rewrite <- !A by (unfold GT.NF; lia). repeat split; try assumption. symmetry. exact B. }
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= 0x7fff7f800000) by (rewrite ILO, IHI; lia).
  assert (LYE : hl_img_lo L <= hl_errno L /\ hl_errno L + 4 <= hl_img_hi L) by (rewrite ILO, IHI, (PmLayout.ly_errno L LAY); lia).
  assert (STKF : sp mod 16 = 0 /\ hl_ceil L + CH.hd_scr G.HDECL <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47)
    by (change (CH.hd_scr G.HDECL) with SCRT; unfold SCRT; repeat split; lia).
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (change (CH.hd_scr G.HDECL) with SCRT; unfold SCRT; lia).
  assert (NF32 : (32 <= GT.NF)%nat) by (unfold GT.NF; lia).
  assert (W_OK : forall (w : L5.range) (a : Z), In w [(o, 24)] -> L5.in_rng w a -> CH2.wclient L sp a).
  { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. split; [lia | left; lia]. }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> exists w : L5.range, In w [(o, 24)] /\ L5.in_rng w a)).
  { intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CH2.in_reg, estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha.
    rewrite U10 in Ha. rewrite u64_of_Z in Ha by lia. exists (o, 24). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia]. }
  unfold PML.cfg. change PML.PC_STR_PUSH_BACK with (CC.cp_pc G.cp0). rewrite <- LS.
  eapply CH2.heap_cert_sound with (NF := GT.NF) (E0 := E0) (M0 := M) (model0 := model) (LBrest := LB) (sp0 := sp) (d := G.HDECL)
    (W := [(o, 24)]) (BLS := G.BLS) (Cred := Cred cr) (CPS := G.CPS) (TAGS := G.TAGS) (RETS := G.RETS) (MALLOC := MALLOC) (FREE := FREE)
    (COPIES := [MEMMOVE]) (IMG_LO := GK.HULL_LO) (IMG_HI := GK.HULL_HI) (FPI := PML.fp_ok) (i := 0%nat) (E := E0) (HI := HI).
  - exact HIok.
  - exact LYI.
  - exact LYE.
  - exact (PmLayout.ly_ro L LAY).
  - rewrite LSTK. lia.
  - exact STKF.
  - exact SCRP.
  - rewrite LSTK. reflexivity.
  - exact NF32.
  - exact U2.
  - rewrite V4, (PmLayout.ly_tp L LAY). reflexivity.
  - exact W_OK.
  - intros rg [].
  - exact WRS_OK.
  - intros rg a [].
  - exact HKnil.
  - exact ILO.
  - exact IHI.
  - rewrite LS. exact FPM.
  - rewrite LS. exact G.plans.
  - exact G.tags_ok.
  - exact heap_ok_g.
  - exact (PmLayout.ly_malloc L LAY).
  - exact (PmLayout.ly_free L LAY).
  - intros pc [<-|[]]. exact (Pm6Memmove_u5.memmove_copy1 L LS).
  - intros i c0 kk ps j sg IL. exfalso. pose proof (CH2.leaves_all_sound _ _ _ no_goto_g _ _ _ _ _ IL) as X. cbv beta iota in X. discriminate X.
  - (* [comment removed for export] *)
    intros i c0 kk ps j cj IL Hret Hcj E E' R' M1 M1' cr' HagE Hag HLF HC. exfalso.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_g_ok _ _ _ _ _ IL) as X. unfold leaf_g in X.
    change (CH2.is_call MALLOC FREE [MEMMOVE] MALLOC) with true in X. cbv beta iota in X. rewrite Hret in X. rewrite Z.eqb_refl in X. discriminate X.
  - (* [comment removed for export] *)
    intros i c0 kk ps pc j cj IL Hcall Hnm Hret Hcj E E' R' M1 M1' cr' HagE Hag HLF HC E2 Hag2.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_g_ok _ _ _ _ _ IL) as X. unfold leaf_g in X. rewrite Hcall, Hret in X.
    apply andb_prop in X as [X Z1]. apply andb_prop in X as [_ XM]. apply negb_true_iff in XM, Z1.
    unfold Cred in *. rewrite Z1. rewrite XM in HC. exact HC.
  - (* [comment removed for export] *)
    intros i c0 kk ps pc IL Hnc.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_g_ok _ _ _ _ _ IL) as X. unfold leaf_g in X. rewrite Hnc in X.
    destruct (Z.eqb_spec pc OPNEW) as [->|Hno].
    { destruct (CH2.ret_of G.RETS i kk) as [j|] eqn:Hret; [|discriminate]. destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate].
      repeat (apply andb_prop in X as [X ?Y]). (* [comment removed for export] *)
      apply negb_true_iff in Y3. apply Z.eqb_eq in Y2. apply Nat.leb_le in Y1. apply expr_eqb_eq in Y0.
      destruct (EON.opnew_chk GT.NF G.HDECL c0 ps cj (nth i G.BLS []) (nth j G.BLS [])) as [ci|] eqn:Hchk; [|discriminate].
      set (XI := fun (_ : nat) (_ : env) (_ : PML.mem) => True).
      assert (DEF0 : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)).
      { change (CH.hd_scr G.HDECL) with SCRT. unfold SCRT. intros j0 Hj0. replace (sp - 8304 + j0) with (sp - (256 + (16 + 8224)) + (j0 + 192)) by lia. apply S5. lia. }
      assert (TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite V4, (PmLayout.ly_tp L LAY); reflexivity).
      assert (LO : CC.leaf_ok (hl_segs L) G.CPS (CH2.amb3 L HI GT.NF E0 M model LB sp G.HDECL [(o, 24)] G.BLS (Cred cr) XI) K PML.fp_ok i c0 ps).
      { apply (EON.opnew_leaf_ok L HI HIok LAY GT.NF E0 M model LB sp G.HDECL [(o, 24)] G.BLS (Cred cr) STKF SCRP NF32 U2 TP0 W_OK
                 ltac:(intros rg []) WRS_OK ltac:(intros rg a []) G.CPS G.TAGS G.RETS K HKnil XI DEF0 OPNEWX i c0 kk ps j cj ci IL Hret Hcj Y2 Hchk); [|intros; exact I].
        intros E E' R' M1 M1' cr1 HagE' Hag HLF HC. unfold Cred in HC. rewrite X in HC. subst cr1.
        rewrite Y0. unfold EON.uv, PB.uv. cbn [edenot]. rewrite u64_of_Z by lia.
        split; [lia|]. split; [exact Hcredit|]. intros E2 _. unfold Cred. rewrite Y3. reflexivity. }
      intros fx' E R1 M1 m1 E' R' M' HAt HAmb HFP Hag HLF HIH.
      apply (LO fx' E R1 M1 m1 E' R' M' HAt (conj HAmb I) HFP Hag HLF).
      intros j0 cj0 fx2 E2 R2 M2 model2 Hcj0 HAt2 [HA2 _] HFP2 Hlt. exact (HIH j0 cj0 fx2 E2 R2 M2 model2 Hcj0 HAt2 HA2 HFP2 Hlt). }
    cbv iota in X.
    intros fx' E R1 M1 m1 E' R' M' HAt HAmb HFP Hag HLF _. unfold exit_g in X.
    pose proof (CH2.exit_amb L HI HIok LYI LYE (PmLayout.ly_ro L LAY) GT.NF E0 M model LB sp G.HDECL [(o, 24)] G.BLS (Cred cr) STKF SCRP NF32 U2 W_OK WRS_OK
                  G.CPS GK.HULL_LO GK.HULL_HI G.TAGS G.RETS MALLOC FREE [MEMMOVE] heap_ok_g i c0 kk ps pc IL Hnc E E' R1 R' M1 M' m1 HAt HAmb Hag HLF) as HA'.
    repeat (apply andb_prop in X as [X ?Y]).
    (* [comment removed for export] *)
    apply Z.eqb_eq in X. apply Nat.leb_le in Y9. apply negb_true_iff in Y8. apply expr_eqb_eq in Y0.
    pose proof HA' as HA2. destruct HA' as (Hmo1 & Hbv1 & HagE1 & (cr1 & HH1 & HC1) & Hfr1 & Hdf1).
    assert (HagE' : env_agree GT.NF E0 E') by (eapply CC.env_agree_trans; [exact HagE1 | eapply CC.env_agree_le; [exact Hag | exact Y9]]).
    destruct (FR E' HagE') as (F2 & F10 & F11 & FB).
    rewrite LS in HLF.
    assert (CELL : forall X0, has (SR.ps_cells ps) X0 = true -> kentry_ok GK.RSEGS E' M' X0).
    { intros X0 HX. apply (CC.lf_cells _ _ _ _ _ _ _ HLF). exact (GK.has_In _ _ HX). }
    unfold hd_base, hd_size in *. destruct (nth i G.BLS []) as [|[pe ce] [|]] eqn:HBL; try discriminate Y7. cbn [hd fst snd] in *. subst ce.
    set (pX := bv_unsigned (edenot E' pe)) in *.
    assert (HH2 : hi_heap HI ((pX, 48) :: LB) cr1 M' (m_vmmaps m1)).
    { unfold CH2.cur in HH1. rewrite HBL in HH1. rewrite <- (CH2.den_agree _ E E' _ Hag Y10) in HH1. exact HH1. }
    destruct (hio_wf L SCFG HI HIok _ _ _ _ HH2) as (Hwf2 & Hnd2 & _).
    destruct (Hwf2 (pX, 48) (or_introl eq_refl)) as ((Q0 & Q1 & Q2 & Q3 & Q4) & Qdef & Qap). cbn [fst snd lb_remove] in Q0, Q1, Q2, Q3, Q4, Qdef, Qap. rewrite Z.eqb_refl in Qap.
    (* [comment removed for export] *)
    assert (W0 : L5.u64_at GK.RSEGS M' o 49).
    { apply (CL5.kword64_elim GK.RSEGS E' M' _ _ o _ (CELL _ Y6)); [unfold estart, e_o; cbn [a_base a_off edenot]; rewrite F10; lia | cbn [edenot]; apply u64_of_Z; lia]. }
    assert (W8 : L5.u64_at GK.RSEGS M' (o + 8) 23).
    { apply (CL5.kword64_elim GK.RSEGS E' M' _ _ (o + 8) _ (CELL _ Y5)); [unfold estart, e_o; cbn [a_base a_off edenot]; rewrite F10; lia | cbn [edenot]; apply u64_of_Z; lia]. }
    assert (W16 : L5.u64_at GK.RSEGS M' (o + 16) pX).
    { apply (CL5.kword64_elim GK.RSEGS E' M' _ _ (o + 16) _ (CELL _ Y4)); [unfold estart, e_o; cbn [a_base a_off edenot]; rewrite F10; lia | reflexivity]. }
    assert (BS : L5.bytes_at GK.RSEGS M' pX s).
    { apply (CL5.kblob_elim GK.RSEGS E' M' _ _ 0%nat pX s (CELL _ Y3)); [unfold estart; cbn [a_base a_off]; fold pX; lia | rewrite FB; reflexivity]. }
    assert (BC : L5.u8_at GK.RSEGS M' (pX + 22) c).
    { apply (GK.kword8_elim E' M' _ _ (pX + 22) c (CELL _ Y2)); [unfold estart; cbn [a_base a_off]; fold pX; lia | exact F11]. }
    assert (NUL : L5.u8_at GK.RSEGS M' (pX + 23) 0).
    { apply (CL5.kword8_zero_elim GK.RSEGS E' M' _ _ (CELL _ Y1)). unfold estart. cbn [a_base a_off]. fold pX. lia. }
    assert (LEN : Z.of_nat (length (s ++ [c])) = 23) by (rewrite length_app, Nat2Z.inj_add; cbn [length]; lia).
    assert (STR : PML.str_at M' o (PML.SLong 48 pX (s ++ [c]))).
    { split; [|split; [reflexivity | rewrite LEN; lia]]. unfold L5.lstr_long. rewrite LEN.
      split; [reflexivity|]. split; [exact W0|]. split; [exact W8|]. split; [exact W16|]. split; [|exact NUL].
      apply CL5.bytes_at_app; [exact BS|]. intros j Hj. cbn [length] in Hj. assert (j = 0%nat) by lia. subst j. cbn [nth]. rewrite Z.add_0_r.
      replace (pX + Z.of_nat (length s)) with (pX + 22) by lia. exact BC. }
    assert (DEF : L5.defined M' o 24).
    { intros j Hj. pose proof (Hdf1 (o + j) ltac:(lia)) as D. rewrite <- (Z_to_bv_bv_unsigned _ (Z_to_bv 64 (o + j))). rewrite u64_of_Z by lia.
      apply D; [| exact (Hdo j Hj)]. split; [right; left; split; lia | unfold in_errno; rewrite (PmLayout.ly_errno L LAY); lia]. }
    (* [comment removed for export] *)
    assert (KEEP : forall y : reg, In (ridx y) CSAVED -> getr R' y = getr R y).
    { intros y Hy. assert (Hy32 : (ridx y < GT.NF)%nat) by (unfold CSAVED, CL5.CSAVED in Hy; cbn [In] in Hy; unfold GT.NF; intuition lia).
      rewrite (CL.ps_keeps_sound GK.RSEGS c0 ps E0 E' R' M1 M' CSAVED GT.NF y HLF Y11 HagE' Hy Hy32). exact (EV y). }
    assert (HRP : regs_preserved R R') by (intros y Hy; apply KEEP; exact (CL5.csaved_in y Hy)).
    assert (Hra' : getr R' 1%bv = Z_to_bv 64 r) by (rewrite (KEEP 1%bv ltac:(left; reflexivity)); exact Hra).
    assert (Hds : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)).
    { change (CH.hd_scr G.HDECL) with SCRT. unfold SCRT. intros j Hj. replace (sp - 8304 + j) with (sp - (256 + (16 + 8224)) + (j + 192)) by lia. apply S5. lia. }
    pose proof (CH2.amb_hpres L HI LYI LYE GT.NF E0 M model LB sp G.HDECL [(o, 24)] G.BLS (Cred cr) STKF NF32 i E M' m1 HA2 Hds) as HP0.
    change (CH.hd_scr G.HDECL) with SCRT in HP0.
    assert (HP : L5C.hpres L LB sp (256 + (16 + 8224)) [(o, 24)] M M').
    { apply (GK.hpres_scr L _ sp SCRT); [unfold SCRT; lia | exact S5 | lia | rewrite (PmLayout.ly_errno L LAY); lia | lia | lia | exact HP0]. }
    rewrite X, LS. eapply CL.ret_cps; [exact ret_at | exact (proj1 Hmo1) | exact (proj1 (proj2 Hmo1)) | |].
    { rewrite Hra'. apply Hoare.ret_ok_even. destruct Hraok as [R1' R2']. rewrite u64_of_Z by lia. exact R2'. }
    rewrite Hra'.
    assert (Hcr : cr1 = PMES.debit_k L cr) by (unfold Cred in HC1; rewrite Y8 in HC1; exact HC1).
    subst cr1.
    apply (Hcont fx' R' M' m1 ((pX, 48) :: LB) (PMES.debit_k L cr) LB [(o, 24)] HFP); [| exact HRP | exact HP | exact Hbv1 | exact HH2].
    split; [|reflexivity]. exists pX.
    split; [exact STR|]. split; [exact DEF|]. split; [|auto]. split; [repeat split; assumption|]. split; [|exact Qdef].
    intros b0 Hb0x. destruct b0 as [bb bm]. exact (Qap (bb, bm) Hb0x).
  - reflexivity.
  - (* [comment removed for export] *)
    rewrite LS.
    assert (Hds : L5.defined M (sp - 8304) 8304) by (intros i Hi; replace (sp - 8304 + i) with (sp - (256 + (16 + 8224)) + (i + 192)) by lia; apply S5; lia).
    assert (B0 : edenot E0 (ELit 44) = Z_to_bv 64 44) by reflexivity.
    split; [exact (regs_ok_id R _ _)|]. unfold know_ok, G.cp0. cbn [CC.cp_know].
    repeat (apply Forall_cons); [.. | apply Forall_nil].
    + eapply GK.kword8_intro with (A := o) (z := 44); [ev_start | lia | lia | exact B0 | lia | replace 44 with (2 * Z.of_nat (length s)) by lia; exact Hb0].
    + e_range.
    + eapply CL5.kblob_intro with (bs := s) (A := o + 1); [ev_start | unfold elenZ; cbn [edenot]; rewrite H22; apply u64_of_Z; lia | lia | lia | lia | reflexivity | exact Hbs | intros j Hj; replace (o + 1 + j) with (o + (1 + j)) by lia; apply Hdo; lia].
    + e_unk. + e_wr. + e_range. + e_align O3.
    + e_unk. + e_wr. + e_range. + e_align S1.
    + e_disj.
  - (* [comment removed for export] *)
    split; [exact Hmo|]. split; [apply L5C.model_but_vm_refl|]. split; [apply CC.env_agree_refl|].
    split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
    exists cr. split; [|reflexivity]. unfold CH2.cur. change (nth 0 G.BLS []) with (@nil (expr * expr)). exact HH.
  - exact Hfp.
Qed.
End PushBackS.
End EPS.
