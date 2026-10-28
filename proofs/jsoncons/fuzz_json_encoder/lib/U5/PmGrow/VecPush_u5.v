(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutL5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Cut_vec_push_grow_xsrc_T_u5 Cut_vec_push_grow_xsrc_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmGrow Require Import GrowKit_u5 VecPushFast_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module VP.
Module G := Cut_vec_push_grow_xsrc_u5.   Module GT := Cut_vec_push_grow_xsrc_T_u5.
Definition MALLOC : Z := PML.PC_MALLOC.  Definition FREE : Z := PML.PC_FREE.
Definition RET : Z := Eval vm_compute in hd 0 GT.ENDS.
Definition SCRT : Z := Eval vm_compute in CH.hd_scr G.HDECL.       (* [comment removed for export] *)
Definition CSAVED := CL5.CSAVED.
Definition has := GK.has.

Lemma heap_ok_g : CH2.heap_chk GT.NF G.HDECL G.BLS G.CPS GK.HULL_LO GK.HULL_HI G.TAGS G.RETS MALLOC FREE [] = true.
Proof. vm_compute. reflexivity. Qed.
Lemma no_goto_g : CH2.leaves_all G.CPS G.TAGS (fun _ _ _ _ t => match t with CC.TGoto _ _ => false | CC.TOther _ => true end) = true.
Proof. vm_compute. reflexivity. Qed.

Definition e_o := EVar 10.  Definition e_b := EVar 32.  Definition e_cap := EVar 34.  Definition e_x := EVar 35.

(* [comment removed for export] *)
Definition pre (i : nat) : bool := Nat.eqb i 0.
Definition hd_base (i : nat) : expr := fst (hd (ELit 0, ELit 0) (nth i G.BLS [])).
Definition hd_size (i : nat) : expr := snd (hd (ELit 0, ELit 0) (nth i G.BLS [])).
Definition CAP2 : expr := EMd M_MUL (ELit 2) e_cap.
Definition CAP1 : expr := EAlu ALU_ADD e_cap (ELit 1).
Definition arm_chk (cells : list kentry) (e : expr) : bool :=
  (expr_eqb e CAP2 || (expr_eqb e CAP1 && has cells (KRange (EAlu ALU_SLTU CAP1 CAP2) 0 0)))%bool.
Definition exit_g (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) : bool :=
  let cells := SR.ps_cells ps in let pe := hd_base i in let ce := hd_size i in
  (CL.ps_at ps [RET] && CL.ps_keeps ps CSAVED && CH2.blocks_vars_lt (CC.cp_nx c) (nth i G.BLS []) && Nat.leb GT.NF (CC.cp_nx c)
   && negb (pre i) && match nth i G.BLS [] with [_] => true | _ => false end
   && has cells (KWord (SA e_o 0) 8 pe) && has cells (KWord (SA e_o 8) 8 (APC.eaddz (APC.eadd e_cap pe) 1)) && has cells (KWord (SA e_o 16) 8 (APC.eadd ce pe))
   && has cells (KBlob (SA pe 0) e_cap 0) && has cells (KWord (SA (APC.eadd e_cap pe) 0) 1 e_x)
   && arm_chk cells ce && has cells (KDisj (SA pe 0) ce (SA e_b 0) e_cap)
   && match pe with EVar v => Nat.leb GT.NF v | _ => false end)%bool.
Definition leaf_g (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      if CH2.is_call MALLOC FREE [] pc then
        match CH2.ret_of G.RETS i k with
        | Some j =>
            match nth_error G.CPS j with
            | Some cj =>
                (Nat.leb GT.NF (CC.cp_nx c) && Nat.leb (CC.cp_nx c) (CC.cp_nx cj - APC.NCS)
                 && if Z.eqb pc MALLOC then (pre i && negb (pre j) && expr_eqb (hd_size j) (CA.ps_reg ps 10) && APC.expr_vars_lt GT.NF (hd_size j) && arm_chk (SR.ps_cells ps) (hd_size j))
                    else (negb (pre i) && negb (pre j) && expr_eqb (hd_size i) (hd_size j) && APC.expr_vars_lt GT.NF (hd_size i)))%bool
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

Section VecPushOk.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps GK.RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom GK.RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom GK.RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.


(* [comment removed for export] *)
Definition Cred (cr0 : credit) (i : nat) (E : env) (cr : credit) : Prop :=
  cr = if pre i then cr0 else debit L cr0 (snd (hd (0, 0) (CH2.den E (nth i G.BLS [])))).

Lemma vec_push_grow : forall (LB : list (Z * Z)) (cr : credit) (o b cap xa x sp r : Z) (st : list Z),
  PML.cps_heap L HI PML.PC_VEC_PUSH r sp PMS.VEC_SCR LB cr
      (fun R M => Z.of_nat (length st) = cap /\ PML.entry L R M sp r PMS.VEC_SCR /\ PML.a0 R o /\ PML.a1 R xa /\ PML.u8 M xa x /\ sp <= xa < hl_sptop L /\
                  PML.u64 M o b /\ PML.u64 M (o + 8) (b + cap) /\ PML.u64 M (o + 16) (b + cap) /\ L5.bytes_at GK.RSEGS M b st /\
                  In (b, cap) LB /\ (length st <= 1026)%nat /\ PML.obj_on_stack L sp o 24 /\ credit_ok L cr (2 * cap))
      (fun R M R' M' LB' cr' LBk W => W = [(o, 24)] /\
          (Z.of_nat (length st) = cap /\ exists b', PML.u64 M' o b' /\ PML.u64 M' (o + 8) (b' + cap + 1) /\ PML.u64 M' (o + 16) (b' + 2 * cap) /\
            L5.bytes_at GK.RSEGS M' b' (st ++ [x]) /\ L5C.fresh_block L LB M' b' (2 * cap) /\
            LB' = (b', 2 * cap) :: lb_remove b LB /\ cr' = debit L cr (2 * cap) /\ LBk = lb_remove b LB)).
Proof.
  intros LB cr o b cap xa x sp r st. unfold PML.cps_heap.
  intros fx R M model K HH Hmo HKnil Hfp (Heq & Hentry & Ha0 & Ha1 & Hx & Hxa & Hw0 & Hw8 & Hw16 & Hbs & HinLB & Hlen & Hobj & Hcredit) Hcont.
  destruct Hentry as (Hra & Hraok & Hsp & Htp & Hstk). destruct Hstk as (S1 & S2 & S3 & S4 & S5).
  unfold PMS.VEC_SCR, PMS.OPNEW_SCR, PML.HEAP_STACK in *. unfold PML.u64, PML.u8 in *.
  destruct Hobj as (O1 & O2 & O3).
  pose proof (PmLayout.ly_segs L LAY) as LS. pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI. pose proof (PmLayout.ly_stack L LAY) as LSTK. unfold PML.HEAP_STACK in LSTK.
  destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hwf & Hnd & _).
  destruct (Hwf _ HinLB) as ((P0 & P1 & P2 & P3 & P4) & Pdef & Pap). cbn [fst snd] in *.
  pose proof (CH2.heap_own_front L HI HIok LB cr M _ b cap HH HinLB) as HH'.
  set (xb := x mod 256). assert (Hxb : 0 <= xb < 256) by (unfold xb; apply Z.mod_pos_bound; lia).
  assert (Hx' : L5.u8_at GK.RSEGS M xa xb) by (apply (proj1 (GK.u8_at_mod M xa x)); exact Hx).
  assert (Hcap : 1 <= cap <= 1026) by lia.
  set (E0 := Env (reg_ev R (fun v => Z_to_bv 64 (nth (v - 32) [b; cap; cap; xb] 0))) (fun id => nth id [map (Z_to_bv 8) st] [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 PML.TP) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 o) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (V11 : ev E0 11 = Z_to_bv 64 xa) by (rewrite <- Ha1; exact (EV 11%bv)).
  assert (V32 : ev E0 32 = Z_to_bv 64 b) by reflexivity.
  assert (V34 : ev E0 34 = Z_to_bv 64 cap) by reflexivity.
  assert (V35 : ev E0 35 = Z_to_bv 64 xb) by reflexivity.
  assert (CLO : 0x7fff7f800000 <= hl_ceil L) by lia.
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; lia).
  assert (U10 : bv_unsigned (ev E0 10) = o) by (rewrite V10; apply u64_of_Z; lia).
  assert (U11 : bv_unsigned (ev E0 11) = xa) by (rewrite V11; apply u64_of_Z; lia).
  assert (U32 : bv_unsigned (ev E0 32) = b) by (rewrite V32; apply u64_of_Z; lia).
  assert (U34 : bv_unsigned (ev E0 34) = cap) by (rewrite V34; apply u64_of_Z; lia).
  assert (U35 : bv_unsigned (ev E0 35) = xb) by (rewrite V35; apply u64_of_Z; lia).
  assert (FR : forall E1, env_agree GT.NF E0 E1 ->
            bv_unsigned (ev E1 2) = sp /\ bv_unsigned (ev E1 10) = o /\ bv_unsigned (ev E1 11) = xa /\
            bv_unsigned (ev E1 32) = b /\ bv_unsigned (ev E1 34) = cap /\ bv_unsigned (ev E1 35) = xb /\ eb E1 = eb E0).
  { intros E1 [A B]. rewrite <- !A by (unfold GT.NF; lia). repeat split; try assumption. symmetry. exact B. }
  (* [comment removed for export] *)
  assert (ARM : forall E1 M1 cells e, env_agree GT.NF E0 E1 -> (forall K0, In K0 cells -> kentry_ok GK.RSEGS E1 M1 K0) -> arm_chk cells e = true ->
            bv_unsigned (edenot E1 e) = 2 * cap).
  { intros E1 M1 cells e Hag1 Hc Harm. destruct (FR E1 Hag1) as (F2 & F10 & F11 & F32 & F34 & F35 & _).
    unfold arm_chk, CAP1, CAP2, e_cap in Harm.
    assert (U1 : bv_unsigned (edenot E1 (EAlu ALU_ADD (EVar 34) (ELit 1))) = cap + 1) by (apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia]).
    assert (U2' : bv_unsigned (edenot E1 (EMd M_MUL (ELit 2) (EVar 34))) = 2 * cap) by (apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia]).
    apply orb_prop in Harm as [He|Harm]; [apply expr_eqb_eq in He; subst e; exact U2'|].
    apply andb_prop in Harm as [He Hf]. apply expr_eqb_eq in He. subst e. rewrite U1.
    pose proof (Hc _ (GK.has_In _ _ Hf)) as G0. cbn [kentry_ok] in G0. cbn [edenot] in G0. rewrite u_sltu64 in G0. cbn [edenot] in U1, U2'. rewrite U1, U2' in G0.
    destruct (Z.ltb_spec (cap + 1) (2 * cap)); lia. }
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
  unfold PML.cfg. change PML.PC_VEC_PUSH with (CC.cp_pc G.cp0). rewrite <- LS.
  eapply CH2.heap_cert_sound with (NF := GT.NF) (E0 := E0) (M0 := M) (model0 := model) (LBrest := lb_remove b LB) (sp0 := sp) (d := G.HDECL)
    (W := [(o, 24)]) (BLS := G.BLS) (Cred := Cred cr) (CPS := G.CPS) (TAGS := G.TAGS) (RETS := G.RETS) (MALLOC := MALLOC) (FREE := FREE)
    (COPIES := []) (IMG_LO := GK.HULL_LO) (IMG_HI := GK.HULL_HI) (FPI := PML.fp_ok) (i := 0%nat) (E := E0) (HI := HI).
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
  - intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CH2.in_reg, estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha.
    rewrite U11 in Ha. rewrite u64_of_Z in Ha by lia. split; [lia|]. left. lia.
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
  - intros pc [].
  - intros i c kk ps j sg IL. exfalso. pose proof (CH2.leaves_all_sound _ _ _ no_goto_g _ _ _ _ _ IL) as X. cbv beta iota in X. discriminate X.
  - (* [comment removed for export] *)
    intros i c kk ps j cj IL Hret Hcj E E' R' M1 M1' cr' HagE Hag HLF HC.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_g_ok _ _ _ _ _ IL) as X. unfold leaf_g in X.
    change (CH2.is_call MALLOC FREE [] MALLOC) with true in X. cbv beta iota in X. rewrite Hret, Hcj in X. change (Z.eqb MALLOC MALLOC) with true in X. cbv beta iota in X.
    apply andb_prop in X as [X XM]. apply andb_prop in X as [XA XB]. apply Nat.leb_le in XA, XB.
    repeat (apply andb_prop in XM as [XM ?Z]). apply expr_eqb_eq in Z1. apply negb_true_iff in Z2.
    assert (HagE' : env_agree GT.NF E0 E') by (eapply CC.env_agree_trans; [exact HagE | eapply CC.env_agree_le; [exact Hag | exact XA]]).
    rewrite LS in HLF. pose proof (ARM E' M1' (SR.ps_cells ps) (hd_size j) HagE' (CC.lf_cells _ _ _ _ _ _ _ HLF) Z) as Hval.
    unfold Cred in HC. rewrite XM in HC. subst cr'. rewrite <- Z1. rewrite Hval. split; [exact Hcredit|].
    intros E2 Hag2. unfold Cred. rewrite Z2. rewrite GK.den_hd. fold (hd_size j). f_equal. rewrite <- Hval.
    f_equal. apply (SR.edenot_agree_AP GT.NF E' E2); [eapply CC.env_agree_le; [exact Hag2 | lia] | exact Z0].
  - (* [comment removed for export] *)
    intros i c kk ps pc j cj IL Hcall Hnm Hret Hcj E E' R' M1 M1' cr' HagE Hag HLF HC E2 Hag2.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_g_ok _ _ _ _ _ IL) as X. unfold leaf_g in X. rewrite Hcall, Hret, Hcj in X.
    destruct (Z.eqb_spec pc MALLOC) as [->|_]; [contradiction|].
    apply andb_prop in X as [X XM]. apply andb_prop in X as [XA XB]. apply Nat.leb_le in XA, XB.
    repeat (apply andb_prop in XM as [XM ?Z]). apply negb_true_iff in XM, Z1. apply expr_eqb_eq in Z0.
    unfold Cred in *. rewrite Z1. rewrite XM in HC. rewrite HC. f_equal. rewrite !GK.den_hd. fold (hd_size i) (hd_size j). rewrite <- Z0. f_equal.
    apply (SR.edenot_agree_AP GT.NF E E2); [|exact Z].
    eapply CC.env_agree_trans; [eapply CC.env_agree_le; [exact Hag | exact XA] | eapply CC.env_agree_le; [exact Hag2 | lia]].
  - (* [comment removed for export] *)
    intros i c kk ps pc IL Hnc fx' E R1 M1 m1 E' R' M' HAt HAmb HFP Hag HLF _.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_g_ok _ _ _ _ _ IL) as X. unfold leaf_g in X. rewrite Hnc in X. unfold exit_g in X.
    pose proof (CH2.exit_amb L HI HIok LYI LYE (PmLayout.ly_ro L LAY) GT.NF E0 M model (lb_remove b LB) sp G.HDECL [(o, 24)] G.BLS (Cred cr) STKF SCRP NF32 U2 W_OK WRS_OK
                  G.CPS GK.HULL_LO GK.HULL_HI G.TAGS G.RETS MALLOC FREE [] heap_ok_g i c kk ps pc IL Hnc E E' R1 R' M1 M' m1 HAt HAmb Hag HLF) as HA'.
    repeat (apply andb_prop in X as [X ?Y]).
    (* [comment removed for export] *)
    apply Z.eqb_eq in X. apply Nat.leb_le in Y9. apply negb_true_iff in Y8.
    pose proof HA' as HA2. destruct HA' as (Hmo1 & Hbv1 & HagE1 & (cr1 & HH1 & HC1) & Hfr1 & Hdf1).
    assert (HagE' : env_agree GT.NF E0 E') by (eapply CC.env_agree_trans; [exact HagE1 | eapply CC.env_agree_le; [exact Hag | exact Y9]]).
    destruct (FR E' HagE') as (F2 & F10 & F11 & F32 & F34 & F35 & FB).
    rewrite LS in HLF.
    assert (CELL : forall X0, has (SR.ps_cells ps) X0 = true -> kentry_ok GK.RSEGS E' M' X0).
    { intros X0 HX. apply (CC.lf_cells _ _ _ _ _ _ _ HLF). exact (GK.has_In _ _ HX). }
    unfold hd_base, hd_size in *. destruct (nth i G.BLS []) as [|[pe ce] [|]] eqn:HBL; try discriminate Y7. cbn [hd fst snd] in *.
    set (pX := bv_unsigned (edenot E' pe)) in *. set (capX := bv_unsigned (edenot E' ce)) in *.
    assert (HcapX : capX = 2 * cap) by (exact (ARM E' M' (SR.ps_cells ps) ce HagE' (CC.lf_cells _ _ _ _ _ _ _ HLF) Y1)).
    assert (HH2 : hi_heap HI ((pX, capX) :: lb_remove b LB) cr1 M' (m_vmmaps m1)).
    { unfold CH2.cur in HH1. rewrite HBL in HH1. rewrite <- (CH2.den_agree _ E E' _ Hag Y10) in HH1. exact HH1. }
    destruct (hio_wf L SCFG HI HIok _ _ _ _ HH2) as (Hwf2 & Hnd2 & _).
    destruct (Hwf2 (pX, capX) (or_introl eq_refl)) as ((Q0 & Q1 & Q2 & Q3 & Q4) & Qdef & Qap). cbn [fst snd lb_remove] in Q0, Q1, Q2, Q3, Q4, Qdef, Qap. rewrite Z.eqb_refl in Qap.
    (* [comment removed for export] *)
    assert (UA : forall e1 e2, bv_unsigned (edenot E' (APC.eadd e1 e2)) = (bv_unsigned (edenot E' e1) + bv_unsigned (edenot E' e2)) mod 2 ^ 64).
    { intros e1 e2. unfold APC.eadd. rewrite mkAlu_denot, u_add64. reflexivity. }
    assert (UCP : bv_unsigned (edenot E' (APC.eadd e_cap pe)) = cap + pX).
    { rewrite UA. unfold e_cap. cbn [edenot]. rewrite F34. fold pX. apply Z.mod_small. lia. }
    assert (UCP1 : bv_unsigned (edenot E' (APC.eaddz (APC.eadd e_cap pe) 1)) = cap + pX + 1).
    { unfold APC.eaddz. rewrite mkAlu_denot, u_add64. rewrite UCP. cbn [edenot]. rewrite (u64_of_Z 1) by lia. apply Z.mod_small. lia. }
    assert (UCE : bv_unsigned (edenot E' (APC.eadd ce pe)) = capX + pX).
    { rewrite UA. fold pX capX. apply Z.mod_small. lia. }
    assert (W0 : L5.u64_at GK.RSEGS M' o pX).
    { apply (CL5.kword64_elim GK.RSEGS E' M' _ _ o _ (CELL _ Y6)); [unfold estart, e_o; cbn [a_base a_off edenot]; rewrite F10; lia | reflexivity]. }
    assert (W8 : L5.u64_at GK.RSEGS M' (o + 8) (pX + cap + 1)).
    { apply (CL5.kword64_elim GK.RSEGS E' M' _ _ (o + 8) _ (CELL _ Y5)); [unfold estart, e_o; cbn [a_base a_off edenot]; rewrite F10; lia | rewrite UCP1; lia]. }
    assert (W16 : L5.u64_at GK.RSEGS M' (o + 16) (pX + 2 * cap)).
    { apply (CL5.kword64_elim GK.RSEGS E' M' _ _ (o + 16) _ (CELL _ Y4)); [unfold estart, e_o; cbn [a_base a_off edenot]; rewrite F10; lia | rewrite UCE; lia]. }
    assert (BS : L5.bytes_at GK.RSEGS M' pX st).
    { apply (CL5.kblob_elim GK.RSEGS E' M' _ _ 0%nat pX st (CELL _ Y3)); [unfold estart; cbn [a_base a_off]; fold pX; lia | rewrite FB; reflexivity]. }
    assert (BX : L5.u8_at GK.RSEGS M' (pX + cap) x).
    { apply (proj2 (GK.u8_at_mod M' (pX + cap) x)). fold xb. apply (GK.kword8_elim E' M' _ _ (pX + cap) xb (CELL _ Y2)); [unfold estart; cbn [a_base a_off]; rewrite UCP; lia | exact F35]. }
    assert (BSX : L5.bytes_at GK.RSEGS M' pX (st ++ [x])).
    { apply CL5.bytes_at_app; [exact BS|]. intros j Hj. cbn [length] in Hj. assert (j = 0%nat) by lia. subst j. cbn [nth]. rewrite Z.add_0_r, Heq. exact BX. }
    (* [comment removed for export] *)
    assert (KEEP : forall y : reg, In (ridx y) CSAVED -> getr R' y = getr R y).
    { intros y Hy. assert (Hy32 : (ridx y < GT.NF)%nat) by (unfold CSAVED, CL5.CSAVED in Hy; cbn [In] in Hy; unfold GT.NF; intuition lia).
      rewrite (CL.ps_keeps_sound GK.RSEGS c ps E0 E' R' M1 M' CSAVED GT.NF y HLF Y11 HagE' Hy Hy32). exact (EV y). }
    assert (HRP : regs_preserved R R') by (intros y Hy; apply KEEP; exact (CL5.csaved_in y Hy)).
    assert (Hra' : getr R' 1%bv = Z_to_bv 64 r) by (rewrite (KEEP 1%bv ltac:(left; reflexivity)); exact Hra).
    assert (Hds : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)).
    { change (CH.hd_scr G.HDECL) with SCRT. eapply (L5.defined_sub _ _ _ _ _ S5); unfold SCRT; lia. }
    pose proof (CH2.amb_hpres L HI LYI LYE GT.NF E0 M model (lb_remove b LB) sp G.HDECL [(o, 24)] G.BLS (Cred cr) STKF NF32 i E M' m1 HA2 Hds) as HP0.
    change (CH.hd_scr G.HDECL) with SCRT in HP0.
    assert (HP : L5C.hpres L (lb_remove b LB) sp (128 + (16 + 8224)) [(o, 24)] M M').
    { apply (GK.hpres_scr L _ sp SCRT); [unfold SCRT; lia | exact S5 | lia | rewrite (PmLayout.ly_errno L LAY); lia | lia | lia | exact HP0]. }
    rewrite X, LS. eapply CL.ret_cps; [exact ret_at | exact (proj1 Hmo1) | exact (proj1 (proj2 Hmo1)) | |].
    { rewrite Hra'. apply Hoare.ret_ok_even. destruct Hraok as [R1' R2']. rewrite u64_of_Z by lia. exact R2'. }
    rewrite Hra'.
    assert (Hcr : cr1 = debit L cr capX).
    { unfold Cred in HC1. rewrite Y8 in HC1. rewrite HC1. f_equal. rewrite GK.den_hd, HBL. cbn [hd snd]. unfold capX. f_equal.
      apply (SR.edenot_agree_AP (CC.cp_nx c) E E' ce Hag). unfold CH2.blocks_vars_lt in Y10. cbn [forallb fst snd] in Y10. apply andb_prop in Y10 as [Y10 _]. apply andb_prop in Y10 as [_ Y10]. exact Y10. }
    subst cr1.
    assert (Hdisj : pX + capX <= b \/ b + cap <= pX).
    { pose proof (CELL _ Y0) as G0. cbn [kentry_ok] in G0. unfold estart, elenZ in G0. cbn [a_base a_off] in G0. fold pX capX in G0.
      unfold e_b, e_cap in G0. cbn [edenot] in G0. rewrite F32, F34 in G0. lia. }
    rewrite HcapX in *.
    apply (Hcont fx' R' M' m1 ((pX, 2 * cap) :: lb_remove b LB) (debit L cr (2 * cap)) (lb_remove b LB) [(o, 24)] HFP); [| exact HRP | exact HP | exact Hbv1 | exact HH2].
    split; [reflexivity|]. split; [exact Heq|]. exists pX. split; [exact W0|]. split; [exact W8|]. split; [exact W16|]. split; [exact BSX|].
    split; [|auto]. split; [repeat split; assumption|]. split; [|exact Qdef].
    intros b0 Hb0. destruct (Z.eq_dec (fst b0) b) as [e0|ne0].
    * rewrite (CH2.nodup_fst_eq LB b0 (b, cap) Hnd Hb0 HinLB e0). cbn [fst snd]. exact Hdisj.
    * destruct b0 as [bb bm]. exact (Qap (bb, bm) (L5C.in_lb_remove_neq b bb bm LB Hb0 ne0)).
  - reflexivity.
  - (* [comment removed for export] *)
    rewrite LS.
    assert (Hdo : L5.defined M o 24).
    { apply GK.defined_3x8; [exact (GK.defined_of_u64 M o _ Hw0 ltac:(unfold GK.HULL_HI; lia) ltac:(lia)) | exact (GK.defined_of_u64 M (o + 8) _ Hw8 ltac:(unfold GK.HULL_HI; lia) ltac:(lia))
                            | exact (GK.defined_of_u64 M (o + 16) _ Hw16 ltac:(unfold GK.HULL_HI; lia) ltac:(lia))]. }
    assert (Hdb : L5.defined M b cap) by exact Pdef.
    assert (WC : edenot E0 (EAlu Instr.ALU_ADD (EVar 32) (EVar 34)) = Z_to_bv 64 (b + cap)).
    { rewrite <- (Z_to_bv_bv_unsigned _ (edenot E0 _)). f_equal. apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia]. }
    split; [exact (regs_ok_id R _ _)|]. unfold know_ok, G.cp0. cbn [CC.cp_know].
    repeat (apply Forall_cons); [.. | apply Forall_nil].
    + eapply CL5.kword64_intro with (A := o) (z := b); [ev_start | lia | lia | exact V32 | exact Hw0].
    + eapply CL5.kword64_intro with (A := o + 8) (z := b + cap); [ev_start | lia | lia | exact WC | exact Hw8].
    + eapply CL5.kword64_intro with (A := o + 16) (z := b + cap); [ev_start | lia | lia | exact WC | exact Hw16].
    + e_range.
    + eapply GK.kword8_intro with (A := xa) (z := xb); [ev_start | lia | lia | exact V35 | lia | exact Hx'].
    + e_range. + e_range.
    + eapply CL5.kblob_intro with (bs := st) (A := b); [ev_start | unfold elenZ; cbn [edenot]; rewrite U34; lia | lia | lia | lia | reflexivity | exact Hbs | rewrite Heq; ev_def].
    + e_unk. + e_wr. + e_range. + e_align P2.
    + e_wr. + e_range. + e_align O3.
    + e_unk. + e_wr. + e_range. + e_align S1.
    + e_disj. + e_disj. + e_disj. + e_disj. + e_disj.
  - (* [comment removed for export] *)
    split; [exact Hmo|]. split; [apply L5C.model_but_vm_refl|]. split; [apply CC.env_agree_refl|].
    split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
    exists cr. split; [|reflexivity]. unfold CH2.cur.
    replace (CH2.den E0 (nth 0 G.BLS [])) with [(b, cap)]; [exact HH'|].
    change (nth 0 G.BLS []) with [(EVar 32, EVar 34)]. unfold CH2.den. cbn [map fst snd edenot]. rewrite U32, U34. reflexivity.
  - exact Hfp.
Qed.

(* [comment removed for export] *)
Theorem vec_push_ok : PMS.vec_push_spec L HI.
Proof.
  intros LB cr o b cap xa x sp r st. unfold PML.cps_heap.
  intros fx R M model K HH Hmo HKnil Hfp (Hentry & Ha0 & Ha1 & Hx & Hxa & Hw0 & Hw8 & Hw16 & Hbs & HinLB & Hle & Hlen & Hobj & Hcredit) Hcont.
  destruct (Z_lt_le_dec (Z.of_nat (length st)) cap) as [Hlt|Hge].
  - apply (VPF.vec_push_fast L HI HIok LAY FPM LB cr o b cap xa x sp r st fx R M model K HH Hmo HKnil Hfp); [repeat (split; [assumption|]); assumption|].
    intros fx' R' M' model' LB' cr' LBk W HFP (HW & Hpost) HRP HP Hbv HH2.
    apply (Hcont fx' R' M' model' LB' cr' LBk W HFP); [|assumption..]. split; [exact HW|]. left. exact Hpost.
  - assert (Heq : Z.of_nat (length st) = cap) by lia.
    apply (vec_push_grow LB cr o b cap xa x sp r st fx R M model K HH Hmo HKnil Hfp).
    { rewrite Heq in Hw8. repeat (split; [assumption|]). exact (Hcredit Heq). }
    intros fx' R' M' model' LB' cr' LBk W HFP (HW & Hpost) HRP HP Hbv HH2.
    apply (Hcont fx' R' M' model' LB' cr' LBk W HFP); [|assumption..]. split; [exact HW|]. right. exact Hpost.
Qed.
End VecPushOk.
End VP.
