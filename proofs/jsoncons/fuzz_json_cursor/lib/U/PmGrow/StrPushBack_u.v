(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u PmLibDefs_u PmLibSpecs_u PmLayout_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutL5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen Require Cut_str_push_back_fast_csrc_T_u Cut_str_push_back_fast_csrc_u Cut_str_push_back_grow_csrc_T_u Cut_str_push_back_grow_csrc_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutDemo Require Pm10Memmove_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmGrow Require Import GrowKit_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module SPB.
Module F := Cut_str_push_back_fast_csrc_u.   Module FT := Cut_str_push_back_fast_csrc_T_u.
Module G := Cut_str_push_back_grow_csrc_u.   Module GT := Cut_str_push_back_grow_csrc_T_u.
Definition MALLOC : Z := PML.PC_MALLOC.  Definition FREE : Z := PML.PC_FREE.  Definition MEMMOVE : Z := 0xb7c98.
Definition RET : Z := Eval vm_compute in hd 0 FT.ENDS.
Definition SCRT : Z := Eval vm_compute in CH.hd_scr F.HDECL.
Definition CSAVED := CL5.CSAVED.
Definition has := GK.has.

Lemma heap_ok_f : CH2.heap_chk FT.NF F.HDECL F.BLS F.CPS GK.HULL_LO GK.HULL_HI F.TAGS F.RETS MALLOC FREE [MEMMOVE] = true.
Proof. vmc_refl. Qed.
Lemma heap_ok_g : CH2.heap_chk GT.NF G.HDECL G.BLS G.CPS GK.HULL_LO GK.HULL_HI G.TAGS G.RETS MALLOC FREE [MEMMOVE] = true.
Proof. vmc_refl. Qed.
Lemma no_goto_f : CH2.leaves_all F.CPS F.TAGS (fun _ _ _ _ t => match t with CC.TGoto _ _ => false | CC.TOther _ => true end) = true.
Proof. vmc_refl. Qed.
Lemma no_goto_g : CH2.leaves_all G.CPS G.TAGS (fun _ _ _ _ t => match t with CC.TGoto _ _ => false | CC.TOther _ => true end) = true.
Proof. vmc_refl. Qed.

Definition e_o := EVar 10.  Definition e_c := EVar 11.  Definition e_k := EVar 32.  Definition e_size := EVar 33.  Definition e_p := EVar 34.
Definition CAP : expr := EMd M_MUL (ELit 2) e_k.

Definition exit_f (c : CC.cutpoint) (ps : SR.post_spec) : bool :=
  let cells := SR.ps_cells ps in
  (CL.ps_at ps [RET] && CL.ps_keeps ps CSAVED && Nat.leb FT.NF (CC.cp_nx c)
   && has cells (KWord (SA e_o 0) 8 (APC.eaddz CAP 1)) && has cells (KWord (SA e_o 8) 8 (APC.eaddz e_size 1)) && has cells (KWord (SA e_o 16) 8 e_p)
   && has cells (KBlob (SA e_p 0) e_size 0) && has cells (KWord (SA (APC.eadd e_size e_p) 0) 1 e_c) && has cells (KWord (SA (APC.eadd e_size e_p) 1) 1 (ELit 0)))%bool.
Definition leaf_f (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with CC.TGoto _ _ => false | CC.TOther pc => (negb (CH2.is_call MALLOC FREE [MEMMOVE] pc) && Nat.eqb i 0 && exit_f c ps)%bool end.
Lemma leaf_f_ok : CH2.leaves_all F.CPS F.TAGS leaf_f = true.
Proof. vmc_refl. Qed.

Definition pre (i : nat) : bool := Nat.eqb i 0.
Definition hd_base (i : nat) : expr := fst (hd (ELit 0, ELit 0) (nth i G.BLS [])).
Definition hd_size (i : nat) : expr := snd (hd (ELit 0, ELit 0) (nth i G.BLS [])).
Definition CAP2 : expr := EAlu ALU_ADD (EMd M_MUL (ELit 4) e_k) (ELit (-2)).
Definition NEWCAP : expr := EAlu ALU_ADD (EMd M_MUL (ELit 8) (EAlu ALU_SRL CAP2 (ELit 3))) (ELit 8).
Definition exit_g (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) : bool :=
  let cells := SR.ps_cells ps in let pe := hd_base i in let ce := hd_size i in
  (CL.ps_at ps [RET] && CL.ps_keeps ps CSAVED && CH2.blocks_vars_lt (CC.cp_nx c) (nth i G.BLS []) && Nat.leb GT.NF (CC.cp_nx c)
   && negb (pre i) && match nth i G.BLS [] with [_] => true | _ => false end
   && has cells (KWord (SA e_o 0) 8 (APC.eaddz ce 1)) && has cells (KWord (SA e_o 8) 8 CAP) && has cells (KWord (SA e_o 16) 8 pe)
   && has cells (KBlob (SA pe 0) (APC.eaddz CAP (-1)) 0) && has cells (KWord (SA (APC.eadd CAP pe) (-1)) 1 e_c) && has cells (KWord (SA (APC.eadd CAP pe) 0) 1 (ELit 0))
   && expr_eqb ce NEWCAP && has cells (KDisj (SA pe 0) ce (SA e_p 0) CAP)
   && match pe with EVar v => Nat.leb GT.NF v | _ => false end)%bool.
Definition leaf_g (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      if CH2.is_call MALLOC FREE [MEMMOVE] pc then
        match CH2.ret_of G.RETS i k with
        | Some j =>
            match nth_error G.CPS j with
            | Some cj =>
                (Nat.leb GT.NF (CC.cp_nx c) && Nat.leb (CC.cp_nx c) (CC.cp_nx cj - APC.NCS)
                 && if Z.eqb pc MALLOC then (pre i && negb (pre j) && expr_eqb (hd_size j) (CA.ps_reg ps 10) && APC.expr_vars_lt GT.NF (hd_size j) && expr_eqb (hd_size j) NEWCAP)
                    else (negb (pre i) && negb (pre j) && expr_eqb (hd_size i) (hd_size j) && APC.expr_vars_lt GT.NF (hd_size i)))%bool
            | None => false
            end
        | None => false
        end
      else exit_g i c ps
  end.
Lemma leaf_g_ok : CH2.leaves_all G.CPS G.TAGS leaf_g = true.
Proof. vmc_refl. Qed.

Lemma ret_at : CL.is_ret_at GK.RSEGS RET.
Proof. CL.solve_is_ret. Qed.

Section StrPushBackOk.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps GK.RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom GK.RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom GK.RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.

Lemma push_back_fast : forall (LB : list (Z * Z)) (cr : credit) (o cap p c sp r : Z) (s : list Z),
  PML.cps_heap L HI PML.PC_STR_PUSH_BACK r sp PMS.STR_SCR LB cr
      (fun R M => (24 <= cap /\ Z.of_nat (length s) + 1 < cap) /\ PML.entry L R M sp r PMS.STR_SCR /\ PML.a0 R o /\ PML.a1 R c /\ 0 <= c < 256 /\ PML.str_at M o (PML.SLong cap p s) /\
                  In (p, cap) LB /\ PML.obj_on_stack L sp o 24 /\ Z.of_nat (length s) < 2 ^ 26)
      (fun R M R' M' LB' cr' LBk W => (PML.str_at M' o (PML.SLong cap p (s ++ [c])) /\ LB' = LB /\ cr' = cr /\ LBk = lb_remove p LB) /\ W = [(o, 24)]).
Proof.
  intros LB cr o cap p c sp r s. unfold PML.cps_heap.
  intros fx R M model K HH Hmo HKnil Hfp ((H24 & Hlt) & Hentry & Ha0 & Ha1 & Hc & Hstr & HinLB & Hobj & Hlen) Hcont.
  destruct Hentry as (Hra & Hraok & Hsp & Htp & Hstk). destruct Hstk as (S1 & S2 & S3 & S4 & S5).
  unfold PMS.STR_SCR, PMS.OPNEW_SCR, PML.HEAP_STACK in *.
  destruct Hstr as ((Hbit & Hw0 & Hw8 & Hw16 & Hbs & Hnul) & Hc8 & Hslt).
  destruct Hobj as (O1 & O2 & O3).
  set (size := Z.of_nat (length s)) in *.
  pose proof (PmLayout.ly_segs L LAY) as LS. pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI. pose proof (PmLayout.ly_stack L LAY) as LSTK. unfold PML.HEAP_STACK in LSTK.
  destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hwf & Hnd & _).
  destruct (Hwf _ HinLB) as ((P0 & P1 & P2 & P3 & P4) & Pdef & Pap). cbn [fst snd] in *.
  pose proof (CH2.heap_own_front L HI HIok LB cr M _ p cap HH HinLB) as HH'.
  set (k := cap / 2). assert (Hk : cap = 2 * k) by (unfold k; assert (cap mod 2 = 0) by (rewrite <- (Z.mod_mod_divide cap 8 2) by (exists 4; reflexivity); rewrite Hc8; reflexivity); rewrite (Z.div_mod cap 2) at 1 by lia; lia).
  set (E0 := Env (reg_ev R (fun v => Z_to_bv 64 (nth (v - 32) [k; size; p] 0))) (fun id => nth id [map (Z_to_bv 8) s] [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 PML.TP) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 o) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (V11 : ev E0 11 = Z_to_bv 64 c) by (rewrite <- Ha1; exact (EV 11%bv)).
  assert (V32 : ev E0 32 = Z_to_bv 64 k) by reflexivity.
  assert (V33 : ev E0 33 = Z_to_bv 64 size) by reflexivity.
  assert (V34 : ev E0 34 = Z_to_bv 64 p) by reflexivity.
  assert (CLO : 0x7fff7f800000 <= hl_ceil L) by lia.
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; lia).
  assert (U10 : bv_unsigned (ev E0 10) = o) by (rewrite V10; apply u64_of_Z; lia).
  assert (U11 : bv_unsigned (ev E0 11) = c) by (rewrite V11; apply u64_of_Z; lia).
  assert (U32 : bv_unsigned (ev E0 32) = k) by (rewrite V32; apply u64_of_Z; lia).
  assert (U33 : bv_unsigned (ev E0 33) = size) by (rewrite V33; apply u64_of_Z; lia).
  assert (U34 : bv_unsigned (ev E0 34) = p) by (rewrite V34; apply u64_of_Z; lia).
  assert (FR : forall E1, env_agree FT.NF E0 E1 ->
            bv_unsigned (ev E1 2) = sp /\ bv_unsigned (ev E1 10) = o /\ bv_unsigned (ev E1 11) = c /\
            bv_unsigned (ev E1 32) = k /\ bv_unsigned (ev E1 33) = size /\ bv_unsigned (ev E1 34) = p /\ eb E1 = eb E0).
  { intros E1 [A B]. rewrite <- !A by (unfold FT.NF; lia). repeat split; try assumption. symmetry. exact B. }
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= 0x7fff7f800000) by (rewrite ILO, IHI; lia).
  assert (LYE : hl_img_lo L <= hl_errno L /\ hl_errno L + 4 <= hl_img_hi L) by (rewrite ILO, IHI, (PmLayout.ly_errno L LAY); lia).
  assert (STKF : sp mod 16 = 0 /\ hl_ceil L + CH.hd_scr F.HDECL <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47)
    by (change (CH.hd_scr F.HDECL) with SCRT; unfold SCRT; repeat split; lia).
  assert (SCRP : 0 <= CH.hd_scr F.HDECL) by (change (CH.hd_scr F.HDECL) with SCRT; unfold SCRT; lia).
  assert (NF32 : (32 <= FT.NF)%nat) by (unfold FT.NF; lia).
  assert (W_OK : forall (w : L5.range) (a : Z), In w [(o, 24)] -> L5.in_rng w a -> CH2.wclient L sp a).
  { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. split; [lia | left; lia]. }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs F.HDECL) -> SGP.region_vars_lt FT.NF rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> exists w : L5.range, In w [(o, 24)] /\ L5.in_rng w a)).
  { intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CH2.in_reg, estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha.
    rewrite U10 in Ha. rewrite u64_of_Z in Ha by lia. exists (o, 24). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia]. }
  unfold PML.cfg. change PML.PC_STR_PUSH_BACK with (CC.cp_pc F.cp0). rewrite <- LS.
  eapply CH2.heap_cert_sound with (NF := FT.NF) (E0 := E0) (M0 := M) (model0 := model) (LBrest := lb_remove p LB) (sp0 := sp) (d := F.HDECL)
    (W := [(o, 24)]) (BLS := F.BLS) (Cred := fun _ _ cr' => cr' = cr) (CPS := F.CPS) (TAGS := F.TAGS) (RETS := F.RETS) (MALLOC := MALLOC) (FREE := FREE)
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
  - rewrite LS. exact F.plans.
  - exact F.tags_ok.
  - exact heap_ok_f.
  - exact (PmLayout.ly_malloc L LAY).
  - exact (PmLayout.ly_free L LAY).
  - intros pc [<-|[]]. exact (Pm10Memmove_u.memmove_copy1 L LS).
  - intros i c0 kk ps j sg IL. exfalso. pose proof (CH2.leaves_all_sound _ _ _ no_goto_f _ _ _ _ _ IL) as X. cbv beta iota in X. discriminate X.
  - intros i c0 kk ps j cj IL. exfalso. pose proof (CH2.leaves_all_sound _ _ _ leaf_f_ok _ _ _ _ _ IL) as X. unfold leaf_f in X.
    change (CH2.is_call MALLOC FREE [MEMMOVE] MALLOC) with true in X. discriminate X.
  - intros i c0 kk ps pc j cj IL Hcall. exfalso. pose proof (CH2.leaves_all_sound _ _ _ leaf_f_ok _ _ _ _ _ IL) as X. unfold leaf_f in X. rewrite Hcall in X. discriminate X.
  -
    intros i c0 kk ps pc IL Hnc fx' E R1 M1 m1 E' R' M' HAt HAmb HFP Hag HLF _.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_f_ok _ _ _ _ _ IL) as X. unfold leaf_f in X. rewrite Hnc in X.
    apply andb_prop in X as [Xi X]. apply andb_prop in Xi as [_ Xi]. apply Nat.eqb_eq in Xi. subst i. unfold exit_f in X.
    pose proof (CH2.exit_amb L HI HIok LYI LYE (PmLayout.ly_ro L LAY) FT.NF E0 M model (lb_remove p LB) sp F.HDECL [(o, 24)] F.BLS (fun _ _ cr' => cr' = cr) STKF SCRP NF32 U2 W_OK WRS_OK
                  F.CPS GK.HULL_LO GK.HULL_HI F.TAGS F.RETS MALLOC FREE [MEMMOVE] heap_ok_f _ c0 kk ps pc IL Hnc E E' R1 R' M1 M' m1 HAt HAmb Hag HLF) as HA'.
    repeat (apply andb_prop in X as [X ?Y]).

    apply Z.eqb_eq in X. apply Nat.leb_le in Y5.
    pose proof HA' as HA2. destruct HA' as (Hmo1 & Hbv1 & HagE1 & (cr1 & HH1 & HC1) & Hfr1 & Hdf1). subst cr1.
    assert (HagE' : env_agree FT.NF E0 E') by (eapply CC.env_agree_trans; [exact HagE1 | eapply CC.env_agree_le; [exact Hag | exact Y5]]).
    destruct (FR E' HagE') as (F2 & F10 & F11 & F32 & F33 & F34 & FB).
    rewrite LS in HLF.
    assert (CELL : forall X0, has (SR.ps_cells ps) X0 = true -> kentry_ok GK.RSEGS E' M' X0).
    { intros X0 HX. apply (CC.lf_cells _ _ _ _ _ _ _ HLF). exact (GK.has_In _ _ HX). }
    assert (UCAP : bv_unsigned (edenot E' CAP) = cap) by (apply CL5.u_lin; [unfold CAP, e_k; lin_eval; rw_atoms; lia | lia]).
    assert (HH2 : hi_heap HI ((p, cap) :: lb_remove p LB) cr M' (m_vmmaps m1)).
    { unfold CH2.cur in HH1. change (nth 0 F.BLS []) with [(EVar 34, EMd M_MUL (ELit 2) (EVar 32))] in HH1. unfold CH2.den in HH1. cbn [map fst snd] in HH1.
      assert (X1 : bv_unsigned (edenot E (EVar 34)) = p) by (cbn [edenot]; destruct HagE1 as [AG1 _]; rewrite <- AG1 by (unfold FT.NF; lia); exact U34).
      assert (X2 : bv_unsigned (edenot E (EMd M_MUL (ELit 2) (EVar 32))) = cap).
      { apply CL5.u_lin; [lin_eval; destruct HagE1 as [AG1 _]; rewrite <- AG1 by (unfold FT.NF; lia); rewrite U32; lia | lia]. }
      rewrite X1, X2 in HH1. exact HH1. }

    assert (UW0 : bv_unsigned (edenot E' (APC.eaddz CAP 1)) = cap + 1) by (apply CL5.u_lin; [unfold CAP, e_k; lin_eval; rw_atoms; lia | lia]).
    assert (US1 : bv_unsigned (edenot E' (APC.eaddz e_size 1)) = size + 1) by (apply CL5.u_lin; [unfold e_size; lin_eval; rw_atoms; lia | lia]).
    assert (USP : bv_unsigned (edenot E' (APC.eadd e_size e_p)) = size + p) by (apply CL5.u_lin; [unfold e_size, e_p; lin_eval; rw_atoms; lia | lia]).
    assert (W0 : L5.u64_at GK.RSEGS M' o (cap + 1)).
    { apply (CL5.kword64_elim GK.RSEGS E' M' _ _ o _ (CELL _ Y4)); [unfold estart, e_o; cbn [a_base a_off edenot]; rewrite F10; lia | exact UW0]. }
    assert (W8 : L5.u64_at GK.RSEGS M' (o + 8) (size + 1)).
    { apply (CL5.kword64_elim GK.RSEGS E' M' _ _ (o + 8) _ (CELL _ Y3)); [unfold estart, e_o; cbn [a_base a_off edenot]; rewrite F10; lia | exact US1]. }
    assert (W16 : L5.u64_at GK.RSEGS M' (o + 16) p).
    { apply (CL5.kword64_elim GK.RSEGS E' M' _ _ (o + 16) _ (CELL _ Y2)); [unfold estart, e_o; cbn [a_base a_off edenot]; rewrite F10; lia | exact F34]. }
    assert (BS : L5.bytes_at GK.RSEGS M' p s).
    { apply (CL5.kblob_elim GK.RSEGS E' M' _ _ 0%nat p s (CELL _ Y1)); [unfold estart, e_p; cbn [a_base a_off edenot]; rewrite F34; lia | rewrite FB; reflexivity]. }
    assert (BC : L5.u8_at GK.RSEGS M' (p + size) c).
    { apply (GK.kword8_elim E' M' _ _ (p + size) c (CELL _ Y0)); [unfold estart; cbn [a_base a_off]; rewrite USP; lia | exact F11]. }
    assert (NUL : L5.u8_at GK.RSEGS M' (p + (size + 1)) 0).
    { apply (CL5.kword8_zero_elim GK.RSEGS E' M' _ _ (CELL _ Y)). unfold estart. cbn [a_base a_off]. rewrite USP. lia. }
    assert (LEN : Z.of_nat (length (s ++ [c])) = size + 1) by (rewrite length_app, Nat2Z.inj_add; reflexivity).
    assert (STR : PML.str_at M' o (PML.SLong cap p (s ++ [c]))).
    { split; [|split; [exact Hc8 | rewrite LEN; lia]]. unfold L5.lstr_long. rewrite LEN.
      split; [exact Hbit|]. split; [exact W0|]. split; [exact W8|]. split; [exact W16|]. split; [|exact NUL].
      apply CL5.bytes_at_app; [exact BS|]. intros j Hj. cbn [length] in Hj. assert (j = 0%nat) by lia. subst j. cbn [nth]. rewrite Z.add_0_r. exact BC. }

    assert (KEEP : forall y : reg, In (ridx y) CSAVED -> getr R' y = getr R y).
    { intros y Hy. assert (Hy32 : (ridx y < FT.NF)%nat) by (unfold CSAVED, CL5.CSAVED in Hy; cbn [In] in Hy; unfold FT.NF; intuition lia).
      rewrite (CL.ps_keeps_sound GK.RSEGS c0 ps E0 E' R' M1 M' CSAVED FT.NF y HLF Y6 HagE' Hy Hy32). exact (EV y). }
    assert (HRP : regs_preserved R R') by (intros y Hy; apply KEEP; exact (CL5.csaved_in y Hy)).
    assert (Hra' : getr R' 1%bv = Z_to_bv 64 r) by (rewrite (KEEP 1%bv ltac:(left; reflexivity)); exact Hra).
    assert (Hds : L5.defined M (sp - CH.hd_scr F.HDECL) (CH.hd_scr F.HDECL)).
    { change (CH.hd_scr F.HDECL) with SCRT. unfold SCRT. intros j Hj. replace (sp - 8304 + j) with (sp - (256 + (16 + 8224)) + (j + 192)) by lia. apply S5. lia. }
    pose proof (CH2.amb_hpres L HI LYI LYE FT.NF E0 M model (lb_remove p LB) sp F.HDECL [(o, 24)] F.BLS (fun _ _ cr' => cr' = cr) STKF NF32 0%nat E M' m1 HA2 Hds) as HP0.
    change (CH.hd_scr F.HDECL) with SCRT in HP0.
    assert (HP : L5C.hpres L (lb_remove p LB) sp (256 + (16 + 8224)) [(o, 24)] M M').
    { apply (GK.hpres_scr L _ sp SCRT); [unfold SCRT; lia | exact S5 | lia | rewrite (PmLayout.ly_errno L LAY); lia | lia | lia | exact HP0]. }
    rewrite X, LS. eapply CL.ret_cps; [exact ret_at | exact (proj1 Hmo1) | exact (proj1 (proj2 Hmo1)) | |].
    { rewrite Hra'. apply Hoare.ret_ok_even. destruct Hraok as [R1' R2']. rewrite u64_of_Z by lia. exact R2'. }
    rewrite Hra'.
    apply (Hcont fx' R' M' m1 LB cr (lb_remove p LB) [(o, 24)] HFP); [| exact HRP | exact HP | exact Hbv1 | exact (CH2.heap_own_back L HI HIok LB cr M' _ p cap HH2 HinLB Hnd)].
    split; [|reflexivity]. split; [exact STR|]. auto.
  - reflexivity.
  -
    rewrite LS.
    assert (Hdo : L5.defined M o 24).
    { apply GK.defined_3x8; [exact (GK.defined_of_u64 M o _ Hw0 ltac:(unfold GK.HULL_HI; lia) ltac:(lia)) | exact (GK.defined_of_u64 M (o + 8) _ Hw8 ltac:(unfold GK.HULL_HI; lia) ltac:(lia))
                            | exact (GK.defined_of_u64 M (o + 16) _ Hw16 ltac:(unfold GK.HULL_HI; lia) ltac:(lia))]. }
    assert (Hdp : L5.defined M p cap) by exact Pdef.
    assert (Hds : L5.defined M (sp - 8304) 8304) by (intros i Hi; replace (sp - 8304 + i) with (sp - (256 + (16 + 8224)) + (i + 192)) by lia; apply S5; lia).
    assert (W0 : edenot E0 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 2) (EVar 32)) (ELit 1)) = Z_to_bv 64 (cap + 1)).
    { rewrite <- (Z_to_bv_bv_unsigned _ (edenot E0 _)). f_equal. apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia]. }
    split; [exact (regs_ok_id R _ _)|]. unfold know_ok, F.cp0. cbn [CC.cp_know].
    repeat (apply Forall_cons); [.. | apply Forall_nil].
    + eapply CL5.kword64_intro with (A := o) (z := cap + 1); [ev_start | lia | lia | exact W0 | exact Hw0].
    + eapply CL5.kword64_intro with (A := o + 8) (z := size); [ev_start | lia | lia | exact V33 | exact Hw8].
    + eapply CL5.kword64_intro with (A := o + 16) (z := p); [ev_start | lia | lia | exact V34 | exact Hw16].
    + e_range. + e_range. + e_range. + e_range.
    + eapply CL5.kblob_intro with (bs := s) (A := p); [ev_start | unfold elenZ; cbn [edenot]; exact U33 | lia | fold size; lia | lia | reflexivity | exact Hbs | fold size; ev_def].
    + e_unk. + e_wr. + e_range. + e_align P2.
    + e_unk. + e_wr. + e_range. + e_align O3.
    + e_unk. + e_wr. + e_range. + e_align S1.
    + e_disj. + e_disj. + e_disj.
  -
    split; [exact Hmo|]. split; [apply L5C.model_but_vm_refl|]. split; [apply CC.env_agree_refl|].
    split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
    exists cr. split; [|reflexivity]. unfold CH2.cur.
    replace (CH2.den E0 (nth 0 F.BLS [])) with [(p, cap)]; [exact HH'|].
    change (nth 0 F.BLS []) with [(EVar 34, EMd Instr.M_MUL (ELit 2) (EVar 32))]. unfold CH2.den. cbn [map fst snd].
    f_equal. f_equal; [cbn [edenot]; symmetry; exact U34 | symmetry; apply CL5.u_lin; [lin_eval; rewrite U32; lia | lia]].
  - exact Hfp.
Qed.

Definition Cred (cr0 : credit) (i : nat) (E : env) (cr : credit) : Prop :=
  cr = if pre i then cr0 else debit L cr0 (snd (hd (0, 0) (CH2.den E (nth i G.BLS [])))).

Lemma push_back_grow : forall (LB : list (Z * Z)) (cr : credit) (o cap p c sp r : Z) (s : list Z),
  PML.cps_heap L HI PML.PC_STR_PUSH_BACK r sp PMS.STR_SCR LB cr
      (fun R M => (24 <= cap /\ Z.of_nat (length s) + 1 = cap) /\ PML.entry L R M sp r PMS.STR_SCR /\ PML.a0 R o /\ PML.a1 R c /\ 0 <= c < 256 /\ PML.str_at M o (PML.SLong cap p s) /\
                  In (p, cap) LB /\ PML.obj_on_stack L sp o 24 /\ Z.of_nat (length s) < 2 ^ 26 /\ credit_ok L cr (PML.grow_cap cap (Z.of_nat (length s) + 1)))
      (fun R M R' M' LB' cr' LBk W =>
         (exists p', let cap' := PML.grow_cap cap (Z.of_nat (length (s ++ [c]))) in
            PML.str_at M' o (PML.SLong cap' p' (s ++ [c])) /\ L5C.fresh_block L LB M' p' cap' /\
            LB' = (p', cap') :: lb_remove p LB /\ cr' = debit L cr cap' /\ LBk = lb_remove p LB) /\ W = [(o, 24)]).
Proof.
  intros LB cr o cap p c sp r s. unfold PML.cps_heap.
  intros fx R M model K HH Hmo HKnil Hfp ((H24 & Heq) & Hentry & Ha0 & Ha1 & Hc & Hstr & HinLB & Hobj & Hlen & Hcredit) Hcont.
  destruct Hentry as (Hra & Hraok & Hsp & Htp & Hstk). destruct Hstk as (S1 & S2 & S3 & S4 & S5).
  unfold PMS.STR_SCR, PMS.OPNEW_SCR, PML.HEAP_STACK in *.
  destruct Hstr as ((Hbit & Hw0 & Hw8 & Hw16 & Hbs & Hnul) & Hc8 & Hslt).
  destruct Hobj as (O1 & O2 & O3).
  set (size := Z.of_nat (length s)) in *.
  pose proof (PmLayout.ly_segs L LAY) as LS. pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI. pose proof (PmLayout.ly_stack L LAY) as LSTK. unfold PML.HEAP_STACK in LSTK.
  destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hwf & Hnd & _).
  destruct (Hwf _ HinLB) as ((P0 & P1 & P2 & P3 & P4) & Pdef & Pap). cbn [fst snd] in *.
  pose proof (CH2.heap_own_front L HI HIok LB cr M _ p cap HH HinLB) as HH'.
  set (k := cap / 2). assert (Hk : cap = 2 * k) by (unfold k; assert (cap mod 2 = 0) by (rewrite <- (Z.mod_mod_divide cap 8 2) by (exists 4; reflexivity); rewrite Hc8; reflexivity); rewrite (Z.div_mod cap 2) at 1 by lia; lia).
  set (E0 := Env (reg_ev R (fun v => Z_to_bv 64 (nth (v - 32) [k; size; p] 0))) (fun id => nth id [map (Z_to_bv 8) s] [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 PML.TP) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 o) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (V11 : ev E0 11 = Z_to_bv 64 c) by (rewrite <- Ha1; exact (EV 11%bv)).
  assert (V32 : ev E0 32 = Z_to_bv 64 k) by reflexivity.
  assert (V34 : ev E0 34 = Z_to_bv 64 p) by reflexivity.
  assert (CLO : 0x7fff7f800000 <= hl_ceil L) by lia.
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; lia).
  assert (U10 : bv_unsigned (ev E0 10) = o) by (rewrite V10; apply u64_of_Z; lia).
  assert (U11 : bv_unsigned (ev E0 11) = c) by (rewrite V11; apply u64_of_Z; lia).
  assert (U32 : bv_unsigned (ev E0 32) = k) by (rewrite V32; apply u64_of_Z; lia).
  assert (U34 : bv_unsigned (ev E0 34) = p) by (rewrite V34; apply u64_of_Z; lia).
  assert (FR : forall E1, env_agree GT.NF E0 E1 ->
            bv_unsigned (ev E1 2) = sp /\ bv_unsigned (ev E1 10) = o /\ bv_unsigned (ev E1 11) = c /\
            bv_unsigned (ev E1 32) = k /\ bv_unsigned (ev E1 34) = p /\ eb E1 = eb E0).
  { intros E1 [A B]. rewrite <- !A by (unfold GT.NF; lia). repeat split; try assumption. symmetry. exact B. }

  assert (GC : PML.grow_cap cap (size + 1) = 8 * ((4 * k - 2) / 8) + 8).
  { unfold PML.grow_cap. rewrite Z.max_r by lia. replace (2 * (cap - 1)) with (4 * k - 2) by lia. rewrite CL5.lor7 by lia. lia. }
  assert (NEWV : forall E1, env_agree GT.NF E0 E1 -> bv_unsigned (edenot E1 NEWCAP) = PML.grow_cap cap (size + 1)).
  { intros E1 Hag1. destruct (FR E1 Hag1) as (F2 & F10 & F11 & F32 & F34 & _). rewrite GC. unfold NEWCAP, CAP2, e_k.
    assert (UC : bv_unsigned (edenot E1 (EAlu ALU_ADD (EMd M_MUL (ELit 4) (EVar 32)) (ELit (-2)))) = 4 * k - 2) by (apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia]).
    apply CL5.u_lin; [lin_form; rewrite u_srl_lit; cbn [edenot]; cbn [edenot] in UC; rewrite UC; change (2 ^ ((3 mod two64) mod 64)) with 8; lia|].
    pose proof (Z.div_le_upper_bound (4 * k - 2) 8 (2 ^ 26) ltac:(lia) ltac:(lia)). pose proof (Z.div_pos (4 * k - 2) 8 ltac:(lia) ltac:(lia)). lia. }
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
  eapply CH2.heap_cert_sound with (NF := GT.NF) (E0 := E0) (M0 := M) (model0 := model) (LBrest := lb_remove p LB) (sp0 := sp) (d := G.HDECL)
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
  - intros pc [<-|[]]. exact (Pm10Memmove_u.memmove_copy1 L LS).
  - intros i c0 kk ps j sg IL. exfalso. pose proof (CH2.leaves_all_sound _ _ _ no_goto_g _ _ _ _ _ IL) as X. cbv beta iota in X. discriminate X.
  -
    intros i c0 kk ps j cj IL Hret Hcj E E' R' M1 M1' cr' HagE Hag HLF HC.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_g_ok _ _ _ _ _ IL) as X. unfold leaf_g in X.
    change (CH2.is_call MALLOC FREE [MEMMOVE] MALLOC) with true in X. cbv beta iota in X. rewrite Hret, Hcj in X. change (Z.eqb MALLOC MALLOC) with true in X. cbv beta iota in X.
    apply andb_prop in X as [X XM]. apply andb_prop in X as [XA XB]. apply Nat.leb_le in XA, XB.
    repeat (apply andb_prop in XM as [XM ?Z]). apply expr_eqb_eq in Z, Z1. apply negb_true_iff in Z2.
    assert (HagE' : env_agree GT.NF E0 E') by (eapply CC.env_agree_trans; [exact HagE | eapply CC.env_agree_le; [exact Hag | exact XA]]).
    pose proof (NEWV E' HagE') as Hval. rewrite <- Z in Hval.
    unfold Cred in HC. rewrite XM in HC. subst cr'. rewrite <- Z1. rewrite Hval. split; [exact Hcredit|].
    intros E2 Hag2. unfold Cred. rewrite Z2. rewrite GK.den_hd. fold (hd_size j). f_equal. rewrite <- Hval.
    f_equal. apply (SR.edenot_agree_AP GT.NF E' E2); [eapply CC.env_agree_le; [exact Hag2 | lia] | exact Z0].
  -
    intros i c0 kk ps pc j cj IL Hcall Hnm Hret Hcj E E' R' M1 M1' cr' HagE Hag HLF HC E2 Hag2.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_g_ok _ _ _ _ _ IL) as X. unfold leaf_g in X. rewrite Hcall, Hret, Hcj in X.
    destruct (Z.eqb_spec pc MALLOC) as [->|_]; [contradiction|].
    apply andb_prop in X as [X XM]. apply andb_prop in X as [XA XB]. apply Nat.leb_le in XA, XB.
    repeat (apply andb_prop in XM as [XM ?Z]). apply negb_true_iff in XM, Z1. apply expr_eqb_eq in Z0.
    unfold Cred in *. rewrite Z1. rewrite XM in HC. rewrite HC. f_equal. rewrite !GK.den_hd. fold (hd_size i) (hd_size j). rewrite <- Z0. f_equal.
    apply (SR.edenot_agree_AP GT.NF E E2); [|exact Z].
    eapply CC.env_agree_trans; [eapply CC.env_agree_le; [exact Hag | exact XA] | eapply CC.env_agree_le; [exact Hag2 | lia]].
  -
    intros i c0 kk ps pc IL Hnc fx' E R1 M1 m1 E' R' M' HAt HAmb HFP Hag HLF _.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_g_ok _ _ _ _ _ IL) as X. unfold leaf_g in X. rewrite Hnc in X. unfold exit_g in X.
    pose proof (CH2.exit_amb L HI HIok LYI LYE (PmLayout.ly_ro L LAY) GT.NF E0 M model (lb_remove p LB) sp G.HDECL [(o, 24)] G.BLS (Cred cr) STKF SCRP NF32 U2 W_OK WRS_OK
                  G.CPS GK.HULL_LO GK.HULL_HI G.TAGS G.RETS MALLOC FREE [MEMMOVE] heap_ok_g i c0 kk ps pc IL Hnc E E' R1 R' M1 M' m1 HAt HAmb Hag HLF) as HA'.
    repeat (apply andb_prop in X as [X ?Y]).

    apply Z.eqb_eq in X. apply Nat.leb_le in Y10. apply negb_true_iff in Y9. apply expr_eqb_eq in Y1.
    pose proof HA' as HA2. destruct HA' as (Hmo1 & Hbv1 & HagE1 & (cr1 & HH1 & HC1) & Hfr1 & Hdf1).
    assert (HagE' : env_agree GT.NF E0 E') by (eapply CC.env_agree_trans; [exact HagE1 | eapply CC.env_agree_le; [exact Hag | exact Y10]]).
    destruct (FR E' HagE') as (F2 & F10 & F11 & F32 & F34 & FB).
    rewrite LS in HLF.
    assert (CELL : forall X0, has (SR.ps_cells ps) X0 = true -> kentry_ok GK.RSEGS E' M' X0).
    { intros X0 HX. apply (CC.lf_cells _ _ _ _ _ _ _ HLF). exact (GK.has_In _ _ HX). }
    unfold hd_base, hd_size in *. destruct (nth i G.BLS []) as [|[pe ce] [|]] eqn:HBL; try discriminate Y8. cbn [hd fst snd] in *.
    set (pX := bv_unsigned (edenot E' pe)) in *. set (capX := bv_unsigned (edenot E' ce)) in *.
    assert (HcapX : capX = PML.grow_cap cap (size + 1)) by (unfold capX; rewrite Y1; exact (NEWV E' HagE')).
    assert (HH2 : hi_heap HI ((pX, capX) :: lb_remove p LB) cr1 M' (m_vmmaps m1)).
    { unfold CH2.cur in HH1. rewrite HBL in HH1. rewrite <- (CH2.den_agree _ E E' _ Hag Y11) in HH1. exact HH1. }
    destruct (hio_wf L SCFG HI HIok _ _ _ _ HH2) as (Hwf2 & Hnd2 & _).
    destruct (Hwf2 (pX, capX) (or_introl eq_refl)) as ((Q0 & Q1 & Q2 & Q3 & Q4) & Qdef & Qap). cbn [fst snd lb_remove] in Q0, Q1, Q2, Q3, Q4, Qdef, Qap. rewrite Z.eqb_refl in Qap.

    assert (UCAP : bv_unsigned (edenot E' CAP) = cap) by (apply CL5.u_lin; [unfold CAP, e_k; lin_eval; rw_atoms; lia | lia]).
    assert (UCAPm : bv_unsigned (edenot E' (APC.eaddz CAP (-1))) = size) by (apply CL5.u_lin; [unfold CAP, e_k; lin_eval; rw_atoms; lia | lia]).
    assert (UCP : bv_unsigned (edenot E' (APC.eadd CAP pe)) = cap + pX).
    { unfold APC.eadd. rewrite mkAlu_denot, u_add64. rewrite UCAP. fold pX. apply Z.mod_small. lia. }
    assert (UW0 : bv_unsigned (edenot E' (APC.eaddz ce 1)) = capX + 1).
    { unfold APC.eaddz. rewrite mkAlu_denot, u_add64. cbn [edenot]. rewrite (u64_of_Z 1) by lia. fold capX. apply Z.mod_small. lia. }
    assert (W0 : L5.u64_at GK.RSEGS M' o (capX + 1)).
    { apply (CL5.kword64_elim GK.RSEGS E' M' _ _ o _ (CELL _ Y7)); [unfold estart, e_o; cbn [a_base a_off edenot]; rewrite F10; lia | exact UW0]. }
    assert (W8 : L5.u64_at GK.RSEGS M' (o + 8) (size + 1)).
    { apply (CL5.kword64_elim GK.RSEGS E' M' _ _ (o + 8) _ (CELL _ Y6)); [unfold estart, e_o; cbn [a_base a_off edenot]; rewrite F10; lia | rewrite UCAP; lia]. }
    assert (W16 : L5.u64_at GK.RSEGS M' (o + 16) pX).
    { apply (CL5.kword64_elim GK.RSEGS E' M' _ _ (o + 16) _ (CELL _ Y5)); [unfold estart, e_o; cbn [a_base a_off edenot]; rewrite F10; lia | reflexivity]. }
    assert (BS : L5.bytes_at GK.RSEGS M' pX s).
    { apply (CL5.kblob_elim GK.RSEGS E' M' _ _ 0%nat pX s (CELL _ Y4)); [unfold estart; cbn [a_base a_off]; fold pX; lia | rewrite FB; reflexivity]. }
    assert (BC : L5.u8_at GK.RSEGS M' (pX + size) c).
    { apply (GK.kword8_elim E' M' _ _ (pX + size) c (CELL _ Y3)); [unfold estart; cbn [a_base a_off]; rewrite UCP; lia | exact F11]. }
    assert (NUL : L5.u8_at GK.RSEGS M' (pX + (size + 1)) 0).
    { apply (CL5.kword8_zero_elim GK.RSEGS E' M' _ _ (CELL _ Y2)). unfold estart. cbn [a_base a_off]. rewrite UCP. lia. }
    assert (LEN : Z.of_nat (length (s ++ [c])) = size + 1) by (rewrite length_app, Nat2Z.inj_add; reflexivity).
    assert (Hlor : capX = 8 * ((4 * k - 2) / 8) + 8) by (rewrite HcapX; exact GC).
    assert (Hbig : size + 1 < capX).
    { rewrite Hlor. pose proof (Z.mod_pos_bound (4 * k - 2) 8 ltac:(lia)). pose proof (Z.div_mod (4 * k - 2) 8 ltac:(lia)). lia. }
    assert (STR : PML.str_at M' o (PML.SLong capX pX (s ++ [c]))).
    { split; [|split; [rewrite Hlor; rewrite Z.add_comm, Z.mul_comm, Z.mod_add by lia; reflexivity | rewrite LEN; exact Hbig]]. unfold L5.lstr_long. rewrite LEN.
      split; [rewrite Z.bit0_odd, Z.odd_add, <- Z.negb_even, Hlor, Z.even_add, Z.even_mul; reflexivity|]. split; [exact W0|]. split; [exact W8|]. split; [exact W16|]. split; [|exact NUL].
      apply CL5.bytes_at_app; [exact BS|]. intros j Hj. cbn [length] in Hj. assert (j = 0%nat) by lia. subst j. cbn [nth]. rewrite Z.add_0_r. exact BC. }

    assert (KEEP : forall y : reg, In (ridx y) CSAVED -> getr R' y = getr R y).
    { intros y Hy. assert (Hy32 : (ridx y < GT.NF)%nat) by (unfold CSAVED, CL5.CSAVED in Hy; cbn [In] in Hy; unfold GT.NF; intuition lia).
      rewrite (CL.ps_keeps_sound GK.RSEGS c0 ps E0 E' R' M1 M' CSAVED GT.NF y HLF Y12 HagE' Hy Hy32). exact (EV y). }
    assert (HRP : regs_preserved R R') by (intros y Hy; apply KEEP; exact (CL5.csaved_in y Hy)).
    assert (Hra' : getr R' 1%bv = Z_to_bv 64 r) by (rewrite (KEEP 1%bv ltac:(left; reflexivity)); exact Hra).
    assert (Hds : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)).
    { change (CH.hd_scr G.HDECL) with SCRT. unfold SCRT. intros j Hj. replace (sp - 8304 + j) with (sp - (256 + (16 + 8224)) + (j + 192)) by lia. apply S5. lia. }
    pose proof (CH2.amb_hpres L HI LYI LYE GT.NF E0 M model (lb_remove p LB) sp G.HDECL [(o, 24)] G.BLS (Cred cr) STKF NF32 i E M' m1 HA2 Hds) as HP0.
    change (CH.hd_scr G.HDECL) with SCRT in HP0.
    assert (HP : L5C.hpres L (lb_remove p LB) sp (256 + (16 + 8224)) [(o, 24)] M M').
    { apply (GK.hpres_scr L _ sp SCRT); [unfold SCRT; lia | exact S5 | lia | rewrite (PmLayout.ly_errno L LAY); lia | lia | lia | exact HP0]. }
    rewrite X, LS. eapply CL.ret_cps; [exact ret_at | exact (proj1 Hmo1) | exact (proj1 (proj2 Hmo1)) | |].
    { rewrite Hra'. apply Hoare.ret_ok_even. destruct Hraok as [R1' R2']. rewrite u64_of_Z by lia. exact R2'. }
    rewrite Hra'.
    assert (Hcr : cr1 = debit L cr capX).
    { unfold Cred in HC1. rewrite Y9 in HC1. rewrite HC1. f_equal. rewrite GK.den_hd, HBL. cbn [hd snd]. unfold capX. f_equal.
      apply (SR.edenot_agree_AP (CC.cp_nx c0) E E' ce Hag). unfold CH2.blocks_vars_lt in Y11. cbn [forallb fst snd] in Y11. apply andb_prop in Y11 as [Y11 _]. apply andb_prop in Y11 as [_ Y11]. exact Y11. }
    subst cr1.
    assert (Hdisj : pX + capX <= p \/ p + cap <= pX).
    { pose proof (CELL _ Y0) as G0. cbn [kentry_ok] in G0. unfold estart, elenZ in G0. cbn [a_base a_off] in G0. fold pX capX in G0.
      rewrite UCAP in G0. unfold e_p in G0. cbn [edenot] in G0. rewrite F34 in G0. lia. }
    apply (Hcont fx' R' M' m1 ((pX, capX) :: lb_remove p LB) (debit L cr capX) (lb_remove p LB) [(o, 24)] HFP); [| exact HRP | exact HP | exact Hbv1 | exact HH2].
    split; [|reflexivity]. exists pX. cbv zeta. rewrite LEN, <- HcapX.
    split; [exact STR|]. split; [|auto]. split; [repeat split; assumption|]. split; [|exact Qdef].
    intros b0 Hb0. destruct (Z.eq_dec (fst b0) p) as [e0|ne0].
    * rewrite (CH2.nodup_fst_eq LB b0 (p, cap) Hnd Hb0 HinLB e0). cbn [fst snd]. exact Hdisj.
    * destruct b0 as [bb bm]. exact (Qap (bb, bm) (L5C.in_lb_remove_neq p bb bm LB Hb0 ne0)).
  - reflexivity.
  -
    rewrite LS.
    assert (Hdo : L5.defined M o 24).
    { apply GK.defined_3x8; [exact (GK.defined_of_u64 M o _ Hw0 ltac:(unfold GK.HULL_HI; lia) ltac:(lia)) | exact (GK.defined_of_u64 M (o + 8) _ Hw8 ltac:(unfold GK.HULL_HI; lia) ltac:(lia))
                            | exact (GK.defined_of_u64 M (o + 16) _ Hw16 ltac:(unfold GK.HULL_HI; lia) ltac:(lia))]. }
    assert (Hdp : L5.defined M p cap) by exact Pdef.
    assert (Hds : L5.defined M (sp - 8304) 8304) by (intros i Hi; replace (sp - 8304 + i) with (sp - (256 + (16 + 8224)) + (i + 192)) by lia; apply S5; lia).
    assert (W0 : edenot E0 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 2) (EVar 32)) (ELit 1)) = Z_to_bv 64 (cap + 1)).
    { rewrite <- (Z_to_bv_bv_unsigned _ (edenot E0 _)). f_equal. apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia]. }
    assert (W8 : edenot E0 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 2) (EVar 32)) (ELit (-1))) = Z_to_bv 64 size).
    { rewrite <- (Z_to_bv_bv_unsigned _ (edenot E0 _)). f_equal. apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia]. }
    split; [exact (regs_ok_id R _ _)|]. unfold know_ok, G.cp0. cbn [CC.cp_know].
    repeat (apply Forall_cons); [.. | apply Forall_nil].
    + eapply CL5.kword64_intro with (A := o) (z := cap + 1); [ev_start | lia | lia | exact W0 | exact Hw0].
    + eapply CL5.kword64_intro with (A := o + 8) (z := size); [ev_start | lia | lia | exact W8 | exact Hw8].
    + eapply CL5.kword64_intro with (A := o + 16) (z := p); [ev_start | lia | lia | exact V34 | exact Hw16].
    + e_range. + e_range.
    + eapply CL5.kblob_intro with (bs := s) (A := p); [ev_start | apply CL5.elen_lin; [lin_eval; rw_atoms; fold size; lia | lia] | lia | fold size; lia | lia | reflexivity | exact Hbs | fold size; ev_def].
    + e_unk. + e_wr. + e_range. + e_align P2.
    + e_unk. + e_wr. + e_range. + e_align O3.
    + e_unk. + e_wr. + e_range. + e_align S1.
    + e_disj. + e_disj. + e_disj.
  -
    split; [exact Hmo|]. split; [apply L5C.model_but_vm_refl|]. split; [apply CC.env_agree_refl|].
    split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
    exists cr. split; [|reflexivity]. unfold CH2.cur.
    replace (CH2.den E0 (nth 0 G.BLS [])) with [(p, cap)]; [exact HH'|].
    change (nth 0 G.BLS []) with [(EVar 34, EMd Instr.M_MUL (ELit 2) (EVar 32))]. unfold CH2.den. cbn [map fst snd].
    f_equal. f_equal; [cbn [edenot]; symmetry; exact U34 | symmetry; apply CL5.u_lin; [lin_eval; rewrite U32; lia | lia]].
  - exact Hfp.
Qed.

Theorem str_push_back_ok : PMS.str_push_back_spec L HI.
Proof.
  intros LB cr o cap p c sp r s. unfold PML.cps_heap.
  intros fx R M model K HH Hmo HKnil Hfp (Hentry & Ha0 & Ha1 & Hc & Hstr & H24 & HinLB & Hobj & Hlen & Hcredit) Hcont.
  assert (LEN : Z.of_nat (length (s ++ [c])) = Z.of_nat (length s) + 1) by (rewrite length_app, Nat2Z.inj_add; reflexivity).
  pose proof Hstr as (_ & _ & Hslt).
  destruct (Z_lt_le_dec (Z.of_nat (length s) + 1) cap) as [Hlt|Hge].
  - apply (push_back_fast LB cr o cap p c sp r s fx R M model K HH Hmo HKnil Hfp); [split; [split; assumption|]; repeat (split; [assumption|]); assumption|].
    intros fx' R' M' model' LB' cr' LBk W HFP (Hpost & HW) HRP HP Hbv HH2.
    apply (Hcont fx' R' M' model' LB' cr' LBk W HFP); [|assumption..]. split; [|exact HW]. left. exact Hpost.
  - assert (Heq : Z.of_nat (length s) + 1 = cap) by lia.
    apply (push_back_grow LB cr o cap p c sp r s fx R M model K HH Hmo HKnil Hfp).
    { split; [split; assumption|]. repeat (split; [assumption|]). apply Hcredit. lia. }
    intros fx' R' M' model' LB' cr' LBk W HFP ((p' & Hpost) & HW) HRP HP Hbv HH2.
    apply (Hcont fx' R' M' model' LB' cr' LBk W HFP); [|assumption..]. split; [|exact HW]. right. exists p'. cbv zeta. cbv zeta in Hpost. split; [rewrite LEN; lia | exact Hpost].
Qed.
End StrPushBackOk.
End SPB.
