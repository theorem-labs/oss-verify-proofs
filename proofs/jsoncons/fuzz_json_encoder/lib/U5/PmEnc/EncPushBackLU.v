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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Cut_str_push_back_x_grow_xsrc_T_u5 Cut_str_push_back_x_grow_xsrc_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutDemo Require Pm6Memmove_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmGrow Require Import GrowKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncSums_u5 EncOpNew_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncPushBackL_u5 EncOpNewU.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.Heap Require Import HeapIfaceU.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.


Module EPLU.
Import EPL.

Lemma lb_remove_In : forall A (LB : list (Z * Z)) b, In b (lb_remove A LB) -> In b LB.
Proof.
  intros A LB b. induction LB as [|x r IH]; cbn [lb_remove]; [tauto|].
  destruct (Z.eqb (fst x) A); cbn [In]; intros H; [right; exact H|]. destruct H as [H|H]; [left; exact H | right; exact (IH H)].
Qed.
Lemma lb_remove_In_ne : forall A (LB : list (Z * Z)) b, In b LB -> fst b <> A -> In b (lb_remove A LB).
Proof.
  intros A LB b. induction LB as [|x r IH]; cbn [lb_remove]; [tauto|]. intros Hin Hne.
  destruct (Z.eqb_spec (fst x) A) as [E|E].
  - destruct Hin as [<-|Hin]; [contradiction|exact Hin].
  - destruct Hin as [<-|Hin]; [left; reflexivity | right; exact (IH Hin Hne)].
Qed.
Lemma lb_remove_fst : forall A (LB : list (Z * Z)), NoDup (map fst LB) -> ~ In A (map fst (lb_remove A LB)).
Proof.
  intros A LB. induction LB as [|x r IH]; cbn [lb_remove map]; [intros _ []|]. intros Hnd. apply list_relations.list.NoDup_cons in Hnd as [Hx Hr]. rewrite list_elem_of_In in Hx.
  destruct (Z.eqb_spec (fst x) A) as [E|E].
  - rewrite <- E. exact Hx.
  - cbn [map In]. intros [H|H]; [exact (E H) | exact (IH Hr H)].
Qed.
Lemma lb_remove_nodup : forall A (LB : list (Z * Z)), NoDup (map fst LB) -> NoDup (map fst (lb_remove A LB)).
Proof.
  intros A LB. induction LB as [|x r IH]; cbn [lb_remove map]; [intros; constructor|]. intros Hnd. apply list_relations.list.NoDup_cons in Hnd as [Hx Hr].
  destruct (Z.eqb (fst x) A); [exact Hr|]. cbn [map]. apply list_relations.list.NoDup_cons. split; [|exact (IH Hr)].
  rewrite list_elem_of_In in Hx |- *. intros H. apply Hx. apply in_map_iff in H as (b & Hb & Hin). apply in_map_iff. exists b. split; [exact Hb | exact (lb_remove_In A r b Hin)].
Qed.
Lemma nodup_fst_eq : forall (LB : list (Z * Z)) b b', NoDup (map fst LB) -> In b LB -> In b' LB -> fst b = fst b' -> b = b'.
Proof.
  induction LB as [|x r IH]; intros b b' Hnd Hb Hb' He; [destruct Hb|]. cbn [map] in Hnd. apply list_relations.list.NoDup_cons in Hnd as [Hx Hr]. rewrite list_elem_of_In in Hx.
  destruct Hb as [<-|Hb]; destruct Hb' as [<-|Hb'].
  - reflexivity.
  - exfalso. apply Hx. rewrite He. apply in_map. exact Hb'.
  - exfalso. apply Hx. rewrite <- He. apply in_map. exact Hb.
  - exact (IH b b' Hr Hb Hb' He).
Qed.

Section PushBackL.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps GK.RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom GK.RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom GK.RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis OPNEWXU : PMES.opnew_x_specU L HI.
Definition CredU (n : Z) (cr0 : credit) (i : nat) (E : env) (cr : credit) : Prop := cr = if pre i then cr0 else debit L cr0 n.

Lemma push_back_grow_xU : forall (LB : list (Z * Z)) (cr : credit) (o cap p c sp r : Z) (s : list Z),
  PML.cps_heap L HI PML.PC_STR_PUSH_BACK r sp PMS.STR_SCR LB cr
      (fun R M => (24 <= cap /\ Z.of_nat (length s) + 1 = cap) /\ PML.entry L R M sp r PMS.STR_SCR /\ PML.a0 R o /\ PML.a1 R c /\ 0 <= c < 256 /\ PML.str_at M o (PML.SLong cap p s) /\
                  In (p, cap) LB /\ PML.obj_on_stack L sp o 24 /\
                  credit_ok L cr (PML.grow_cap cap (Z.of_nat (length (s ++ [c])))) /\ PML.grow_cap cap (Z.of_nat (length (s ++ [c]))) <= NBU)
      (fun R M R' M' LB' cr' LBk W =>
         (exists p', let cap' := PML.grow_cap cap (Z.of_nat (length (s ++ [c]))) in
            PML.str_at M' o (PML.SLong cap' p' (s ++ [c])) /\ L5C.fresh_block L LB M' p' cap' /\
            LB' = (p', cap') :: lb_remove p LB /\ cr' = debit L cr cap' /\ LBk = lb_remove p LB) /\ W = [(o, 24)]).
Proof.
  intros LB cr o cap p c sp r s. unfold PML.cps_heap.
  intros fx R M model K HH Hmo HKnil Hfp ((Hcap & Hlen) & Hentry & Ha0 & Ha1 & Hc & Hstr & HinLB & Hobj & Hcredit & HNB) Hcont.
  destruct Hentry as (Hra & Hraok & Hsp & Htp & Hstk). destruct Hstk as (S1 & S2 & S3 & S4 & S5).
  unfold PMS.STR_SCR, PMS.OPNEW_SCR, PML.HEAP_STACK in *.
  destruct Hstr as ((Hodd & Hw0 & Hw8 & Hw16 & Hbs & Hnul) & Hc8 & Hslt).
  destruct Hobj as (O1 & O2 & O3).
  pose proof (PmLayout.ly_segs L LAY) as LS. pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI. pose proof (PmLayout.ly_stack L LAY) as LSTK. unfold PML.HEAP_STACK in LSTK.
  pose proof (hl_ceil_eq L) as CEQ.
  assert (Hdo : L5.defined M o 24).
  { apply GK.defined_3x8; [exact (GK.defined_of_u64 M o _ Hw0 ltac:(unfold GK.HULL_HI; lia) ltac:(lia))
                          | exact (GK.defined_of_u64 M (o + 8) _ Hw8 ltac:(unfold GK.HULL_HI; lia) ltac:(lia))
                          | exact (GK.defined_of_u64 M (o + 16) _ Hw16 ltac:(unfold GK.HULL_HI; lia) ltac:(lia))]. }
  assert (LEN1 : Z.of_nat (length (s ++ [c])) = Z.of_nat (length s) + 1) by (rewrite length_app, Nat2Z.inj_add; cbn [length]; lia).
  rewrite LEN1 in Hcredit, HNB.
  destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hwf & Hnd & _).
  destruct (Hwf (p, cap) HinLB) as ((P0 & P1 & P2 & P3 & P4) & Pdef & Pap). cbn [fst snd] in P0, P1, P2, P3, P4, Pdef, Pap.
  assert (PdefL : L5.defined M p cap) by exact Pdef.
  assert (HH' : hi_heap HI ((p, cap) :: lb_remove p LB) cr M (m_vmmaps model)).
  { apply (hio_perm L SCFG HI HIok LB _ cr M _ HH).
    - intros b. split.
      + intros Hb. destruct (Z.eq_dec (fst b) p) as [E|E].
        * left. exact (nodup_fst_eq LB (p, cap) b Hnd HinLB Hb (eq_sym E)).
        * right. exact (lb_remove_In_ne p LB b Hb E).
      + intros [<-|Hb]; [exact HinLB | exact (lb_remove_In p LB b Hb)].
    - cbn [map]. apply list_relations.list.NoDup_cons. split; [rewrite list_elem_of_In; exact (lb_remove_fst p LB Hnd) | exact (lb_remove_nodup p LB Hnd)]. }
  set (k := cap / 2).
  assert (Hk : cap = 2 * k) by (unfold k; Z.div_mod_to_equations; lia).
  assert (QB : 8 * ((4 * k - 2) / 8) <= 4 * k - 2 < 8 * ((4 * k - 2) / 8) + 8) by (Z.div_mod_to_equations; lia).
  set (cap' := PML.grow_cap cap (Z.of_nat (length s) + 1)) in *.
  assert (GC : cap' = 8 * ((4 * k - 2) / 8) + 8).
  { unfold cap', PML.grow_cap. rewrite Z.max_r by lia. rewrite CL5.lor7 by lia. replace (2 * (cap - 1)) with (4 * k - 2) by lia. lia. }
  set (E0 := Env (reg_ev R (fun v => if Nat.eqb v 32 then Z_to_bv 64 k else if Nat.eqb v 34 then Z_to_bv 64 p else Z_to_bv 64 0)) (fun id => nth id [map (Z_to_bv 8) s] [])).
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
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= 0x7fff7f800000) by (rewrite ILO, IHI; lia).
  assert (LYE : hl_img_lo L <= hl_errno L /\ hl_errno L + 4 <= hl_img_hi L) by (rewrite ILO, IHI, (PmLayout.ly_errno L LAY); lia).
  assert (STKF : sp mod 16 = 0 /\ hl_ceil L + CH.hd_scr G.HDECL <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47)
    by (change (CH.hd_scr G.HDECL) with SCRT; unfold SCRT; repeat split; lia).
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (change (CH.hd_scr G.HDECL) with SCRT; unfold SCRT; lia).
  assert (NF32 : (32 <= GT.NF)%nat) by (unfold GT.NF; lia).
  assert (SCR : CH.hd_scr G.HDECL = 8304) by (change (CH.hd_scr G.HDECL) with SCRT; unfold SCRT; reflexivity).
  assert (U32 : bv_unsigned (ev E0 32) = k) by (rewrite V32; apply u64_of_Z; lia).
  assert (U34 : bv_unsigned (ev E0 34) = p) by (rewrite V34; apply u64_of_Z; lia).
  assert (FR : forall E1, env_agree GT.NF E0 E1 ->
            bv_unsigned (ev E1 2) = sp /\ bv_unsigned (ev E1 10) = o /\ bv_unsigned (ev E1 11) = c /\ bv_unsigned (ev E1 32) = k /\ bv_unsigned (ev E1 34) = p /\ eb E1 = eb E0).
  { intros E1 [A B]. rewrite <- !A by (unfold GT.NF; lia). repeat split; try assumption. symmetry. exact B. }
  assert (NEWV : forall E1, env_agree GT.NF E0 E1 -> bv_unsigned (edenot E1 NEWCAP) = cap').
  { intros E1 HA. destruct (FR E1 HA) as (_ & _ & _ & F32 & _).
    assert (UC : bv_unsigned (edenot E1 CAP2) = 4 * k - 2) by (apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia]).
    rewrite GC. unfold NEWCAP. cbn [edenot]. rewrite u_add64, u_mul64, u_srl64, UC. rewrite !u_small by lia.
    change (2 ^ (3 mod 64)) with 8. rewrite (Z.mod_small (8 * ((4 * k - 2) / 8))) by lia. rewrite Z.mod_small by lia. reflexivity. }
  assert (W_OK : forall (w : L5.range) (a : Z), In w [(o, 24)] -> L5.in_rng w a -> CH2.wclient L sp a).
  { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. split; [lia | left; lia]. }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> exists w : L5.range, In w [(o, 24)] /\ L5.in_rng w a)).
  { intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CH2.in_reg, estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha.
    rewrite U10 in Ha. rewrite u64_of_Z in Ha by lia. exists (o, 24). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia]. }
  unfold PML.cfg. change PML.PC_STR_PUSH_BACK with (CC.cp_pc G.cp0). rewrite <- LS.
  eapply CH2.heap_cert_sound with (NF := GT.NF) (E0 := E0) (M0 := M) (model0 := model) (LBrest := lb_remove p LB) (sp0 := sp) (d := G.HDECL)
    (W := [(o, 24)]) (BLS := G.BLS) (Cred := CredU cap' cr) (CPS := G.CPS) (TAGS := G.TAGS) (RETS := G.RETS) (MALLOC := MALLOC) (FREE := FREE)
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
  -
    intros i c0 kk ps j cj IL Hret Hcj E E' R' M1 M1' cr' HagE Hag HLF HC. exfalso.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_g_ok _ _ _ _ _ IL) as X. unfold leaf_g in X.
    change (CH2.is_call MALLOC FREE [MEMMOVE] MALLOC) with true in X. cbv beta iota in X. rewrite Hret in X. rewrite Z.eqb_refl in X. discriminate X.
  -
    intros i c0 kk ps pc j cj IL Hcall Hnm Hret Hcj E E' R' M1 M1' cr' HagE Hag HLF HC E2 Hag2.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_g_ok _ _ _ _ _ IL) as X. unfold leaf_g in X. rewrite Hcall, Hret in X.
    apply andb_prop in X as [X Z1]. apply andb_prop in X as [_ XM]. apply negb_true_iff in XM, Z1.
    unfold CredU in *. rewrite Z1. rewrite XM in HC. exact HC.
  -
    intros i c0 kk ps pc IL Hnc.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_g_ok _ _ _ _ _ IL) as X. unfold leaf_g in X. rewrite Hnc in X.
    destruct (Z.eqb_spec pc OPNEW) as [->|Hno].
    { destruct (CH2.ret_of G.RETS i kk) as [j|] eqn:Hret; [|discriminate]. destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate].
      repeat (apply andb_prop in X as [X ?Y]).
      apply negb_true_iff in Y3. apply Z.eqb_eq in Y2. apply Nat.leb_le in Y1. apply expr_eqb_eq in Y0.
      destruct (EON.opnew_chk GT.NF G.HDECL c0 ps cj (nth i G.BLS []) (nth j G.BLS [])) as [ci|] eqn:Hchk; [|discriminate].
      set (XI := fun (_ : nat) (_ : env) (_ : PML.mem) => True).
      assert (DEF0 : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)).
      { change (CH.hd_scr G.HDECL) with SCRT. unfold SCRT. intros j0 Hj0. replace (sp - 8304 + j0) with (sp - (256 + (16 + 8224)) + (j0 + 192)) by lia. apply S5. lia. }
      assert (TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite V4, (PmLayout.ly_tp L LAY); reflexivity).
      assert (LO : CC.leaf_ok (hl_segs L) G.CPS (CH2.amb3 L HI GT.NF E0 M model (lb_remove p LB) sp G.HDECL [(o, 24)] G.BLS (CredU cap' cr) XI) K PML.fp_ok i c0 ps).
      { apply (EONU.opnew_leaf_okU L HI HIok LAY GT.NF E0 M model (lb_remove p LB) sp G.HDECL [(o, 24)] G.BLS (CredU cap' cr) STKF SCRP NF32 U2 TP0 W_OK
                 ltac:(intros rg []) WRS_OK ltac:(intros rg a []) G.CPS G.TAGS G.RETS K HKnil XI DEF0 OPNEWXU i c0 kk ps j cj ci IL Hret Hcj Y2 Hchk); [|intros; exact I].
        intros E E' R' M1 M1' cr1 HagE' Hag HLF HC. unfold CredU in HC. rewrite X in HC. subst cr1.
        rewrite Y0. unfold EON.uv, PB.uv. rewrite (NEWV E' HagE').
        split; [split; [rewrite GC; lia | exact HNB]|]. split; [exact Hcredit|]. intros E2 _. unfold CredU. rewrite Y3. reflexivity. }
      intros fx' E R1 M1 m1 E' R' M' HAt HAmb HFP Hag HLF HIH.
      apply (LO fx' E R1 M1 m1 E' R' M' HAt (conj HAmb I) HFP Hag HLF).
      intros j0 cj0 fx2 E2 R2 M2 model2 Hcj0 HAt2 [HA2 _] HFP2 Hlt. exact (HIH j0 cj0 fx2 E2 R2 M2 model2 Hcj0 HAt2 HA2 HFP2 Hlt). }
    cbv iota in X.
    intros fx' E R1 M1 m1 E' R' M' HAt HAmb HFP Hag HLF _. unfold exit_g in X.
    pose proof (CH2.exit_amb L HI HIok LYI LYE (PmLayout.ly_ro L LAY) GT.NF E0 M model (lb_remove p LB) sp G.HDECL [(o, 24)] G.BLS (CredU cap' cr) STKF SCRP NF32 U2 W_OK WRS_OK
                  G.CPS GK.HULL_LO GK.HULL_HI G.TAGS G.RETS MALLOC FREE [MEMMOVE] heap_ok_g i c0 kk ps pc IL Hnc E E' R1 R' M1 M' m1 HAt HAmb Hag HLF) as HA'.
    repeat (apply andb_prop in X as [X ?Y]).
    apply Z.eqb_eq in X. apply Nat.leb_le in Y10. apply negb_true_iff in Y9. apply expr_eqb_eq in Y1.
    pose proof HA' as HA2. destruct HA' as (Hmo1 & Hbv1 & HagE1 & (cr1 & HH1 & HC1) & Hfr1 & Hdf1).
    assert (HagE' : env_agree GT.NF E0 E') by (eapply CC.env_agree_trans; [exact HagE1 | eapply CC.env_agree_le; [exact Hag | exact Y10]]).
    destruct (FR E' HagE') as (F2 & F10 & F11 & F32 & F34 & FB).
    rewrite LS in HLF.
    assert (CELL : forall X0, has (SR.ps_cells ps) X0 = true -> kentry_ok GK.RSEGS E' M' X0).
    { intros X0 HX. apply (CC.lf_cells _ _ _ _ _ _ _ HLF). exact (GK.has_In _ _ HX). }
    unfold hd_base, hd_size in *. destruct (nth i G.BLS []) as [|[pe ce] [|]] eqn:HBL; try discriminate Y8. cbn [hd fst snd] in *. subst ce.
    destruct pe as [? | v | ? ? ? | ? ? ? | ? ? ? | ? ? ? | ? ? ? ? | ? ? ? ?]; try discriminate Y. apply Nat.leb_le in Y.
    set (pX := bv_unsigned (edenot E' (EVar v))) in *.
    assert (UPX : bv_unsigned (ev E' v) = pX) by reflexivity.
    assert (NV : bv_unsigned (edenot E' NEWCAP) = cap') by exact (NEWV E' HagE').
    assert (CAPV : bv_unsigned (edenot E' CAP) = cap) by (apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia]).
    assert (HH2 : hi_heap HI ((pX, cap') :: lb_remove p LB) cr1 M' (m_vmmaps m1)).
    { unfold CH2.cur in HH1. rewrite HBL in HH1. rewrite <- (CH2.den_agree _ E E' _ Hag Y11) in HH1. rewrite <- NV. exact HH1. }
    destruct (hio_wf L SCFG HI HIok _ _ _ _ HH2) as (Hwf2 & Hnd2 & _).
    destruct (Hwf2 (pX, cap') (or_introl eq_refl)) as ((Q0 & Q1 & Q2 & Q3 & Q4) & Qdef & Qap). cbn [fst snd lb_remove] in Q0, Q1, Q2, Q3, Q4, Qdef, Qap. rewrite Z.eqb_refl in Qap.
    assert (W0V : bv_unsigned (edenot E' (APC.eaddz NEWCAP 1)) = cap' + 1).
    { change (APC.eaddz NEWCAP 1) with (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EAlu ALU_SRL CAP2 (ELit 3))) (ELit 9)).
      assert (UC : bv_unsigned (edenot E' CAP2) = 4 * k - 2) by (apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia]).
      cbn [edenot]. rewrite u_add64, u_mul64, u_srl64, UC. rewrite !u_small by lia. change (2 ^ (3 mod 64)) with 8. rewrite GC.
      rewrite (Z.mod_small (8 * ((4 * k - 2) / 8))) by lia. rewrite Z.mod_small by lia. lia. }
    assert (W0 : L5.u64_at GK.RSEGS M' o (cap' + 1)).
    { apply (CL5.kword64_elim GK.RSEGS E' M' _ _ o _ (CELL _ Y7)); [unfold estart, e_o; cbn [a_base a_off edenot]; rewrite F10; lia | exact W0V]. }
    assert (W8 : L5.u64_at GK.RSEGS M' (o + 8) cap).
    { apply (CL5.kword64_elim GK.RSEGS E' M' _ _ (o + 8) _ (CELL _ Y6)); [unfold estart, e_o; cbn [a_base a_off edenot]; rewrite F10; lia | exact CAPV]. }
    assert (W16 : L5.u64_at GK.RSEGS M' (o + 16) pX).
    { apply (CL5.kword64_elim GK.RSEGS E' M' _ _ (o + 16) _ (CELL _ Y5)); [unfold estart, e_o; cbn [a_base a_off edenot]; rewrite F10; lia | reflexivity]. }
    assert (BS : L5.bytes_at GK.RSEGS M' pX s).
    { apply (CL5.kblob_elim GK.RSEGS E' M' _ _ 0%nat pX s (CELL _ Y4)); [unfold estart; cbn [a_base a_off]; fold pX; lia | rewrite FB; reflexivity]. }
    assert (EST : forall off, estart E' (SA (APC.eadd CAP (EVar v)) off) = pX + cap + off).
    { intros off. unfold estart. cbn [a_base a_off]. unfold APC.eadd. rewrite mkAlu_denot. cbn [edenot].
      rewrite u_add64, CAPV, UPX. rewrite Z.mod_small by lia. lia. }
    assert (BC : L5.u8_at GK.RSEGS M' (pX + cap - 1) c).
    { apply (GK.kword8_elim E' M' _ _ (pX + cap - 1) c (CELL _ Y3)); [rewrite EST; lia | exact F11]. }
    assert (NUL : L5.u8_at GK.RSEGS M' (pX + cap) 0).
    { apply (CL5.kword8_zero_elim GK.RSEGS E' M' _ _ (CELL _ Y2)). rewrite EST. lia. }
    assert (KD : pX + cap' <= p \/ p + cap <= pX).
    { pose proof (CELL _ Y0) as KD. cbn [kentry_ok] in KD. unfold estart, elenZ, e_p in KD. cbn [a_base a_off edenot] in KD.
      rewrite UPX, F34, NV, CAPV in KD. lia. }
    assert (ODD : Z.testbit (cap' + 1) 0 = true).
    { rewrite Z.bit0_odd. apply Z.odd_spec. exists (4 * ((4 * k - 2) / 8) + 4). rewrite GC. lia. }
    assert (STR : PML.str_at M' o (PML.SLong cap' pX (s ++ [c]))).
    { split; [|split; [rewrite GC; replace (8 * ((4 * k - 2) / 8) + 8) with (((4 * k - 2) / 8 + 1) * 8) by ring; apply Z_mod_mult | rewrite LEN1, GC; lia]].
      unfold L5.lstr_long. rewrite LEN1.
      split; [exact ODD|]. split; [exact W0|]. split; [replace (Z.of_nat (length s) + 1) with cap by lia; exact W8|]. split; [exact W16|].
      split; [|replace (pX + (Z.of_nat (length s) + 1)) with (pX + cap) by lia; exact NUL].
      apply CL5.bytes_at_app; [exact BS|]. intros j Hj. cbn [length] in Hj. assert (j = 0%nat) by lia. subst j. cbn [nth]. rewrite Z.add_0_r.
      replace (pX + Z.of_nat (length s)) with (pX + cap - 1) by lia. exact BC. }
    assert (FRESH : L5C.fresh_block L LB M' pX cap').
    { split; [repeat split; assumption|]. split; [|exact Qdef].
      intros b Hb. destruct (Z.eq_dec (fst b) p) as [E1|E1].
      - rewrite <- (nodup_fst_eq LB (p, cap) b Hnd HinLB Hb (eq_sym E1)). cbn [fst snd]. exact KD.
      - exact (Qap b (lb_remove_In_ne p LB b Hb E1)). }
    assert (KEEP : forall y : reg, In (ridx y) CSAVED -> getr R' y = getr R y).
    { intros y Hy. assert (Hy32 : (ridx y < GT.NF)%nat) by (unfold CSAVED, CL5.CSAVED in Hy; cbn [In] in Hy; unfold GT.NF; intuition lia).
      rewrite (CL.ps_keeps_sound GK.RSEGS c0 ps E0 E' R' M1 M' CSAVED GT.NF y HLF Y12 HagE' Hy Hy32). exact (EV y). }
    assert (HRP : regs_preserved R R') by (intros y Hy; apply KEEP; exact (CL5.csaved_in y Hy)).
    assert (Hra' : getr R' 1%bv = Z_to_bv 64 r) by (rewrite (KEEP 1%bv ltac:(left; reflexivity)); exact Hra).
    assert (Hds : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)).
    { change (CH.hd_scr G.HDECL) with SCRT. unfold SCRT. intros j Hj. replace (sp - 8304 + j) with (sp - (256 + (16 + 8224)) + (j + 192)) by lia. apply S5. lia. }
    pose proof (CH2.amb_hpres L HI LYI LYE GT.NF E0 M model (lb_remove p LB) sp G.HDECL [(o, 24)] G.BLS (CredU cap' cr) STKF NF32 i E M' m1 HA2 Hds) as HP0.
    change (CH.hd_scr G.HDECL) with SCRT in HP0.
    assert (HP : L5C.hpres L (lb_remove p LB) sp (256 + (16 + 8224)) [(o, 24)] M M').
    { apply (GK.hpres_scr L _ sp SCRT); [unfold SCRT; lia | exact S5 | lia | rewrite (PmLayout.ly_errno L LAY); lia | lia | lia | exact HP0]. }
    rewrite X, LS. eapply CL.ret_cps; [exact ret_at | exact (proj1 Hmo1) | exact (proj1 (proj2 Hmo1)) | |].
    { rewrite Hra'. apply Hoare.ret_ok_even. destruct Hraok as [R1' R2']. rewrite u64_of_Z by lia. exact R2'. }
    rewrite Hra'.
    assert (Hcr : cr1 = debit L cr cap') by (unfold CredU in HC1; rewrite Y9 in HC1; exact HC1).
    subst cr1.
    apply (Hcont fx' R' M' m1 ((pX, cap') :: lb_remove p LB) (debit L cr cap') (lb_remove p LB) [(o, 24)] HFP); [| exact HRP | exact HP | exact Hbv1 | exact HH2].
    split; [|reflexivity]. exists pX. cbv zeta. rewrite LEN1.
    split; [exact STR|]. split; [exact FRESH|]. split; [reflexivity|]. split; reflexivity.
  - reflexivity.
  -
    rewrite LS.
    assert (Hds : L5.defined M (sp - 8304) 8304) by (intros i Hi; replace (sp - 8304 + i) with (sp - (256 + (16 + 8224)) + (i + 192)) by lia; apply S5; lia).
    split; [exact (regs_ok_id R _ _)|]. unfold know_ok, G.cp0. cbn [CC.cp_know].
    repeat (apply Forall_cons); [.. | apply Forall_nil].
    + eapply CL5.kword64_intro with (A := o) (z := cap + 1); [ev_start | lia | lia | apply bv_eq; rewrite u64_of_Z by lia; apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia] | exact Hw0].
    + eapply CL5.kword64_intro with (A := o + 8) (z := Z.of_nat (length s)); [ev_start | lia | lia | apply bv_eq; rewrite u64_of_Z by lia; apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia] | exact Hw8].
    + eapply CL5.kword64_intro with (A := o + 16) (z := p); [ev_start | lia | lia | exact V34 | exact Hw16].
    + e_range.
    + e_range.
    + eapply CL5.kblob_intro with (bs := s) (A := p); [ev_start | apply CL5.elen_lin; [lin_eval; rw_atoms; lia | lia] | lia | lia | lia | reflexivity | exact Hbs | intros j Hj; apply PdefL; lia].
    + e_unk. + e_wr. + e_range. + e_align P2.
    + e_unk. + e_wr. + e_range. + e_align O3.
    + e_unk. + e_wr. + e_range. + e_align S1.
    + e_disj. + e_disj. + e_disj.
  -
    split; [exact Hmo|]. split; [apply L5C.model_but_vm_refl|]. split; [apply CC.env_agree_refl|].
    split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
    assert (DEN0 : CH2.den E0 (nth 0 G.BLS []) = [(p, cap)]).
    { change (nth 0 G.BLS []) with [(EVar 34, EMd M_MUL (ELit 2) (EVar 32))]. unfold CH2.den. cbn [map fst snd].
      f_equal. f_equal; [exact U34 | apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia]]. }
    exists cr. split; [|reflexivity]. unfold CH2.cur. rewrite DEN0. exact HH'.
  - exact Hfp.
Qed.
End PushBackL.
End EPLU.
