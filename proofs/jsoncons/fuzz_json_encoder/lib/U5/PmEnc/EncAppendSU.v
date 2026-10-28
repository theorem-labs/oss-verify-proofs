(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6Sums_u5 Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Cut_str_append_x_zero_sso_xsrc_T_u5 Cut_str_append_x_zero_sso_xsrc_u5 Cut_str_append_x_sso_xsrc_T_u5 Cut_str_append_x_sso_xsrc_u5
  Cut_str_append_x_sso_grow48_xsrc_T_u5 Cut_str_append_x_sso_grow48_xsrc_u5 Cut_str_append_x_sso_growN_xsrc_T_u5 Cut_str_append_x_sso_growN_xsrc_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutDemo Require Pm6Memmove_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmGrow Require Import GrowKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncSums_u5 EncOpNew_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmEnc Require Import EncCopyX. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncAppendK_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncAppendS_u5 EncOpNewU.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.Heap Require Import HeapIfaceU.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module EASU.
Import EAS.

Definition GXS : expr := EAlu ALU_ADD (EVar 12) (EVar 32).

Section AppendSU.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps GK.RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom GK.RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom GK.RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis OPNEWXU : PMES.opnew_x_specU L HI.
Definition CredU (n : Z) (cr0 : credit) (i : nat) (E : env) (cr : credit) : Prop := cr = if pre i then cr0 else debit L cr0 n.

Lemma append_sso_grow48_xU : forall (LB : list (Z * Z)) (cr : credit) (o q sp r : Z) (s src : list Z),
  PML.cps_heap L HI PML.PC_STR_APPEND r sp PMS.STR_SCR LB cr
      (fun R M => (1 <= PMES.len src /\ 23 <= PMES.len s + PMES.len src <= 44) /\ PML.entry L R M sp r PMS.STR_SCR /\ PML.a0 R o /\ PML.a1 R q /\ PML.a2 R (PMES.len src) /\
                  PML.str_at M o (PML.SShort s) /\ L5.defined M o 24 /\ PML.obj_on_stack L sp o 24 /\
                  L5.bytes_at GK.RSEGS M q src /\ PMES.src_ok L M LB sp o (PML.SShort s) q (PMES.len src) /\
                  credit_ok L cr (PML.grow_cap 23 (PMES.len s + PMES.len src)) /\ PML.grow_cap 23 (PMES.len s + PMES.len src) <= NBU)
      (fun R M R' M' LB' cr' LBk W =>
         (exists p' s', let cap' := PML.grow_cap 23 (PMES.len s + PMES.len src) in
            PMES.len s' = PMES.len s + PMES.len src /\ PML.str_at M' o (PML.SLong cap' p' s') /\ L5C.fresh_block L LB M' p' cap' /\
            LB' = (p', cap') :: LB /\ cr' = debit L cr cap' /\ LBk = LB) /\ W = [(o, 24)]).
Proof.
  intros LB cr o q sp r s src. unfold PML.cps_heap.
  intros fx R M model K HH Hmo HKnil Hfp ((Hn1 & Hgrow) & Hentry & Ha0 & Ha1 & Ha2 & Hstr & Hdo & Hobj & Hbytes & Hsrc & Hcredit & HNB) Hcont.
  destruct Hentry as (Hra & Hraok & Hsp & Htp & Hstk). destruct Hstk as (S1 & S2 & S3 & S4 & S5).
  unfold PMS.STR_SCR, PMS.OPNEW_SCR, PML.HEAP_STACK in *.
  destruct (EAK.short_word0 M o s Hstr Hdo) as (u & Hu & Hw0).
  destruct Hstr as (Hlen22 & Hb0 & Hbs & Hnul).
  destruct Hobj as (O1 & O2 & O3).
  pose proof (PmLayout.ly_segs L LAY) as LS. pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI. pose proof (PmLayout.ly_stack L LAY) as LSTK. unfold PML.HEAP_STACK in LSTK.
  pose proof (hl_ceil_eq L) as CEQ.
  set (size := PMES.len s) in *. set (n := PMES.len src) in *.
  assert (SZE : size = Z.of_nat (length s)) by reflexivity. assert (NE : n = Z.of_nat (length src)) by reflexivity.
  assert (SZ0 : 0 <= size) by (unfold size, PMES.len; lia).
  destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hwf & Hnd & _).
  assert (Hbr : forall b, In b LB -> block_range L (fst b) (snd b) /\ blocks_apart (fst b) (snd b) (lb_remove (fst b) LB)).
  { intros b Hb. destruct (Hwf b Hb) as (B1 & _ & B3). split; assumption. }
  assert (HndL : List.NoDup (map fst LB)) by (apply base.NoDup_ListNoDup; exact Hnd).
  assert (CLO : 0x7fff7f800000 <= hl_ceil L) by lia.
  assert (HKEPT : forall a, q <= a < q + n -> L5C.kept L (PMES.lb_drop (PML.SShort s) LB) sp SCRT [(o, 24)] a).
  { apply (EAK.src_kept L LAY M LB sp o (PML.SShort s) q n SCRT Hsrc Hn1); [unfold SCRT; lia | unfold SCRT; lia | lia | rewrite CEQ; lia | exact O1 | exact O2 | intros b Hb; exact (proj1 (Hbr b Hb)) | exact HndL | exact I]. }
  destruct (EAK.src_range L M LB sp o (PML.SShort s) q n Hsrc Hn1 ltac:(lia) ltac:(lia) (fun b Hb => proj1 (Hbr b Hb)) ltac:(rewrite CEQ; lia)) as (QLO & QHI).
  assert (HRD : exists bs, rdn (hl_segs L) M (Z_to_bv 64 q) (Z.to_nat n) = Some bs /\ length bs = Z.to_nat n).
  { apply (EAK.src_rdn L LAY M q src); [lia | lia | exact Hbytes]. }
  destruct (EAK.src_apart L LAY M LB sp o (PML.SShort s) q n (8384) Hsrc Hn1 ltac:(lia) ltac:(rewrite CEQ; lia) CLO O1 Hbr HndL I) as (AP1 & AP2 & AP3).
  cbv beta iota in AP3. clear Hsrc.
  set (cap' := PML.grow_cap 23 (size + n)) in *.
  assert (GC : cap' = 48) by (unfold cap', PML.grow_cap; rewrite Z.max_r by lia; reflexivity).
  set (E0 := Env (reg_ev R (fun v => if Nat.eqb v 32 then Z_to_bv 64 size else if Nat.eqb v 33 then Z_to_bv 64 u else Z_to_bv 64 0)) (fun id => nth id [] [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 PML.TP) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 o) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (V11 : ev E0 11 = Z_to_bv 64 q) by (rewrite <- Ha1; exact (EV 11%bv)).
  assert (V12 : ev E0 12 = Z_to_bv 64 n) by (rewrite <- Ha2; exact (EV 12%bv)).
  assert (V32 : ev E0 32 = Z_to_bv 64 size) by reflexivity.
  assert (V33 : ev E0 33 = Z_to_bv 64 u) by reflexivity.
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; lia).
  assert (U10 : bv_unsigned (ev E0 10) = o) by (rewrite V10; apply u64_of_Z; lia).
  assert (U11 : bv_unsigned (ev E0 11) = q) by (rewrite V11; apply u64_of_Z; lia).
  assert (U12 : bv_unsigned (ev E0 12) = n) by (rewrite V12; apply u64_of_Z; lia).
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= 0x7fff7f800000) by (rewrite ILO, IHI; lia).
  assert (LYE : hl_img_lo L <= hl_errno L /\ hl_errno L + 4 <= hl_img_hi L) by (rewrite ILO, IHI, (PmLayout.ly_errno L LAY); lia).
  assert (STKF : sp mod 16 = 0 /\ hl_ceil L + CH.hd_scr S48.HDECL <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47)
    by (change (CH.hd_scr S48.HDECL) with SCRT; unfold SCRT; repeat split; lia).
  assert (SCRP : 0 <= CH.hd_scr S48.HDECL) by (change (CH.hd_scr S48.HDECL) with SCRT; unfold SCRT; lia).
  assert (NF32 : (32 <= S48T.NF)%nat) by (unfold S48T.NF; lia).
  assert (HSTKE : hl_stack L = CH.hd_hstk S48.HDECL) by (rewrite LSTK; reflexivity).
  assert (U32 : bv_unsigned (ev E0 32) = size) by (rewrite V32; apply u64_of_Z; lia).
  assert (U33 : bv_unsigned (ev E0 33) = u) by (rewrite V33; apply u64_of_Z; lia).
  assert (FR : forall E1, env_agree S48T.NF E0 E1 ->
            bv_unsigned (ev E1 2) = sp /\ bv_unsigned (ev E1 10) = o /\ bv_unsigned (ev E1 11) = q /\ bv_unsigned (ev E1 12) = n /\ bv_unsigned (ev E1 32) = size /\ bv_unsigned (ev E1 33) = u).
  { intros E1 [A _]. rewrite <- !A by (unfold S48T.NF; lia). repeat split; assumption. }
  assert (NEWV : forall E1, env_agree S48T.NF E0 E1 -> bv_unsigned (edenot E1 NEWCAP_sso_grow48) = cap').
  { intros E1 _. rewrite GC. change NEWCAP_sso_grow48 with (ELit 48). cbn [edenot]. apply u64_of_Z. lia. }
  assert (W_OK : forall (w : L5.range) (a : Z), In w [(o, 24)] -> L5.in_rng w a -> CH2.wclient L sp a).
  { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. split; [lia | left; lia]. }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs S48.HDECL) -> SGP.region_vars_lt S48T.NF rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> exists w : L5.range, In w [(o, 24)] /\ L5.in_rng w a)).
  { intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CH2.in_reg, estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha.
    rewrite U10 in Ha. rewrite u64_of_Z in Ha by lia. exists (o, 24). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia]. }
  unfold PML.cfg. change PML.PC_STR_APPEND with (CC.cp_pc S48.cp0). rewrite <- LS.
  eapply CH2.heap_cert_sound with (NF := S48T.NF) (E0 := E0) (M0 := M) (model0 := model) (LBrest := LB) (sp0 := sp) (d := S48.HDECL)
    (W := [(o, 24)]) (BLS := S48.BLS) (Cred := CredU cap' cr) (CPS := S48.CPS) (TAGS := S48.TAGS) (RETS := S48.RETS) (MALLOC := MALLOC) (FREE := FREE)
    (COPIES := []) (IMG_LO := GK.HULL_LO) (IMG_HI := GK.HULL_HI) (FPI := PML.fp_ok) (i := 0%nat) (E := E0) (HI := HI).
  - exact HIok.
  - exact LYI.
  - exact LYE.
  - exact (PmLayout.ly_ro L LAY).
  - rewrite LSTK. lia.
  - exact STKF.
  - exact SCRP.
  - exact HSTKE.
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
  - rewrite LS. exact S48.plans.
  - exact S48.tags_ok.
  - exact heap_ok_sso_grow48.
  - exact (PmLayout.ly_malloc L LAY).
  - exact (PmLayout.ly_free L LAY).
  - intros pc [].
  - intros i c0 kk ps j sg IL. exfalso. pose proof (CH2.leaves_all_sound _ _ _ no_goto_sso_grow48 _ _ _ _ _ IL) as X. cbv beta iota in X. discriminate X.
  -
    intros i c0 kk ps j cj IL Hret Hcj E E' R' M1 M1' cr' HagE Hag HLF HC. exfalso.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_sso_grow48_ok _ _ _ _ _ IL) as X. unfold leaf_s in X.
    change (CH2.is_call MALLOC FREE [] MALLOC) with true in X. cbv beta iota in X. discriminate X.
  -
    intros i c0 kk ps pc j cj IL Hcall Hnm Hret Hcj E E' R' M1 M1' cr' HagE Hag HLF HC E2 Hag2. exfalso.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_sso_grow48_ok _ _ _ _ _ IL) as X. unfold leaf_s in X. rewrite Hcall in X. cbv beta iota in X. discriminate X.
  -
    intros i c0 kk ps pc IL Hnc.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_sso_grow48_ok _ _ _ _ _ IL) as X. unfold leaf_s in X. rewrite Hnc in X. cbn [Nat.eqb] in X.
    destruct (Z.eqb_spec pc OPNEW) as [->|Hno].
    { destruct (CH2.ret_of S48.RETS i kk) as [j|] eqn:Hret; [|discriminate]. destruct (nth_error S48.CPS j) as [cj|] eqn:Hcj; [|discriminate].
      repeat (apply andb_prop in X as [X ?Y]).
      apply negb_true_iff in Y3. apply Z.eqb_eq in Y2. apply Nat.leb_le in Y1. apply expr_eqb_eq in Y0.
      destruct (EON.opnew_chk S48T.NF S48.HDECL c0 ps cj (nth i S48.BLS []) (nth j S48.BLS [])) as [ci|] eqn:Hchk; [|discriminate].
      set (XI := fun (_ : nat) (_ : env) (_ : PML.mem) => True).
      assert (DEF0 : L5.defined M (sp - CH.hd_scr S48.HDECL) (CH.hd_scr S48.HDECL)).
      { change (CH.hd_scr S48.HDECL) with SCRT. unfold SCRT. intros j0 Hj0. replace (sp - 8384 + j0) with (sp - (256 + (16 + 8224)) + (j0 + 112)) by lia. apply S5. lia. }
      assert (TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite V4, (PmLayout.ly_tp L LAY); reflexivity).
      assert (LO : CC.leaf_ok (hl_segs L) S48.CPS (CH2.amb3 L HI S48T.NF E0 M model LB sp S48.HDECL [(o, 24)] S48.BLS (CredU cap' cr) XI) K PML.fp_ok i c0 ps).
      { apply (EONU.opnew_leaf_okU L HI HIok LAY S48T.NF E0 M model LB sp S48.HDECL [(o, 24)] S48.BLS (CredU cap' cr) STKF SCRP NF32 U2 TP0 W_OK
                 ltac:(intros rg []) WRS_OK ltac:(intros rg a []) S48.CPS S48.TAGS S48.RETS K HKnil XI DEF0 OPNEWXU i c0 kk ps j cj ci IL Hret Hcj Y2 Hchk); [|intros; exact I].
        intros E E' R' M1 M1' cr1 HagE' Hag HLF HC. unfold CredU in HC. rewrite X in HC. subst cr1.
        rewrite Y0. unfold EON.uv, PB.uv. rewrite (NEWV E' HagE').
        split; [split; [rewrite GC; lia | exact HNB]|]. split; [exact Hcredit|]. intros E2 _. unfold CredU. rewrite Y3. reflexivity. }
      intros fx' E R1 M1 m1 E' R' M' HAt HAmb HFP Hag HLF HIH.
      apply (LO fx' E R1 M1 m1 E' R' M' HAt (conj HAmb I) HFP Hag HLF).
      intros j0 cj0 fx2 E2 R2 M2 model2 Hcj0 HAt2 [HA2 _] HFP2 Hlt. exact (HIH j0 cj0 fx2 E2 R2 M2 model2 Hcj0 HAt2 HA2 HFP2 Hlt). }
    cbv iota in X.
    destruct (Z.eqb_spec pc MEMMOVE) as [->|Hmm].
    { destruct (CH2.ret_of S48.RETS i kk) as [j|] eqn:Hret; [|discriminate]. destruct (nth_error S48.CPS j) as [cj|] eqn:Hcj; [|discriminate].
      apply andb_prop in X as [X Xc]. apply andb_prop in X as [Xi Xj]. apply negb_true_iff in Xi, Xj.
      apply (CH2.copy_leaf_ok L HI HIok LYI LYE (PmLayout.ly_ro L LAY) ltac:(rewrite LSTK; lia) S48T.NF E0 M model LB sp S48.HDECL [(o, 24)] S48.BLS (CredU cap' cr)
               STKF SCRP HSTKE NF32 U2 ltac:(rewrite V4, (PmLayout.ly_tp L LAY); reflexivity) W_OK WRS_OK S48.CPS K PML.fp_ok i c0 ps j cj MEMMOVE
               ltac:(rewrite LS; exact FPM) (Pm6Memmove_u5.memmove_copy1 L LS) Hcj Xc).
      intros E E' R' M1 M1' cr1 _ _ _ HC E2 _. unfold CredU in *. rewrite Xi in HC. rewrite Xj. exact HC. }
    cbv iota in X.
    destruct (Z.eqb_spec pc MEMCPY) as [->|Hmc].
    { destruct (CH2.ret_of S48.RETS i kk) as [j|] eqn:Hret; [|discriminate]. destruct (nth_error S48.CPS j) as [cj|] eqn:Hcj; [|discriminate].
      apply andb_prop in X as [X Xc]. apply andb_prop in X as [Xi Xj]. apply negb_true_iff in Xi, Xj.
      assert (MEMCPY1 : CH2.copy1_spec L MEMCPY).
      { apply CH2.copy1_of_copy_spec. intros fx0. rewrite LS. exact (Pm6Sums_u5.src0_copy_spec_memcpy fx0). }
      apply (ECX.copyx_leaf_ok L HI HIok LYI LYE (PmLayout.ly_ro L LAY) ltac:(rewrite LSTK; lia) S48T.NF E0 M model LB sp S48.HDECL [(o, 24)] S48.BLS (CredU cap' cr)
               STKF SCRP HSTKE NF32 U2 ltac:(rewrite V4, (PmLayout.ly_tp L LAY); reflexivity) W_OK WRS_OK S48.CPS K PML.fp_ok i c0 ps j cj MEMCPY e_q e_n q n
               ltac:(rewrite LS; exact FPM) MEMCPY1 Hcj Xc U11 U12 Hn1 ltac:(lia)).
      - change (CH.hd_scr S48.HDECL) with SCRT. exact HKEPT.
      - exact HRD.
      - intros E E' R' M1 M1' cr1 _ _ _ HC E2 _. unfold CredU in *. rewrite Xi in HC. rewrite Xj. exact HC. }
    cbv iota in X.
    clear AP1 AP2 AP3 HKEPT HRD.
    intros fx' E R1 M1 m1 E' R' M' HAt HAmb HFP Hag HLF _. unfold exit_g in X.
    pose proof (CH2.exit_amb L HI HIok LYI LYE (PmLayout.ly_ro L LAY) S48T.NF E0 M model LB sp S48.HDECL [(o, 24)] S48.BLS (CredU cap' cr) STKF SCRP NF32 U2 W_OK WRS_OK
                  S48.CPS GK.HULL_LO GK.HULL_HI S48.TAGS S48.RETS MALLOC FREE [] heap_ok_sso_grow48 i c0 kk ps pc IL Hnc E E' R1 R' M1 M' m1 HAt HAmb Hag HLF) as HA'.
    repeat (apply andb_prop in X as [X ?Y]).
    apply Z.eqb_eq in X. apply Nat.leb_le in Y7. apply negb_true_iff in Y6. apply expr_eqb_eq in Y0.
    pose proof HA' as HA2. destruct HA' as (Hmo1 & Hbv1 & HagE1 & (cr1 & HH1 & HC1) & Hfr1 & Hdf1).
    assert (HagE' : env_agree S48T.NF E0 E') by (eapply CC.env_agree_trans; [exact HagE1 | eapply CC.env_agree_le; [exact Hag | exact Y7]]).
    destruct (FR E' HagE') as (F2 & F10 & F11 & F12 & F32 & F33).
    rewrite LS in HLF.
    assert (CELL : forall X0, has (SR.ps_cells ps) X0 = true -> kentry_ok GK.RSEGS E' M' X0).
    { intros X0 HX. apply (CC.lf_cells _ _ _ _ _ _ _ HLF). exact (GK.has_In _ _ HX). }
    unfold hd_base_g, hd_size_g in *. destruct (nth i S48.BLS []) as [|[pe ce] [|]] eqn:HBL; try discriminate Y5. cbn [hd fst snd] in *. subst ce.
    destruct pe as [? | v | ? ? ? | ? ? ? | ? ? ? | ? ? ? | ? ? ? ? | ? ? ? ?]; try discriminate Y. apply Nat.leb_le in Y.
    set (pX := bv_unsigned (edenot E' (EVar v))) in *.
    assert (UPX : bv_unsigned (ev E' v) = pX) by reflexivity.
    assert (NV : bv_unsigned (edenot E' NEWCAP_sso_grow48) = cap') by exact (NEWV E' HagE').
    assert (HH2 : hi_heap HI ((pX, cap') :: LB) cr1 M' (m_vmmaps m1)).
    { unfold CH2.cur in HH1. rewrite HBL in HH1. rewrite <- (CH2.den_agree _ E E' _ Hag Y8) in HH1. rewrite <- NV. exact HH1. }
    destruct (hio_wf L SCFG HI HIok _ _ _ _ HH2) as (Hwf2 & Hnd2 & _).
    destruct (Hwf2 (pX, cap') (or_introl eq_refl)) as ((Q0 & Q1 & Q2 & Q3 & Q4) & Qdef & Qap). cbn [fst snd lb_remove] in Q0, Q1, Q2, Q3, Q4, Qdef, Qap. rewrite Z.eqb_refl in Qap.
    assert (W0V : bv_unsigned (edenot E' (APC.eaddz NEWCAP_sso_grow48 1)) = cap' + 1).
    { rewrite GC. unfold NEWCAP_sso_grow48. vm_compute. reflexivity. }
    assert (W0 : L5.u64_at GK.RSEGS M' o (cap' + 1)).
    { apply (CL5.kword64_elim GK.RSEGS E' M' _ _ o _ (CELL _ Y4)); [unfold estart, e_o; cbn [a_base a_off edenot]; rewrite F10; lia | exact W0V]. }
    assert (W8 : L5.u64_at GK.RSEGS M' (o + 8) (size + n)).
    { apply (CL5.kword64_elim GK.RSEGS E' M' _ _ (o + 8) _ (CELL _ Y3)); [unfold estart, e_o; cbn [a_base a_off edenot]; rewrite F10; lia | apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia]]. }
    assert (W16 : L5.u64_at GK.RSEGS M' (o + 16) pX).
    { apply (CL5.kword64_elim GK.RSEGS E' M' _ _ (o + 16) _ (CELL _ Y2)); [unfold estart, e_o; cbn [a_base a_off edenot]; rewrite F10; lia | reflexivity]. }
    assert (UEP : estart E' (SA (EAlu ALU_ADD e_n (EAlu ALU_ADD e_size (EVar v))) 0) = pX + (size + n)).
    { unfold estart, e_n, e_size. cbn [a_base a_off edenot]. rewrite !u_add64, F12, F32, UPX.
      rewrite (Z.mod_small (size + pX)) by lia. rewrite Z.mod_small by lia. lia. }
    assert (NUL : L5.u8_at GK.RSEGS M' (pX + (size + n)) 0) by exact (CL5.kword8_zero_elim GK.RSEGS E' M' _ _ (CELL _ Y1) UEP).
    assert (C8 : cap' mod 8 = 0).
    { rewrite GC. reflexivity. }
    assert (LB1 : 0 <= size + n < cap') by (clear - GC Hgrow SZ0 Hn1; lia).
    assert (LB2 : 0 <= pX /\ pX + cap' <= 2 ^ 63) by (clear - Q0 Q4 CEQ S4; lia).
    destruct (EAK.long_intro M' o cap' pX (size + n) W0 W8 W16 NUL Qdef LB1 C8 (proj1 LB2) (proj2 LB2)) as (s' & Hs'len & STR).
    assert (FRESH : L5C.fresh_block L LB M' pX cap').
    { split; [repeat split; assumption|]. split; [|exact Qdef].
      intros b0 Hb0x. destruct b0 as [bb bm]. exact (Qap (bb, bm) Hb0x). }
    assert (KEEP : forall y : reg, In (ridx y) CSAVED -> getr R' y = getr R y).
    { intros y Hy. assert (Hy32 : (ridx y < S48T.NF)%nat) by (unfold CSAVED, CL5.CSAVED in Hy; cbn [In] in Hy; unfold S48T.NF; intuition lia).
      rewrite (CL.ps_keeps_sound GK.RSEGS c0 ps E0 E' R' M1 M' CSAVED S48T.NF y HLF Y9 HagE' Hy Hy32). exact (EV y). }
    assert (HRP : regs_preserved R R') by (intros y Hy; apply KEEP; exact (CL5.csaved_in y Hy)).
    assert (Hra' : getr R' 1%bv = Z_to_bv 64 r) by (rewrite (KEEP 1%bv ltac:(left; reflexivity)); exact Hra).
    assert (Hds : L5.defined M (sp - CH.hd_scr S48.HDECL) (CH.hd_scr S48.HDECL)).
    { change (CH.hd_scr S48.HDECL) with SCRT. unfold SCRT. intros j Hj. replace (sp - 8384 + j) with (sp - (256 + (16 + 8224)) + (j + 112)) by lia. apply S5. lia. }
    pose proof (CH2.amb_hpres L HI LYI LYE S48T.NF E0 M model LB sp S48.HDECL [(o, 24)] S48.BLS (CredU cap' cr) STKF NF32 i E M' m1 HA2 Hds) as HP0.
    change (CH.hd_scr S48.HDECL) with SCRT in HP0.
    assert (HP : L5C.hpres L LB sp (256 + (16 + 8224)) [(o, 24)] M M').
    { apply (GK.hpres_scr L _ sp SCRT); [unfold SCRT; lia | exact S5 | lia | rewrite (PmLayout.ly_errno L LAY); lia | lia | lia | exact HP0]. }
    rewrite X, LS. eapply CL.ret_cps; [exact ret_at | exact (proj1 Hmo1) | exact (proj1 (proj2 Hmo1)) | |].
    { rewrite Hra'. apply Hoare.ret_ok_even. destruct Hraok as [R1' R2']. rewrite u64_of_Z by lia. exact R2'. }
    rewrite Hra'.
    assert (Hcr : cr1 = debit L cr cap') by (unfold CredU in HC1; rewrite Y6 in HC1; exact HC1).
    subst cr1.
    apply (Hcont fx' R' M' m1 ((pX, cap') :: LB) (debit L cr cap') LB [(o, 24)] HFP); [| exact HRP | exact HP | exact Hbv1 | exact HH2].
    split; [|reflexivity]. exists pX, s'. cbv zeta.
    split; [exact Hs'len|]. split; [exact STR|]. split; [exact FRESH|]. split; [reflexivity|]. split; reflexivity.
  - reflexivity.
  -
    rewrite LS.
    assert (Hds : L5.defined M (sp - 8384) 8384) by (intros i Hi; replace (sp - 8384 + i) with (sp - (256 + (16 + 8224)) + (i + 112)) by lia; apply S5; lia).
    split; [exact (regs_ok_id R _ _)|]. unfold know_ok, S48.cp0. cbn [CC.cp_know].
    repeat (apply Forall_cons); [.. | apply Forall_nil].
    + eapply GK.kword8_intro with (A := o) (z := 2 * Z.of_nat (length s)); [ev_start | lia | lia | apply bv_eq; rewrite u64_of_Z by lia; apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia] | lia | exact Hb0].
    + eapply CL5.kword64_intro with (A := o) (z := 2 * Z.of_nat (length s) + 256 * u); [ev_start | lia | lia | apply bv_eq; rewrite u64_of_Z by lia; apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia] | exact Hw0].
    + e_range. + e_range. + e_range. + e_range. + e_range. + e_range.
    + e_unk. + e_wr. + e_range. + e_align O3.
    + e_unk. + e_wr. + e_range. + e_align S1.
    + e_disj. + e_disj. + e_disj.
  -
    split; [exact Hmo|]. split; [apply L5C.model_but_vm_refl|]. split; [apply CC.env_agree_refl|].
    split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
    exists cr. split; [|reflexivity]. unfold CH2.cur. change (nth 0 S48.BLS []) with (@nil (expr * expr)). exact HH.
  - exact Hfp.
Qed.

Lemma append_sso_growN_xU : forall (LB : list (Z * Z)) (cr : credit) (o q sp r : Z) (s src : list Z),
  PML.cps_heap L HI PML.PC_STR_APPEND r sp PMS.STR_SCR LB cr
      (fun R M => (1 <= PMES.len src /\ 45 <= PMES.len s + PMES.len src /\ PMES.len s + PMES.len src < 2 ^ 47) /\ PML.entry L R M sp r PMS.STR_SCR /\ PML.a0 R o /\ PML.a1 R q /\ PML.a2 R (PMES.len src) /\
                  PML.str_at M o (PML.SShort s) /\ L5.defined M o 24 /\ PML.obj_on_stack L sp o 24 /\
                  L5.bytes_at GK.RSEGS M q src /\ PMES.src_ok L M LB sp o (PML.SShort s) q (PMES.len src) /\
                  credit_ok L cr (PML.grow_cap 23 (PMES.len s + PMES.len src)) /\ PML.grow_cap 23 (PMES.len s + PMES.len src) <= NBU)
      (fun R M R' M' LB' cr' LBk W =>
         (exists p' s', let cap' := PML.grow_cap 23 (PMES.len s + PMES.len src) in
            PMES.len s' = PMES.len s + PMES.len src /\ PML.str_at M' o (PML.SLong cap' p' s') /\ L5C.fresh_block L LB M' p' cap' /\
            LB' = (p', cap') :: LB /\ cr' = debit L cr cap' /\ LBk = LB) /\ W = [(o, 24)]).
Proof.
  intros LB cr o q sp r s src. unfold PML.cps_heap.
  intros fx R M model K HH Hmo HKnil Hfp ((Hn1 & Hgrow & H47) & Hentry & Ha0 & Ha1 & Ha2 & Hstr & Hdo & Hobj & Hbytes & Hsrc & Hcredit & HNB) Hcont.
  destruct Hentry as (Hra & Hraok & Hsp & Htp & Hstk). destruct Hstk as (S1 & S2 & S3 & S4 & S5).
  unfold PMS.STR_SCR, PMS.OPNEW_SCR, PML.HEAP_STACK in *.
  destruct (EAK.short_word0 M o s Hstr Hdo) as (u & Hu & Hw0).
  destruct Hstr as (Hlen22 & Hb0 & Hbs & Hnul).
  destruct Hobj as (O1 & O2 & O3).
  pose proof (PmLayout.ly_segs L LAY) as LS. pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI. pose proof (PmLayout.ly_stack L LAY) as LSTK. unfold PML.HEAP_STACK in LSTK.
  pose proof (hl_ceil_eq L) as CEQ.
  set (size := PMES.len s) in *. set (n := PMES.len src) in *.
  assert (SZE : size = Z.of_nat (length s)) by reflexivity. assert (NE : n = Z.of_nat (length src)) by reflexivity.
  assert (SZ0 : 0 <= size) by (unfold size, PMES.len; lia).
  destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hwf & Hnd & _).
  assert (Hbr : forall b, In b LB -> block_range L (fst b) (snd b) /\ blocks_apart (fst b) (snd b) (lb_remove (fst b) LB)).
  { intros b Hb. destruct (Hwf b Hb) as (B1 & _ & B3). split; assumption. }
  assert (HndL : List.NoDup (map fst LB)) by (apply base.NoDup_ListNoDup; exact Hnd).
  assert (CLO : 0x7fff7f800000 <= hl_ceil L) by lia.
  assert (HKEPT : forall a, q <= a < q + n -> L5C.kept L (PMES.lb_drop (PML.SShort s) LB) sp SCRT [(o, 24)] a).
  { apply (EAK.src_kept L LAY M LB sp o (PML.SShort s) q n SCRT Hsrc Hn1); [unfold SCRT; lia | unfold SCRT; lia | lia | rewrite CEQ; lia | exact O1 | exact O2 | intros b Hb; exact (proj1 (Hbr b Hb)) | exact HndL | exact I]. }
  destruct (EAK.src_range L M LB sp o (PML.SShort s) q n Hsrc Hn1 ltac:(lia) ltac:(lia) (fun b Hb => proj1 (Hbr b Hb)) ltac:(rewrite CEQ; lia)) as (QLO & QHI).
  assert (HRD : exists bs, rdn (hl_segs L) M (Z_to_bv 64 q) (Z.to_nat n) = Some bs /\ length bs = Z.to_nat n).
  { apply (EAK.src_rdn L LAY M q src); [lia | lia | exact Hbytes]. }
  destruct (EAK.src_apart L LAY M LB sp o (PML.SShort s) q n (8384) Hsrc Hn1 ltac:(lia) ltac:(rewrite CEQ; lia) CLO O1 Hbr HndL I) as (AP1 & AP2 & AP3).
  cbv beta iota in AP3. clear Hsrc.
  assert (QB : 8 * ((size + n) / 8) <= size + n < 8 * ((size + n) / 8) + 8) by (Z.div_mod_to_equations; lia).
  set (cap' := PML.grow_cap 23 (size + n)) in *.
  assert (GC : cap' = 8 * ((size + n) / 8) + 8).
  { unfold cap', PML.grow_cap. rewrite Z.max_l by lia. rewrite CL5.lor7 by lia. lia. }
  set (E0 := Env (reg_ev R (fun v => if Nat.eqb v 32 then Z_to_bv 64 size else if Nat.eqb v 33 then Z_to_bv 64 u else Z_to_bv 64 0)) (fun id => nth id [] [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 PML.TP) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 o) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (V11 : ev E0 11 = Z_to_bv 64 q) by (rewrite <- Ha1; exact (EV 11%bv)).
  assert (V12 : ev E0 12 = Z_to_bv 64 n) by (rewrite <- Ha2; exact (EV 12%bv)).
  assert (V32 : ev E0 32 = Z_to_bv 64 size) by reflexivity.
  assert (V33 : ev E0 33 = Z_to_bv 64 u) by reflexivity.
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; lia).
  assert (U10 : bv_unsigned (ev E0 10) = o) by (rewrite V10; apply u64_of_Z; lia).
  assert (U11 : bv_unsigned (ev E0 11) = q) by (rewrite V11; apply u64_of_Z; lia).
  assert (U12 : bv_unsigned (ev E0 12) = n) by (rewrite V12; apply u64_of_Z; lia).
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= 0x7fff7f800000) by (rewrite ILO, IHI; lia).
  assert (LYE : hl_img_lo L <= hl_errno L /\ hl_errno L + 4 <= hl_img_hi L) by (rewrite ILO, IHI, (PmLayout.ly_errno L LAY); lia).
  assert (STKF : sp mod 16 = 0 /\ hl_ceil L + CH.hd_scr SGN.HDECL <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47)
    by (change (CH.hd_scr SGN.HDECL) with SCRT; unfold SCRT; repeat split; lia).
  assert (SCRP : 0 <= CH.hd_scr SGN.HDECL) by (change (CH.hd_scr SGN.HDECL) with SCRT; unfold SCRT; lia).
  assert (NF32 : (32 <= SGNT.NF)%nat) by (unfold SGNT.NF; lia).
  assert (HSTKE : hl_stack L = CH.hd_hstk SGN.HDECL) by (rewrite LSTK; reflexivity).
  assert (U32 : bv_unsigned (ev E0 32) = size) by (rewrite V32; apply u64_of_Z; lia).
  assert (U33 : bv_unsigned (ev E0 33) = u) by (rewrite V33; apply u64_of_Z; lia).
  assert (FR : forall E1, env_agree SGNT.NF E0 E1 ->
            bv_unsigned (ev E1 2) = sp /\ bv_unsigned (ev E1 10) = o /\ bv_unsigned (ev E1 11) = q /\ bv_unsigned (ev E1 12) = n /\ bv_unsigned (ev E1 32) = size /\ bv_unsigned (ev E1 33) = u).
  { intros E1 [A _]. rewrite <- !A by (unfold SGNT.NF; lia). repeat split; assumption. }
  assert (NEWV : forall E1, env_agree SGNT.NF E0 E1 -> bv_unsigned (edenot E1 NEWCAP_sso_growN) = cap').
  { intros E1 HA. destruct (FR E1 HA) as (F2 & F10 & F11 & F12 & F32 & F33).
    assert (UC : bv_unsigned (edenot E1 GXS) = size + n) by (unfold GXS; apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia]).
    rewrite GC. change NEWCAP_sso_growN with (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EAlu ALU_SRL GXS (ELit 3))) (ELit 8)). cbn [edenot]. rewrite u_add64, u_mul64, u_srl64, UC. rewrite !u_small by lia.
    change (2 ^ (3 mod 64)) with 8. rewrite (Z.mod_small (8 * ((size + n) / 8))) by lia. rewrite Z.mod_small by lia. reflexivity. }
  assert (W_OK : forall (w : L5.range) (a : Z), In w [(o, 24)] -> L5.in_rng w a -> CH2.wclient L sp a).
  { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. split; [lia | left; lia]. }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs SGN.HDECL) -> SGP.region_vars_lt SGNT.NF rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> exists w : L5.range, In w [(o, 24)] /\ L5.in_rng w a)).
  { intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CH2.in_reg, estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha.
    rewrite U10 in Ha. rewrite u64_of_Z in Ha by lia. exists (o, 24). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia]. }
  unfold PML.cfg. change PML.PC_STR_APPEND with (CC.cp_pc SGN.cp0). rewrite <- LS.
  eapply CH2.heap_cert_sound with (NF := SGNT.NF) (E0 := E0) (M0 := M) (model0 := model) (LBrest := LB) (sp0 := sp) (d := SGN.HDECL)
    (W := [(o, 24)]) (BLS := SGN.BLS) (Cred := CredU cap' cr) (CPS := SGN.CPS) (TAGS := SGN.TAGS) (RETS := SGN.RETS) (MALLOC := MALLOC) (FREE := FREE)
    (COPIES := []) (IMG_LO := GK.HULL_LO) (IMG_HI := GK.HULL_HI) (FPI := PML.fp_ok) (i := 0%nat) (E := E0) (HI := HI).
  - exact HIok.
  - exact LYI.
  - exact LYE.
  - exact (PmLayout.ly_ro L LAY).
  - rewrite LSTK. lia.
  - exact STKF.
  - exact SCRP.
  - exact HSTKE.
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
  - rewrite LS. exact SGN.plans.
  - exact SGN.tags_ok.
  - exact heap_ok_sso_growN.
  - exact (PmLayout.ly_malloc L LAY).
  - exact (PmLayout.ly_free L LAY).
  - intros pc [].
  - intros i c0 kk ps j sg IL. exfalso. pose proof (CH2.leaves_all_sound _ _ _ no_goto_sso_growN _ _ _ _ _ IL) as X. cbv beta iota in X. discriminate X.
  -
    intros i c0 kk ps j cj IL Hret Hcj E E' R' M1 M1' cr' HagE Hag HLF HC. exfalso.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_sso_growN_ok _ _ _ _ _ IL) as X. unfold leaf_s in X.
    change (CH2.is_call MALLOC FREE [] MALLOC) with true in X. cbv beta iota in X. discriminate X.
  -
    intros i c0 kk ps pc j cj IL Hcall Hnm Hret Hcj E E' R' M1 M1' cr' HagE Hag HLF HC E2 Hag2. exfalso.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_sso_growN_ok _ _ _ _ _ IL) as X. unfold leaf_s in X. rewrite Hcall in X. cbv beta iota in X. discriminate X.
  -
    intros i c0 kk ps pc IL Hnc.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_sso_growN_ok _ _ _ _ _ IL) as X. unfold leaf_s in X. rewrite Hnc in X. cbn [Nat.eqb] in X.
    destruct (Z.eqb_spec pc OPNEW) as [->|Hno].
    { destruct (CH2.ret_of SGN.RETS i kk) as [j|] eqn:Hret; [|discriminate]. destruct (nth_error SGN.CPS j) as [cj|] eqn:Hcj; [|discriminate].
      repeat (apply andb_prop in X as [X ?Y]).
      apply negb_true_iff in Y3. apply Z.eqb_eq in Y2. apply Nat.leb_le in Y1. apply expr_eqb_eq in Y0.
      destruct (EON.opnew_chk SGNT.NF SGN.HDECL c0 ps cj (nth i SGN.BLS []) (nth j SGN.BLS [])) as [ci|] eqn:Hchk; [|discriminate].
      set (XI := fun (_ : nat) (_ : env) (_ : PML.mem) => True).
      assert (DEF0 : L5.defined M (sp - CH.hd_scr SGN.HDECL) (CH.hd_scr SGN.HDECL)).
      { change (CH.hd_scr SGN.HDECL) with SCRT. unfold SCRT. intros j0 Hj0. replace (sp - 8384 + j0) with (sp - (256 + (16 + 8224)) + (j0 + 112)) by lia. apply S5. lia. }
      assert (TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite V4, (PmLayout.ly_tp L LAY); reflexivity).
      assert (LO : CC.leaf_ok (hl_segs L) SGN.CPS (CH2.amb3 L HI SGNT.NF E0 M model LB sp SGN.HDECL [(o, 24)] SGN.BLS (CredU cap' cr) XI) K PML.fp_ok i c0 ps).
      { apply (EONU.opnew_leaf_okU L HI HIok LAY SGNT.NF E0 M model LB sp SGN.HDECL [(o, 24)] SGN.BLS (CredU cap' cr) STKF SCRP NF32 U2 TP0 W_OK
                 ltac:(intros rg []) WRS_OK ltac:(intros rg a []) SGN.CPS SGN.TAGS SGN.RETS K HKnil XI DEF0 OPNEWXU i c0 kk ps j cj ci IL Hret Hcj Y2 Hchk); [|intros; exact I].
        intros E E' R' M1 M1' cr1 HagE' Hag HLF HC. unfold CredU in HC. rewrite X in HC. subst cr1.
        rewrite Y0. unfold EON.uv, PB.uv. rewrite (NEWV E' HagE').
        split; [split; [rewrite GC; lia | exact HNB]|]. split; [exact Hcredit|]. intros E2 _. unfold CredU. rewrite Y3. reflexivity. }
      intros fx' E R1 M1 m1 E' R' M' HAt HAmb HFP Hag HLF HIH.
      apply (LO fx' E R1 M1 m1 E' R' M' HAt (conj HAmb I) HFP Hag HLF).
      intros j0 cj0 fx2 E2 R2 M2 model2 Hcj0 HAt2 [HA2 _] HFP2 Hlt. exact (HIH j0 cj0 fx2 E2 R2 M2 model2 Hcj0 HAt2 HA2 HFP2 Hlt). }
    cbv iota in X.
    destruct (Z.eqb_spec pc MEMMOVE) as [->|Hmm].
    { destruct (CH2.ret_of SGN.RETS i kk) as [j|] eqn:Hret; [|discriminate]. destruct (nth_error SGN.CPS j) as [cj|] eqn:Hcj; [|discriminate].
      apply andb_prop in X as [X Xc]. apply andb_prop in X as [Xi Xj]. apply negb_true_iff in Xi, Xj.
      apply (CH2.copy_leaf_ok L HI HIok LYI LYE (PmLayout.ly_ro L LAY) ltac:(rewrite LSTK; lia) SGNT.NF E0 M model LB sp SGN.HDECL [(o, 24)] SGN.BLS (CredU cap' cr)
               STKF SCRP HSTKE NF32 U2 ltac:(rewrite V4, (PmLayout.ly_tp L LAY); reflexivity) W_OK WRS_OK SGN.CPS K PML.fp_ok i c0 ps j cj MEMMOVE
               ltac:(rewrite LS; exact FPM) (Pm6Memmove_u5.memmove_copy1 L LS) Hcj Xc).
      intros E E' R' M1 M1' cr1 _ _ _ HC E2 _. unfold CredU in *. rewrite Xi in HC. rewrite Xj. exact HC. }
    cbv iota in X.
    destruct (Z.eqb_spec pc MEMCPY) as [->|Hmc].
    { destruct (CH2.ret_of SGN.RETS i kk) as [j|] eqn:Hret; [|discriminate]. destruct (nth_error SGN.CPS j) as [cj|] eqn:Hcj; [|discriminate].
      apply andb_prop in X as [X Xc]. apply andb_prop in X as [Xi Xj]. apply negb_true_iff in Xi, Xj.
      assert (MEMCPY1 : CH2.copy1_spec L MEMCPY).
      { apply CH2.copy1_of_copy_spec. intros fx0. rewrite LS. exact (Pm6Sums_u5.src0_copy_spec_memcpy fx0). }
      apply (ECX.copyx_leaf_ok L HI HIok LYI LYE (PmLayout.ly_ro L LAY) ltac:(rewrite LSTK; lia) SGNT.NF E0 M model LB sp SGN.HDECL [(o, 24)] SGN.BLS (CredU cap' cr)
               STKF SCRP HSTKE NF32 U2 ltac:(rewrite V4, (PmLayout.ly_tp L LAY); reflexivity) W_OK WRS_OK SGN.CPS K PML.fp_ok i c0 ps j cj MEMCPY e_q e_n q n
               ltac:(rewrite LS; exact FPM) MEMCPY1 Hcj Xc U11 U12 Hn1 ltac:(lia)).
      - change (CH.hd_scr SGN.HDECL) with SCRT. exact HKEPT.
      - exact HRD.
      - intros E E' R' M1 M1' cr1 _ _ _ HC E2 _. unfold CredU in *. rewrite Xi in HC. rewrite Xj. exact HC. }
    cbv iota in X.
    clear AP1 AP2 AP3 HKEPT HRD.
    intros fx' E R1 M1 m1 E' R' M' HAt HAmb HFP Hag HLF _. unfold exit_g in X.
    pose proof (CH2.exit_amb L HI HIok LYI LYE (PmLayout.ly_ro L LAY) SGNT.NF E0 M model LB sp SGN.HDECL [(o, 24)] SGN.BLS (CredU cap' cr) STKF SCRP NF32 U2 W_OK WRS_OK
                  SGN.CPS GK.HULL_LO GK.HULL_HI SGN.TAGS SGN.RETS MALLOC FREE [] heap_ok_sso_growN i c0 kk ps pc IL Hnc E E' R1 R' M1 M' m1 HAt HAmb Hag HLF) as HA'.
    repeat (apply andb_prop in X as [X ?Y]).
    apply Z.eqb_eq in X. apply Nat.leb_le in Y7. apply negb_true_iff in Y6. apply expr_eqb_eq in Y0.
    pose proof HA' as HA2. destruct HA' as (Hmo1 & Hbv1 & HagE1 & (cr1 & HH1 & HC1) & Hfr1 & Hdf1).
    assert (HagE' : env_agree SGNT.NF E0 E') by (eapply CC.env_agree_trans; [exact HagE1 | eapply CC.env_agree_le; [exact Hag | exact Y7]]).
    destruct (FR E' HagE') as (F2 & F10 & F11 & F12 & F32 & F33).
    rewrite LS in HLF.
    assert (CELL : forall X0, has (SR.ps_cells ps) X0 = true -> kentry_ok GK.RSEGS E' M' X0).
    { intros X0 HX. apply (CC.lf_cells _ _ _ _ _ _ _ HLF). exact (GK.has_In _ _ HX). }
    unfold hd_base_g, hd_size_g in *. destruct (nth i SGN.BLS []) as [|[pe ce] [|]] eqn:HBL; try discriminate Y5. cbn [hd fst snd] in *. subst ce.
    destruct pe as [? | v | ? ? ? | ? ? ? | ? ? ? | ? ? ? | ? ? ? ? | ? ? ? ?]; try discriminate Y. apply Nat.leb_le in Y.
    set (pX := bv_unsigned (edenot E' (EVar v))) in *.
    assert (UPX : bv_unsigned (ev E' v) = pX) by reflexivity.
    assert (NV : bv_unsigned (edenot E' NEWCAP_sso_growN) = cap') by exact (NEWV E' HagE').
    assert (HH2 : hi_heap HI ((pX, cap') :: LB) cr1 M' (m_vmmaps m1)).
    { unfold CH2.cur in HH1. rewrite HBL in HH1. rewrite <- (CH2.den_agree _ E E' _ Hag Y8) in HH1. rewrite <- NV. exact HH1. }
    destruct (hio_wf L SCFG HI HIok _ _ _ _ HH2) as (Hwf2 & Hnd2 & _).
    destruct (Hwf2 (pX, cap') (or_introl eq_refl)) as ((Q0 & Q1 & Q2 & Q3 & Q4) & Qdef & Qap). cbn [fst snd lb_remove] in Q0, Q1, Q2, Q3, Q4, Qdef, Qap. rewrite Z.eqb_refl in Qap.
    assert (W0V : bv_unsigned (edenot E' (APC.eaddz NEWCAP_sso_growN 1)) = cap' + 1).
    { change (APC.eaddz NEWCAP_sso_growN 1) with (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EAlu ALU_SRL GXS (ELit 3))) (ELit 9)).
      assert (UC : bv_unsigned (edenot E' GXS) = size + n) by (unfold GXS; apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia]).
      cbn [edenot]. rewrite u_add64, u_mul64, u_srl64, UC. rewrite !u_small by lia. change (2 ^ (3 mod 64)) with 8. rewrite GC.
      rewrite (Z.mod_small (8 * ((size + n) / 8))) by lia. rewrite Z.mod_small by lia. lia. }
    assert (W0 : L5.u64_at GK.RSEGS M' o (cap' + 1)).
    { apply (CL5.kword64_elim GK.RSEGS E' M' _ _ o _ (CELL _ Y4)); [unfold estart, e_o; cbn [a_base a_off edenot]; rewrite F10; lia | exact W0V]. }
    assert (W8 : L5.u64_at GK.RSEGS M' (o + 8) (size + n)).
    { apply (CL5.kword64_elim GK.RSEGS E' M' _ _ (o + 8) _ (CELL _ Y3)); [unfold estart, e_o; cbn [a_base a_off edenot]; rewrite F10; lia | apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia]]. }
    assert (W16 : L5.u64_at GK.RSEGS M' (o + 16) pX).
    { apply (CL5.kword64_elim GK.RSEGS E' M' _ _ (o + 16) _ (CELL _ Y2)); [unfold estart, e_o; cbn [a_base a_off edenot]; rewrite F10; lia | reflexivity]. }
    assert (UEP : estart E' (SA (EAlu ALU_ADD e_n (EAlu ALU_ADD e_size (EVar v))) 0) = pX + (size + n)).
    { unfold estart, e_n, e_size. cbn [a_base a_off edenot]. rewrite !u_add64, F12, F32, UPX.
      rewrite (Z.mod_small (size + pX)) by lia. rewrite Z.mod_small by lia. lia. }
    assert (NUL : L5.u8_at GK.RSEGS M' (pX + (size + n)) 0) by exact (CL5.kword8_zero_elim GK.RSEGS E' M' _ _ (CELL _ Y1) UEP).
    assert (C8 : cap' mod 8 = 0).
    { rewrite GC. replace (8 * ((size + n) / 8) + 8) with (((size + n) / 8 + 1) * 8) by ring. apply Z_mod_mult. }
    assert (LB1 : 0 <= size + n < cap') by (clear - GC QB Hgrow SZ0 Hn1; lia).
    assert (LB2 : 0 <= pX /\ pX + cap' <= 2 ^ 63) by (clear - Q0 Q4 CEQ S4; lia).
    destruct (EAK.long_intro M' o cap' pX (size + n) W0 W8 W16 NUL Qdef LB1 C8 (proj1 LB2) (proj2 LB2)) as (s' & Hs'len & STR).
    assert (FRESH : L5C.fresh_block L LB M' pX cap').
    { split; [repeat split; assumption|]. split; [|exact Qdef].
      intros b0 Hb0x. destruct b0 as [bb bm]. exact (Qap (bb, bm) Hb0x). }
    assert (KEEP : forall y : reg, In (ridx y) CSAVED -> getr R' y = getr R y).
    { intros y Hy. assert (Hy32 : (ridx y < SGNT.NF)%nat) by (unfold CSAVED, CL5.CSAVED in Hy; cbn [In] in Hy; unfold SGNT.NF; intuition lia).
      rewrite (CL.ps_keeps_sound GK.RSEGS c0 ps E0 E' R' M1 M' CSAVED SGNT.NF y HLF Y9 HagE' Hy Hy32). exact (EV y). }
    assert (HRP : regs_preserved R R') by (intros y Hy; apply KEEP; exact (CL5.csaved_in y Hy)).
    assert (Hra' : getr R' 1%bv = Z_to_bv 64 r) by (rewrite (KEEP 1%bv ltac:(left; reflexivity)); exact Hra).
    assert (Hds : L5.defined M (sp - CH.hd_scr SGN.HDECL) (CH.hd_scr SGN.HDECL)).
    { change (CH.hd_scr SGN.HDECL) with SCRT. unfold SCRT. intros j Hj. replace (sp - 8384 + j) with (sp - (256 + (16 + 8224)) + (j + 112)) by lia. apply S5. lia. }
    pose proof (CH2.amb_hpres L HI LYI LYE SGNT.NF E0 M model LB sp SGN.HDECL [(o, 24)] SGN.BLS (CredU cap' cr) STKF NF32 i E M' m1 HA2 Hds) as HP0.
    change (CH.hd_scr SGN.HDECL) with SCRT in HP0.
    assert (HP : L5C.hpres L LB sp (256 + (16 + 8224)) [(o, 24)] M M').
    { apply (GK.hpres_scr L _ sp SCRT); [unfold SCRT; lia | exact S5 | lia | rewrite (PmLayout.ly_errno L LAY); lia | lia | lia | exact HP0]. }
    rewrite X, LS. eapply CL.ret_cps; [exact ret_at | exact (proj1 Hmo1) | exact (proj1 (proj2 Hmo1)) | |].
    { rewrite Hra'. apply Hoare.ret_ok_even. destruct Hraok as [R1' R2']. rewrite u64_of_Z by lia. exact R2'. }
    rewrite Hra'.
    assert (Hcr : cr1 = debit L cr cap') by (unfold CredU in HC1; rewrite Y6 in HC1; exact HC1).
    subst cr1.
    apply (Hcont fx' R' M' m1 ((pX, cap') :: LB) (debit L cr cap') LB [(o, 24)] HFP); [| exact HRP | exact HP | exact Hbv1 | exact HH2].
    split; [|reflexivity]. exists pX, s'. cbv zeta.
    split; [exact Hs'len|]. split; [exact STR|]. split; [exact FRESH|]. split; [reflexivity|]. split; reflexivity.
  - reflexivity.
  -
    rewrite LS.
    assert (Hds : L5.defined M (sp - 8384) 8384) by (intros i Hi; replace (sp - 8384 + i) with (sp - (256 + (16 + 8224)) + (i + 112)) by lia; apply S5; lia).
    split; [exact (regs_ok_id R _ _)|]. unfold know_ok, SGN.cp0. cbn [CC.cp_know].
    repeat (apply Forall_cons); [.. | apply Forall_nil].
    + eapply GK.kword8_intro with (A := o) (z := 2 * Z.of_nat (length s)); [ev_start | lia | lia | apply bv_eq; rewrite u64_of_Z by lia; apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia] | lia | exact Hb0].
    + eapply CL5.kword64_intro with (A := o) (z := 2 * Z.of_nat (length s) + 256 * u); [ev_start | lia | lia | apply bv_eq; rewrite u64_of_Z by lia; apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia] | exact Hw0].
    + e_range. + e_range. + e_range. + e_range. + e_range. + e_range.
    + e_unk. + e_wr. + e_range. + e_align O3.
    + e_unk. + e_wr. + e_range. + e_align S1.
    + e_disj. + e_disj. + e_disj.
  -
    split; [exact Hmo|]. split; [apply L5C.model_but_vm_refl|]. split; [apply CC.env_agree_refl|].
    split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
    exists cr. split; [|reflexivity]. unfold CH2.cur. change (nth 0 SGN.BLS []) with (@nil (expr * expr)). exact HH.
  - exact Hfp.
Qed.

End AppendSU.
End EASU.
