(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import HeapIface L5Defs L5Core
  FrmInv. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10FrmInv_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import CutVF CutVFX DecIface DecIfaceU DecJson DecOkDefs DecOkSem StrtodPure StrtodIface. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10Leaf_trunctfdf2_u PmLibDefs_u PmLibSpecs_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.FCutCert Require Import CutCert CutOps CutHeap CutAuto CutLib CutL5 CutOpsD CutAutoD. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.FCutCert Require Import Pm10CutKitD_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.FCutGen Require Import Cut_strtod_csrc_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S. Import DOK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module STO.
Definition GADDR : Z := 0xf6a70.   Definition TPV : Z := 0xd6800.   Definition ERRNO : Z := 0xd6800 - 164.
Definition SCR : Z := 8944.        Definition NFs : nat := 34.
Definition IMGc : option (Z * Z) := Some (65536, 801400).
Definition F0x : list SGP.region := [(EVar 2, -8944, ELit 8944); (EVar 11, 0, ELit 8); (ELit 0, ERRNO, ELit 4)].

Lemma guard_readable : forall M : word -> option byte, exists CAN, L5.u64_at RSEGS M GADDR CAN /\ 0 <= CAN < 2 ^ 64.
Proof.
  intros M. assert (H : exists bs, rdn RSEGS M (Z_to_bv 64 GADDR) 8 = Some bs /\ length bs = 8%nat).
  { assert (G : forall n a, (forall i, (i < n)%nat -> seg_rom RSEGS (Z_to_bv 64 (a + Z.of_nat i)) <> None) -> exists bs, rdn RSEGS M (Z_to_bv 64 a) n = Some bs /\ length bs = n).
    { induction n as [|n IH]; intros a Hr; [exists []; split; reflexivity|]. cbn [rdn].
      assert (Hb : exists b, match M (Z_to_bv 64 a) with Some b => Some b | None => seg_rom RSEGS (Z_to_bv 64 a) end = Some b).
      { destruct (M (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity|]. specialize (Hr 0%nat ltac:(lia)). replace (a + Z.of_nat 0) with a in Hr by lia.
        destruct (seg_rom RSEGS (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity | contradiction]. }
      destruct Hb as [b ->].
      replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)).
      2:{ apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_unsigned (1%bv : bv 64)) with 1. rewrite <- Zplus_mod_idemp_l. reflexivity. }
      destruct (IH (a + 1)) as (bs & -> & Hl); [intros i Hi; replace (a + 1 + Z.of_nat i) with (a + Z.of_nat (S i)) by lia; apply Hr; lia|].
      exists (b :: bs). split; [reflexivity | cbn; lia]. }
    apply G. intros i Hi. do 8 (destruct i as [|i]; [vm_compute; discriminate|]). lia. }
  destruct H as (bs & Hr & Hl). exists (bytes_le_to_Z bs). split.
  - unfold L5.u64_at. rewrite Hr. f_equal. symmetry. rewrite <- Hl at 1. apply APSX.word_to_le_bytes_of_bytes. lia.
  - pose proof (AX2S.bytes_le_to_Z_bound bs) as B. rewrite Hl in B. exact B.
Qed.
Lemma errno_writable : forall M : word -> option byte, L5.writable RSEGS M ERRNO 4.
Proof.
  intros M d k Hd Hk. apply store_ok_seg_writable.
  - rewrite L5.unsigned_lit by (unfold ERRNO; lia). unfold ERRNO. lia.
  - intros x Hx. rewrite L5.unsigned_lit in Hx by (unfold ERRNO; lia).
    assert (Hc : x = Z_to_bv 64 ERRNO \/ x = Z_to_bv 64 (ERRNO + 1) \/ x = Z_to_bv 64 (ERRNO + 2) \/ x = Z_to_bv 64 (ERRNO + 3)).
    { assert (E : forall v, bv_unsigned x = v -> x = Z_to_bv 64 v) by (intros v <-; symmetry; apply Z_to_bv_bv_unsigned).
      unfold ERRNO in *. assert (C : bv_unsigned x = 878428 \/ bv_unsigned x = 878429 \/ bv_unsigned x = 878430 \/ bv_unsigned x = 878431) by lia.
      destruct C as [C|[C|[C|C]]]; [left | right; left | right; right; left | right; right; right]; apply E; exact C. }
    destruct Hc as [-> | [-> | [-> | ->]]]; eexists; (split; [vm_compute; reflexivity|]); split; vm_compute; [reflexivity | discriminate | reflexivity | discriminate | reflexivity | discriminate | reflexivity | discriminate].
Qed.

Definition fs_kn1 (ps : SR.post_spec) : list kentry :=
  APC.kn_havoc (APC.kn_havoc (APC.kn_havoc (SR.ps_cells ps) (EVar 2) (-264) (ELit 8)) (EVar 2) (-8944) (ELit 8672)) (ELit 0) ERRNO (ELit 4).
Definition RPOS' : expr := APC.eadd (EVar 10) (EVar 33).
Definition fs_chk (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) : bool :=
  let regs := CA.ps_reglist ps in
  let nx := Nat.max (CC.cp_nx c) (CA.ps_bound ps) in
  let cells := SR.ps_cells ps in
  match nth 1 regs (ELit 1) with
  | ELit ra =>
      (CVF.all_regs_chk ps && expr_eqb (nth 2 regs (ELit 0)) (APC.eaddz (EVar 2) (-272)) && expr_eqb (nth 10 regs (ELit 0)) (APC.eaddz (EVar 2) (-272))
       && expr_eqb (nth 11 regs (ELit 0)) (ELit 1) && expr_eqb (nth 12 regs (ELit 0)) (ELit 1) && expr_eqb (nth 4 regs (ELit 0)) (ELit TPV)
       && Z.leb 0 ra && Z.ltb ra (2 ^ 47) && Z.eqb (ra mod 2) 0
       && has cells (KWord (SA (EVar 2) (-264)) 8 (EVar 10)) && has cells (KWord (SA (EVar 2) (-88)) 8 (ELit 18446744073709551615)) && has cells (KWord (SA (EVar 2) (-80)) 8 (ELit 0))
       && has cells (KWord (SA (ELit 0) GADDR) 8 (EVar 32)) && has cells (KImg 65536 801400) && has cells (KRange (CC.cp_meas c) 1 CC.MB)
       && APC.expr_vars_lt (CC.cp_nx c) (CC.cp_meas c) && APC.sr_vars_lt nx regs && APC.kn_vars_lt nx (fs_kn1 ps)
       && Z.eqb (CC.cp_pc cj) ra && CA.regs_eqb (CC.cp_regs cj) (APC.sr_fresh regs APC.caller_saved nx)
       && CVF.kn_eqb (CC.cp_know cj) (KWord (SA (EVar 2) (-264)) 8 RPOS' :: KUnk (SA (EVar 2) (-8944)) (ELit 8672) :: fs_kn1 ps)
       && Nat.eqb (CC.cp_nx cj) (nx + 16) && expr_eqb (CC.cp_meas cj) (APC.esub (CC.cp_meas c) (ELit 1)))%bool
  | _ => false
  end.
Lemma fs_chk_ok : fs_chk cp0 (nth 0 (CC.cp_PSS cp0) (SR.PS 0 [] [] [])) cp1 = true.
Proof. vmc_refl. Qed.
Lemma tr_chk_ok : CVF.call_chk 8944 cp1 (nth 0 (CC.cp_PSS cp1) (SR.PS 0 [] [] [])) cp2 16 IMGc = true.
Proof. vmc_refl. Qed.
Definition exit_chk (ps : SR.post_spec) : bool :=
  (Z.eqb (SR.ps_pc ps) 0xb6bd8 && forallb (fun r => CL.ps_reg_is ps r (EVar r)) [1; 2; 3; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat && CL.ps_reg_is ps 4 (ELit TPV)
   && has (SR.ps_cells ps) (KWord (SA (EVar 11) 0) 8 RPOS'))%bool.
Lemma exit_chk_ok : exit_chk (nth 0 (CC.cp_PSS cp2) (SR.PS 0 [] [] [])) = true.
Proof. vmc_refl. Qed.
Lemma ret_ok_pc : CL.is_ret_at RSEGS 0xb6bd8.
Proof. CL.solve_is_ret. Qed.

Definition ghost (CAN N : Z) (n : nat) : word := match n with 32 => Z_to_bv 64 CAN | 33 => Z_to_bv 64 N | _ => Z_to_bv 64 0 end%nat.
Definition mkE (R : bvmap 5 word) (CAN N : Z) : env := Env (reg_ev R (ghost CAN N)) (fun _ => []).
Definition XIt (i : nat) (E : env) (M : word -> option byte) : Prop := True.

Section Run.
Context {SCFG_P : ScfgP}.
Hypothesis FS : PSI.floatscan_contract RSEGS PDCU.ubsan11 0xb27ec.
Variable L : heap_layout.

Theorem strtod_ok : PMS.strtod_spec L PML.STRTOD_SCR_V.
Proof.
  unfold PMS.strtod_spec, PML.cps_pure, PML.STRTOD_SCR_V. intros s endp sp r txt fx R M model K Hh Hl _ Hfp Hpre HK.
  destruct Hpre as (Hent & Ha0 & Ha1 & Himg & Tb & Tn & Hnf & Hlen & Dend & Hend1 & Hend2 & Ap1 & Ap2 & Ap3 & Tdef & Hs1 & Hs2).
  destruct Hent as (Rra & Hrok & Rsp & Rtp & Hstk). destruct Hstk as (Hal & Hfl & Htop & Hwin & Hdef).
  unfold PML.a0, PML.a1, PML.img_ro, PML.IMG_RO_HI, PML.u8, PML.TP in *. change (878592 - 164) with ERRNO in *. change (878592 - 160) with (ERRNO + 4) in *.
  set (N := Z.of_nat (length txt)) in *.
  destruct (guard_readable M) as (CAN & Hguard & RCAN).
  assert (HN1 : 1 <= N) by (destruct (PSP.final_shape txt Hnf) as [(c0 & r0 & -> & _) | (c1 & r0 & -> & _)]; unfold N; cbn [length]; lia).
  set (E0 := mkE R CAN N).
  assert (Usp : bv_unsigned (getr R 2%bv) = sp) by (rewrite Rsp; apply u64_of_Z; lia).
  assert (Us : bv_unsigned (getr R 10%bv) = s) by (rewrite Ha0; apply u64_of_Z; lia).
  assert (Uend : bv_unsigned (getr R 11%bv) = endp) by (rewrite Ha1; apply u64_of_Z; lia).
  assert (U2 : bv_unsigned (ev E0 2) = sp) by exact Usp.
  assert (U10 : bv_unsigned (ev E0 10) = s) by exact Us.
  assert (U11 : bv_unsigned (ev E0 11) = endp) by exact Uend.
  assert (U33 : bv_unsigned (ev E0 33) = N) by (change (ev E0 33) with (Z_to_bv 64 N); apply u64_of_Z; lia).
  assert (OUT : forall x : word, ~ (sp - 8944 <= bv_unsigned x < sp) -> ~ (endp <= bv_unsigned x < endp + 8) -> ~ (ERRNO <= bv_unsigned x < ERRNO + 4) -> SGP.outside E0 F0x x).
  { intros x A1 A2 A3. unfold SGP.outside, F0x. unfold ERRNO in *.
    repeat apply Forall_cons; [| | | apply Forall_nil]; rewrite ?(DOS.estart_reg E0 2 _ sp U2), ?(DOS.estart_reg E0 11 _ endp U11), ?(DOS.estart_lit E0 0) by lia; rewrite DOS.elen_lit by lia; lia. }
  assert (OUT' : forall x : word, SGP.outside E0 F0x x -> ~ (sp - 8944 <= bv_unsigned x < sp) /\ ~ (endp <= bv_unsigned x < endp + 8) /\ ~ (ERRNO <= bv_unsigned x < ERRNO + 4)).
  { intros x H. unfold SGP.outside, F0x in H. unfold ERRNO in *. apply Forall_cons_iff in H as [B1 H]. apply Forall_cons_iff in H as [B2 H]. apply Forall_cons_iff in H as [B3 _].
    rewrite ?(DOS.estart_reg E0 2 _ sp U2), ?(DOS.estart_reg E0 11 _ endp U11), ?(DOS.estart_lit E0 0) in * by lia. rewrite !DOS.elen_lit in * by lia. lia. }
  set (AMB := CVX.AmbX NFs E0 M model F0x XIt).
  assert (SUBF : forall c, CC.cp_F c = F0x -> CL.sub_F NFs E0 F0x c).
  { intros c HF Ex a Hagx Ho. rewrite HF. exact (CL.outside_agree_F0 NFs E0 F0x eq_refl Ex a Hagx Ho). }
  replace (PML.cfg R PML.PC_STRTOD M model) with (mkCfg (@mkst fx R (Z_to_bv 64 (CC.cp_pc cp0)) M (seg_rom RSEGS)) model) by reflexivity.
  eapply (CC.cutcert_sound_tagged RSEGS CPS TAGS NFs AMB K FrmInv.fp_ok
            (fun fx1 fx2 R1 pc1 M1 R2 pc2 M2 H => FrmInv.msteps_fp_ok RSEGS Pm10FrmInv.text_safe fx1 fx2 R1 _ M1 _ R2 _ M2 _ H) (plans (Forall_nil _)) tags_ok)
    with (i := 0%nat) (c := cp0) (E := E0).
  - intros i E M1 m1 H. exact (CVX.ambx_model NFs E0 M model F0x XIt Hh Hl i E M1 m1 H).
  - intros i c1 tags k ps j sg Hc1 Htags Hps Htag. exfalso.
    destruct i as [|[|[|i]]]; cbv [TAGS nth_error] in Htags; [| | | destruct i; discriminate Htags];
      (injection Htags as <-; destruct k as [|k]; cbv [nth_error] in Htag; [discriminate Htag | destruct k; discriminate Htag]).
  - intros i c1 tags k ps id Hc1 Htags Hps Htag.
    destruct i as [|[|[|i]]]; cbv [CPS nth_error] in Hc1; [| | | destruct i; discriminate Hc1]; injection Hc1 as <-;
      (destruct k as [|k]; cbv [cp0 cp1 cp2 CC.cp_PSS nth_error] in Hps; [|destruct k; discriminate Hps]); injection Hps as <-.
    +
      intros fx' E R1 M1 m1 E' R' M' HAt1 [HAmb1 _] HFP Hag HLF HIH.
      assert (HA' : CL.pure_amb NFs E0 M model F0x 0%nat E' M' m1).
      { eapply CL.pure_amb_step with (c := cp0); [exact (SUBF cp0 eq_refl) | vm_compute; lia | exact HAmb1 | exact Hag | exact HLF | apply CC.env_agree_refl]. }
      destruct HA' as (-> & Hag0 & Hfr & Hgr).
      set (ps := nth 0 (CC.cp_PSS cp0) (SR.PS 0 [] [] [])) in *.
      pose proof fs_chk_ok as X. unfold fs_chk in X. fold ps in X. set (regs := CA.ps_reglist ps) in *. set (nx := Nat.max (CC.cp_nx cp0) (CA.ps_bound ps)) in *.
      assert (Era : nth 1 regs (ELit 1) = ELit 748436) by vmc_refl. rewrite Era in X.
      do 22 (apply andb_prop in X as [X ?Y]). rename X into Xall.
      apply expr_eqb_eq in Y20, Y19, Y18, Y17, Y16, Y. apply CVF.regs_eqb_eq in Y2. apply CVF.kn_eqb_eq in Y1. apply Nat.eqb_eq in Y0. apply Z.eqb_eq in Y3.
      pose proof (CVF.leaf_regs_ok RSEGS cp0 ps E' R' M1 M' Xall HLF) as HR. fold regs in HR.
      assert (HK' : know_ok RSEGS E' M' (SR.ps_cells ps)) by (apply Forall_forall; intros Z HZ; exact (CC.lf_cells _ _ _ _ _ _ _ HLF Z HZ)).
      assert (EVf : forall n, (n < 34)%nat -> ev E' n = ev E0 n) by (intros n Hn; symmetry; apply (proj1 Hag0); exact Hn).
      assert (U2' : bv_unsigned (ev E' 2) = sp) by (rewrite EVf by lia; exact U2).
      assert (Hm272 : forall e, bv_unsigned (edenot E' e) = sp -> bv_unsigned (edenot E' (APC.eaddz e (-272))) = sp - 272).
      { intros e He. unfold APC.eaddz. rewrite mkAlu_denot, u_add64. cbn [edenot]. rewrite He. change (bv_unsigned (Z_to_bv 64 (-272))) with (2 ^ 64 - 272).
        replace (sp + (2 ^ 64 - 272)) with (sp - 272 + 1 * 2 ^ 64) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
      set (F := sp - 272).
      assert (G2 : PDC.rz R' 2 = F) by (unfold PDC.rz; rewrite (DOS.reg_read 0 regs E' R' 2 _ HR ltac:(lia) Y20); apply Hm272; exact U2').
      assert (G10 : PDC.rz R' 10 = F) by (unfold PDC.rz; rewrite (DOS.reg_read 0 regs E' R' 10 _ HR ltac:(lia) Y19); apply Hm272; exact U2').
      assert (G11 : PDC.rz R' 11 = 1) by (unfold PDC.rz; rewrite (DOS.reg_read 0 regs E' R' 11 _ HR ltac:(lia) Y18); cbn [edenot]; apply u64_of_Z; lia).
      assert (G12 : PDC.rz R' 12 = 1) by (unfold PDC.rz; rewrite (DOS.reg_read 0 regs E' R' 12 _ HR ltac:(lia) Y17); cbn [edenot]; apply u64_of_Z; lia).
      assert (G4 : PDC.rz R' 4 = 878592) by (unfold PDC.rz; rewrite (DOS.reg_read 0 regs E' R' 4 _ HR ltac:(lia) Y16); cbn [edenot]; apply u64_of_Z; unfold TPV; lia).
      assert (G1 : getr R' (PDC.reg_of 1) = Z_to_bv 64 748436).
      { apply (DOS.reg_read 0 regs E' R' 1 (ELit 748436) HR ltac:(lia)). rewrite (nth_indep regs (ELit 0) (ELit 1)) by (unfold regs; rewrite CVF.reglist_len; lia). exact Era. }
      assert (ESr : forall o, estart E' (SA (EVar 2) o) = sp + o) by (intros o; apply (DOS.estart_reg E' 2 o sp U2')).
      assert (CELL : forall o z, has (SR.ps_cells ps) (KWord (SA (EVar 2) o) 8 (ELit z)) = true -> 0 <= z < 2 ^ 64 -> L5.u64_at RSEGS M' (sp + o) z).
      { intros o z Hc Hz. apply (CL5.kword64_elim RSEGS E' M' _ _ (sp + o) _ (DOS.know_in RSEGS E' M' _ _ HK' Hc) (ESr o)). cbn [edenot]. apply u64_of_Z. exact Hz. }
      assert (OUTM : forall x : word, ~ (sp - 8944 <= bv_unsigned x < sp) -> ~ (endp <= bv_unsigned x < endp + 8) -> ~ (ERRNO <= bv_unsigned x < ERRNO + 4) -> M' x = M x).
      { intros x A1 A2 A3. apply Hfr. apply OUT; assumption. }
      assert (DEFW : L5.defined M' (F - PSI.WIN) PSI.WIN).
      { intros d Hd. apply Hgr. unfold F, PSI.WIN in *. replace (sp - 272 - 8672 + d) with (sp - 8944 + d) by lia. apply Hdef. lia. }
      replace (Z_to_bv 64 (SR.ps_pc ps)) with (Z_to_bv 64 0xb27ec) by reflexivity.
      unfold ERRNO in *.
      eapply (FS fx' R' M' model K F F s CAN txt Hh Hl HFP G2); cbn [PDC.a_G PDC.a_TP PDC.a_img_lo PDC.a_img_hi PDCU.ubsan11]; unfold PDC.STK_FLOOR, PSI.WIN in *.
      * unfold F. rewrite Zminus_mod, Hal. reflexivity.
      * unfold F. lia.
      * exact DEFW.
      * exact G10.
      * exact G11.
      * exact G12.
      * exact G4.
      * rewrite G1. apply Hoare.ret_ok_even. rewrite u64_of_Z by lia. reflexivity.
      * unfold PDC.file_ok, PDC.STK_FLOOR. split; [|split; [|split; [|split; [|unfold F; lia]]]].
        -- replace (F + 8) with (sp + -264) by (unfold F; lia).
           apply (CL5.kword64_elim RSEGS E' M' _ _ (sp + -264) _ (DOS.know_in RSEGS E' M' _ _ HK' Y12) (ESr (-264))). cbn [edenot]. rewrite EVf by lia. exact U10.
        -- replace (F + 184) with (sp + -88) by (unfold F; lia). apply (CELL (-88) _ Y11). lia.
        -- replace (F + 192) with (sp + -80) by (unfold F; lia). apply (CELL (-80) _ Y10). lia.
        -- apply (L5C.writable_of_defined RSEGS M' (F + 8) 8); [|unfold F; lia | unfold F; lia].
           intros d Hd. apply Hgr. unfold F. replace (sp - 272 + 8 + d) with (sp - 8944 + (8680 + d)) by lia. apply Hdef. lia.
      * unfold PDC.apart. lia.
      * apply (CL5.kword64_elim RSEGS E' M' _ _ 1010288 _ (DOS.know_in RSEGS E' M' _ _ HK' Y9)); [rewrite DOS.estart_lit by lia; unfold GADDR; lia|].
        cbn [edenot]. rewrite EVf by lia. change (ev E0 32) with (Z_to_bv 64 CAN). apply u64_of_Z. exact RCAN.
      * unfold PDC.apart, F. lia.
      * unfold PDC.text_ok. fold N. split; [|split; [|split; [lia | split; [lia | split; [lia | split]]]]].
        -- intros j Hj. apply (u8_at_same RSEGS M M' (s + Z.of_nat j) _ ltac:(lia) ltac:(unfold N in *; lia)); [|exact (Tb j Hj)].
           intros x Hx. apply OUTM; rewrite Hx; unfold N in *; lia.
        -- apply (u8_at_same RSEGS M M' (s + N) _ ltac:(lia) ltac:(lia)); [|exact Tn]. intros x Hx. apply OUTM; rewrite Hx; lia.
        -- intros d Hd. apply Hgr. apply Tdef. exact Hd.
        -- exact (PSP.final_bytes txt Hnf).
      * unfold PDC.text_apart, PDC.apart. cbn [PDC.a_TP PDCU.ubsan11]. fold N. cbv zeta. unfold F. lia.
      * exact Hnf.
      * exact (L5.writable_grows RSEGS M M' _ _ Hgr (errno_writable M)).
      * intros a Ha. rewrite OUTM by (rewrite u64_of_Z by lia; lia). apply Himg. exact Ha.
      *
        intros fx2 R2 M2 HFP2 Hcs2 Hfr2 Hgr2 Hrp2. rewrite G1, <- Y3.
        set (E2 := APS.ext_list E' nx (map (fun r0 => getr R2 (Z_to_bv 5 (Z.of_nat r0))) APC.caller_saved)).
        pose proof (APS.ext_list_agree E' nx (map (fun r0 => getr R2 (Z_to_bv 5 (Z.of_nat r0))) APC.caller_saved) : env_agree nx E' E2) as Hag2.
        assert (Hnx : (34 <= nx)%nat) by (unfold nx; vm_compute; lia).
        assert (U2e : bv_unsigned (ev E2 2) = sp) by (rewrite <- (proj1 Hag2 2%nat) by lia; exact U2').
        apply (HIH 1%nat cp1 fx2 E2 R2 M2 model eq_refl).
        -- split.
           ++ rewrite Y2. apply CH.fresh_regs_ok; [| exact Y5 | repeat constructor; lia].
              intros r0 Hn. destruct (bv_eqb r0 0) eqn:Er0.
              { assert (r0 = 0%bv) as -> by (apply bv_eq; unfold bv_eqb in Er0; apply Z.eqb_eq in Er0; exact Er0).
                unfold sr_get. change (bv_eqb (0%bv : bv 5) 0) with true. cbn [edenot]. apply getr_zero. }
              assert (Hr0 : r0 <> 0%bv) by (intros ->; unfold bv_eqb in Er0; rewrite Z.eqb_refl in Er0; discriminate).
              pose proof (Hcs2 (ridx r0) (CVF.csaved_partition r0 Hr0 Hn)) as Hc. unfold PDC.reg_of in Hc. rewrite CC.reg_of_ridx in Hc. rewrite Hc. exact (HR r0).
           ++ rewrite Y1. apply Forall_cons; [|apply Forall_cons].
              ** apply (CL5.kword64_intro RSEGS E2 M2 _ _ (F + 8) (s + N)); [rewrite (DOS.estart_reg E2 2 _ sp U2e); unfold F; lia | unfold F; lia | unfold F; lia | | exact Hrp2].
                 unfold RPOS', APC.eadd. rewrite mkAlu_denot. cbn [edenot]. apply bv_eq. rewrite u_add64.
                 rewrite <- (proj1 Hag2 10%nat), <- (proj1 Hag2 33%nat) by lia. rewrite !EVf by lia. rewrite U10, U33. rewrite u64_of_Z by lia. apply Z.mod_small. lia.
              ** apply (CL5.kunk_intro RSEGS E2 M2 _ _ (sp - 8944) 8672); [rewrite (DOS.estart_reg E2 2 _ sp U2e); lia | apply DOS.elen_lit; lia | lia | lia | lia |].
                 intros d Hd. apply Hgr2. apply Hgr. apply Hdef. lia.
              **
                 set (inA := fun x : word => ((F + 8 <=? bv_unsigned x) && (bv_unsigned x <? F + 16))%bool).
                 set (inB := fun x : word => ((sp - 8944 <=? bv_unsigned x) && (bv_unsigned x <? sp - 272))%bool).
                 set (Ma := fun x : word => if inA x then M2 x else M' x). set (Mb := fun x : word => if (inA x || inB x)%bool then M2 x else M' x).
                 assert (Ga : mem_grows M' Ma) by (intros x Hx; unfold Ma; destruct (inA x); [apply Hgr2; exact Hx | exact Hx]).
                 assert (Gb : mem_grows Ma Mb) by (intros x Hx; unfold Ma, Mb in *; destruct (inA x); cbn [orb]; [exact Hx | destruct (inB x); [apply Hgr2; exact Hx | exact Hx]]).
                 assert (Gc : mem_grows Mb M2) by (intros x Hx; unfold Mb in Hx; destruct (inA x || inB x)%bool; [exact Hx | apply Hgr2; exact Hx]).
                 assert (K1 : know_ok RSEGS E' Ma (APC.kn_havoc (SR.ps_cells ps) (EVar 2) (-264) (ELit 8))).
                 { apply (APS.know_ok_havoc RSEGS E' M' Ma _ _ _ _ HK'); [|exact Ga]. intros x Hx. rewrite (ESr (-264)), DOS.elen_lit in Hx by lia.
                   unfold Ma, inA, F. destruct ((sp - 272 + 8 <=? bv_unsigned x) && (bv_unsigned x <? sp - 272 + 16))%bool eqn:Eb; [|reflexivity].
                   apply andb_prop in Eb as [B1 B2]. apply Z.leb_le in B1. apply Z.ltb_lt in B2. lia. }
                 assert (K2 : know_ok RSEGS E' Mb (APC.kn_havoc (APC.kn_havoc (SR.ps_cells ps) (EVar 2) (-264) (ELit 8)) (EVar 2) (-8944) (ELit 8672))).
                 { apply (APS.know_ok_havoc RSEGS E' Ma Mb _ _ _ _ K1); [|exact Gb]. intros x Hx. rewrite (ESr (-8944)), DOS.elen_lit in Hx by lia.
                   unfold Ma, Mb, inB. destruct (inA x); cbn [orb]; [reflexivity|].
                   destruct ((sp - 8944 <=? bv_unsigned x) && (bv_unsigned x <? sp - 272))%bool eqn:Eb; [|reflexivity].
                   apply andb_prop in Eb as [B1 B2]. apply Z.leb_le in B1. apply Z.ltb_lt in B2. lia. }
                 assert (K3 : know_ok RSEGS E' M2 (fs_kn1 ps)).
                 { unfold fs_kn1. apply (APS.know_ok_havoc RSEGS E' Mb M2 _ _ _ _ K2); [|exact Gc]. intros x Hx. rewrite DOS.estart_lit, DOS.elen_lit in Hx by lia.
                   unfold Mb, inA, inB, F. destruct (((sp - 272 + 8 <=? bv_unsigned x) && (bv_unsigned x <? sp - 272 + 16)) || ((sp - 8944 <=? bv_unsigned x) && (bv_unsigned x <? sp - 272)))%bool eqn:Eb; [reflexivity|].
                   apply orb_false_iff in Eb as [B1 B2]. apply Hfr2; unfold F, PSI.WIN; cbn [PDC.a_TP PDCU.ubsan11].
                   - apply andb_false_iff in B2 as [B|B]; [apply Z.leb_gt in B | apply Z.ltb_ge in B]; lia.
                   - apply andb_false_iff in B1 as [B|B]; [apply Z.leb_gt in B | apply Z.ltb_ge in B]; lia.
                   - unfold ERRNO in Hx. lia. }
                 apply Forall_forall. intros Z HZ.
                 eapply SGP.kentry_ok_agree1; [exact Hag2 | exact (SGP.kn_vars_lt_In nx _ Z Y4 HZ) | exact (proj1 (Forall_forall _ _) K3 Z HZ)].
        -- split; [|exact I]. split; [reflexivity|]. split; [eapply CC.env_agree_trans; [exact Hag0 | eapply CC.env_agree_le; [exact Hag2 | unfold NFs; lia]]|]. split.
           ++ intros a Ha. apply OUT' in Ha. destruct Ha as (O1 & O2 & O3). rewrite Hfr2; [apply OUTM; assumption | unfold F, PSI.WIN; lia | unfold F; lia | cbn [PDC.a_TP PDCU.ubsan11]; lia].
           ++ eapply mem_grows_trans; [exact Hgr | exact Hgr2].
        -- exact HFP2.
        -- unfold CC.meas. rewrite Y. unfold APC.esub. rewrite mkAlu_denot, u_sub64. cbn [edenot].
           assert (Em : edenot E2 (CC.cp_meas cp0) = edenot E (CC.cp_meas cp0)) by reflexivity.
           rewrite Em. change (bv_unsigned (edenot E (CC.cp_meas cp0))) with (2 ^ 60). rewrite u64_of_Z by lia. rewrite Z.mod_small by lia. lia.
    +
      refine (CVX.call_leaf_okX RSEGS CPS NFs E0 M model F0x K XIt Hh Hl 8944 sp _ 1%nat cp1 (nth 0 (CC.cp_PSS cp1) (SR.PS 0 [] [] [])) 2%nat cp2 16 IMGc ltac:(unfold NFs; lia) ltac:(lia) eq_refl U2 Hal ltac:(lia) Hdef eq_refl tr_chk_ok _ (SUBF cp1 eq_refl) ltac:(vm_compute; lia) _).
      * exact (CVF.vf_contract_weaken RSEGS _ 0 16 None IMGc ltac:(lia) ltac:(auto) Leaf_trunctfdf2_csrc.ok).
      * intros E E' E2 M1 M' M2 _ _ _ _ _ _ _. exact I.
    +
      intros fx' E R1 M1 m1 E' R' M' HAt1 [HAmb1 _] HFP Hag HLF _.
      assert (HA' : CL.pure_amb NFs E0 M model F0x 0%nat E' M' m1).
      { eapply CL.pure_amb_step with (c := cp2); [exact (SUBF cp2 eq_refl) | vm_compute; lia | exact HAmb1 | exact Hag | exact HLF | apply CC.env_agree_refl]. }
      destruct HA' as (-> & Hag0 & Hfr & Hgr).
      pose proof exit_chk_ok as X. unfold exit_chk in X. do 3 (apply andb_prop in X as [X ?Y]). clear X.
      set (ps := nth 0 (CC.cp_PSS cp2) (SR.PS 0 [] [] [])) in *.
      assert (Hkeep : forall n, In n [1; 2; 3; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat n)) = getr R (Z_to_bv 5 (Z.of_nat n))).
      { intros n Hn. rewrite forallb_forall in Y1. rewrite (CL.ps_reg_is_sound RSEGS cp2 ps E' R' M1 M' n _ HLF (Y1 n Hn)). cbn [edenot].
        rewrite <- (proj1 Hag0 n) by (unfold NFs; cbn in Hn; intuition lia). unfold E0, mkE. cbn [ev]. unfold reg_ev.
        assert (Hlt : Nat.ltb n 32 = true) by (apply Nat.ltb_lt; cbn in Hn; intuition lia). rewrite Hlt. reflexivity. }
      assert (Hra : getr R' 1%bv = Z_to_bv 64 r).
      { replace (1%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 1)) by (apply bv_eq; reflexivity). rewrite Hkeep by (cbn; tauto).
        replace (Z_to_bv 5 (Z.of_nat 1)) with (1%bv : bv 5) by (apply bv_eq; reflexivity). exact Rra. }
      replace (Z_to_bv 64 (SR.ps_pc ps)) with (Z_to_bv 64 0xb6bd8) by reflexivity.
      eapply CL.ret_cps; [exact ret_ok_pc | exact Hh | exact Hl | rewrite Hra; apply Hoare.ret_ok_even; rewrite u64_of_Z by (destruct Hrok; lia); exact (proj2 Hrok) |].
      rewrite Hra. apply HK; [exact HFP | | | | exact Hgr].
      *
        pose proof (CC.lf_cells _ _ _ _ _ _ _ HLF _ (has_In _ _ Y)) as Z.
        assert (U11' : bv_unsigned (ev E' 11) = endp) by (rewrite <- (proj1 Hag0 11%nat) by (unfold NFs; lia); exact U11).
        apply (CL5.kword64_elim RSEGS E' M' _ _ endp _ Z); [rewrite (DOS.estart_reg E' 11 0 endp U11'); lia|].
        unfold RPOS', APC.eadd. rewrite mkAlu_denot, u_add64. cbn [edenot]. rewrite <- (proj1 Hag0 10%nat), <- (proj1 Hag0 33%nat) by (unfold NFs; lia). rewrite U10, U33.
        apply Z.mod_small. lia.
      * intros x Hx. unfold callee_saved_idx in Hx. cbn [In] in Hx.
        assert (Ex : x = Z_to_bv 5 (bv_unsigned x)) by (symmetry; apply Z_to_bv_bv_unsigned).
        assert (Htp : getr R' (Z_to_bv 5 4) = getr R (Z_to_bv 5 4)).
        { change (Z_to_bv 5 4) with (Z_to_bv 5 (Z.of_nat 4)). rewrite (CL.ps_reg_is_sound RSEGS cp2 ps E' R' M1 M' 4 _ HLF Y0). cbn [edenot].
          replace (Z_to_bv 5 (Z.of_nat 4)) with (4%bv : bv 5) by (apply bv_eq; reflexivity). symmetry. exact Rtp. }
        repeat (destruct Hx as [Hx|Hx]; [rewrite Ex, <- Hx;
          first [exact Htp | exact (Hkeep 2%nat ltac:(cbn; tauto)) | exact (Hkeep 3%nat ltac:(cbn; tauto)) | exact (Hkeep 8%nat ltac:(cbn; tauto)) | exact (Hkeep 9%nat ltac:(cbn; tauto))
                | exact (Hkeep 18%nat ltac:(cbn; tauto)) | exact (Hkeep 19%nat ltac:(cbn; tauto)) | exact (Hkeep 20%nat ltac:(cbn; tauto)) | exact (Hkeep 21%nat ltac:(cbn; tauto))
                | exact (Hkeep 22%nat ltac:(cbn; tauto)) | exact (Hkeep 23%nat ltac:(cbn; tauto)) | exact (Hkeep 24%nat ltac:(cbn; tauto)) | exact (Hkeep 25%nat ltac:(cbn; tauto))
                | exact (Hkeep 26%nat ltac:(cbn; tauto)) | exact (Hkeep 27%nat ltac:(cbn; tauto))]|]). contradiction.
      * intros x Hx. apply Hfr. unfold L5.outside in Hx.
        apply OUT; intros A; [apply (Hx (sp - 8944, 8944)); [left; reflexivity | unfold L5.in_rng; cbn; lia]
                             | apply (Hx (endp, 8)); [right; left; reflexivity | unfold L5.in_rng; cbn; lia]
                             | apply (Hx (ERRNO, 4)); [right; right; left; reflexivity | unfold L5.in_rng; cbn; unfold ERRNO in *; lia]].
  - reflexivity.
  -
    split.
    + apply DOK.regs_ok_tmpl. intros n Hn. assert (W4 : getr R (Z_to_bv 5 (Z.of_nat 4)) = Z_to_bv 64 TPV) by (replace (Z_to_bv 5 (Z.of_nat 4)) with (4%bv : bv 5) by (apply bv_eq; reflexivity); exact Rtp).
      do 32 (destruct n as [|n]; [first [lia | reflexivity | (symmetry; exact W4)]|]); lia.
    + (let k := eval vm_compute in (CC.cp_know cp0) in change (CC.cp_know cp0) with k).
      assert (ES2 : forall o, estart E0 (SA (EVar 2) o) = sp + o) by (intros o; apply (DOS.estart_reg E0 2 o sp U2)).
      assert (ES11 : forall o, estart E0 (SA (EVar 11) o) = endp + o) by (intros o; apply (DOS.estart_reg E0 11 o endp U11)).
      assert (EL : forall z, 0 <= z < 2 ^ 64 -> elenZ E0 (ELit z) = z) by (intros z Hz; apply DOS.elen_lit; exact Hz).
      unfold know_ok.
      apply Forall_cons; [cbn [kentry_ok edenot]; rewrite U2; lia|].
      apply Forall_cons; [cbn [kentry_ok edenot]; rewrite U2; split; [lia | exact Hal]|].
      apply Forall_cons; [cbn [kentry_ok]; split; [lia | split; [lia | exact Himg]]|].
      apply Forall_cons; [apply (DOK.kwr_of_writable RSEGS E0 M _ _ (sp - 8944) 8944); [rewrite ES2; lia | apply EL; lia | lia | lia | lia | lia | apply (L5C.writable_of_defined RSEGS M _ _ Hdef); lia]|].
      apply Forall_cons; [apply (CL5.kunk_intro RSEGS E0 M _ _ (sp - 8944) 8944); [rewrite ES2; lia | apply EL; lia | lia | lia | lia | exact Hdef]|].
      apply Forall_cons; [apply (CL5.kword64_intro RSEGS E0 M _ _ GADDR CAN); [rewrite DOS.estart_lit by lia; unfold GADDR; lia | unfold GADDR; lia | unfold GADDR; lia | reflexivity | exact Hguard]|].
      apply Forall_cons; [cbn [kentry_ok edenot]; rewrite U10; lia|].
      apply Forall_cons; [cbn [kentry_ok edenot]; rewrite U33; lia|].
      apply Forall_cons; [cbn [kentry_ok edenot]; rewrite U11; lia|].
      apply Forall_cons; [apply (DOK.kwr_of_writable RSEGS E0 M _ _ endp 8); [rewrite ES11; lia | apply EL; lia | lia | lia | lia | lia | apply (L5C.writable_of_defined RSEGS M _ _ Dend); lia]|].
      apply Forall_cons; [apply (CL5.kunk_intro RSEGS E0 M _ _ endp 8); [rewrite ES11; lia | apply EL; lia | lia | lia | lia | exact Dend]|].
      apply Forall_cons; [cbn [kentry_ok]; rewrite ES11, ES2, !EL by lia; lia | constructor].
  - split; [|exact I]. split; [reflexivity|]. split; [apply CC.env_agree_refl|]. split; [reflexivity | apply mem_grows_refl].
  - exact Hfp.
Qed.
End Run.
End STO.
