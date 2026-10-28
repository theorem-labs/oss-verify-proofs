(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import L5Defs L5Core
  FrmInv. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10FrmInv_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import FpBridge. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10FpSites_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import CutVF CutVFX DecIface DecIfaceU DecJson DecOkDefs DecOkSem StrtodPure StrtodIface. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10Leaf_extendsftf2_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.FCutCert Require Import CutCert CutOps CutHeap CutHeap2 CutAuto CutLib CutL5 CutOpsD CutAutoD. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.FCutCert Require Import Pm10CutKitD_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.FCutGen Require Import Cut_fsinf_csrc_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S. Import DOK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module FSIC.
Module G := Cut_fsinf_csrc_u.
Definition ENTRY : Z := 0xb27ec.   Definition RET_PC : Z := 0xb3314.   Definition XS_PC : Z := 0xb47fc.
Definition GADDR : Z := 0xf6a70.   Definition TPV : Z := 0xd6800.
Definition NFs : nat := 34.
Definition INL : list Z := [0xb326c; 0xb3274; 0xb3278; 0xb3024].
Definition F0 : list SGP.region := [(EVar 2, -8672, ELit 8672); (EVar 10, 8, ELit 8)].

Definition TXT_INF : list Z := [105; 110; 102].   Definition TXT_NAN : list Z := [110; 97; 110].
Definition infnan (txt : list Z) : Prop := In txt [TXT_INF; 45 :: TXT_INF; TXT_NAN; 45 :: TXT_NAN].
Definition idx_of (txt : list Z) : nat := match txt with 45 :: 105 :: _ => 1 | 110 :: _ => 2 | 45 :: _ => 3 | _ => 0 end.

Section Contracts.
Variable segs : list Segment.
Context {SCFG_P : ScfgP}.
Variable A : PDC.addrs.
Definition floatscan_cls_contract (cls : list Z -> Prop) (pc : Z) : Prop :=
  forall (fx : FPState) R M model K sp F s CAN txt,
  m_halted model = None -> m_vm_lazy model = [] -> FrmInv.fp_ok fx ->
  PDC.rz R 2 = sp -> sp mod 16 = 0 -> PDC.STK_FLOOR + PSI.WIN <= sp <= 2 ^ 47 -> L5.defined M (sp - PSI.WIN) PSI.WIN ->
  PDC.rz R 10 = F -> PDC.rz R 11 = 1 -> PDC.rz R 12 = 1 -> PDC.rz R 4 = PDC.a_TP A -> Hoare.ret_ok (getr R (PDC.reg_of 1)) ->
  PDC.file_ok segs M F s -> PDC.apart (F + 8) 192 (sp - PSI.WIN) PSI.WIN ->
  L5.u64_at segs M (PDC.a_G A) CAN -> PDC.apart (PDC.a_G A) 8 (sp - PSI.WIN) PSI.WIN ->
  PDC.text_ok segs M s txt -> PDC.text_apart A s txt F (sp - PSI.WIN) PSI.WIN -> cls txt ->
  L5.writable segs M (PDC.a_TP A - 164) 4 -> L5.img_clear M (PDC.a_img_lo A) (PDC.a_img_hi A) ->
  (forall (fx' : FPState) R' M', FrmInv.fp_ok fx' ->
      (forall x : nat, In x PSI.CSAVED -> getr R' (PDC.reg_of x) = getr R (PDC.reg_of x)) ->
      (forall a : word, ~ (sp - PSI.WIN <= bv_unsigned a < sp) -> ~ (F + 8 <= bv_unsigned a < F + 16) -> ~ (PDC.a_TP A - 164 <= bv_unsigned a < PDC.a_TP A - 160) -> M' a = M a) ->
      mem_grows M M' ->
      L5.u64_at segs M' (F + 8) (s + Z.of_nat (length txt)) ->
      srealizes segs SCFG (mkCfg (@mkst fx' R' (getr R (PDC.reg_of 1)) M' (seg_rom segs)) model) K) ->
  srealizes segs SCFG (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom segs)) model) K.
Definition floatscan_nf_contract (pc : Z) : Prop := floatscan_cls_contract infnan pc.
End Contracts.

Definition CSL : list nat := [1; 2; 3; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Lemma csl_lt : forall n, In n CSL -> (n < 32)%nat.
Proof. intros n H. unfold CSL in H. cbn [In] in H. intuition lia. Qed.
Lemma csaved_cases : forall x, In x PSI.CSAVED -> x = 4%nat \/ In x CSL.
Proof. intros x H. unfold PSI.CSAVED in H. unfold CSL. cbn [In] in H |- *. intuition. Qed.
Lemma csl_1 : In 1%nat CSL. Proof. unfold CSL; cbn; tauto. Qed.

Lemma lems : G.LEMS_OK. Proof. unfold G.LEMS_OK, CXD.LEMS_OK, G.LEMS. apply Forall_nil. Qed.
Lemma ret_pc_ok : CL.is_ret_at RSEGS RET_PC. Proof. CL.solve_is_ret. Qed.
Lemma foot_ok : forall i c, nth_error G.CPS i = Some c -> CC.cp_F c = F0.
Proof.
  assert (X : CC.cps_all G.CPS (fun _ c => regions_eqb (CC.cp_F c) F0) = true) by (vm_cast_no_check (@eq_refl bool true)).
  intros i c H. apply regions_eqb_eq. exact (CC.cps_all_sound _ _ X i c H).
Qed.

Definition lchk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      if Z.eqb pc RET_PC then true else
      existsb (fun e : nat * nat * nat * Z => let '(j, i', k', pc') := e in
                 (Nat.eqb i' i && Nat.eqb k' k && Z.eqb pc' pc && Bool.eqb (Nat.odd i) (Nat.odd j) && Z.eqb (SR.ps_pc ps) pc &&
                  match nth_error G.CPS j with
                  | Some cj => if existsb (Z.eqb pc) INL then CVF.inl_chk c ps cj 4 [] None
                               else (Z.eqb pc XS_PC && CVF.call_chk 8672 c ps cj 16 None)
                  | None => false
                  end)%bool) G.RETS
  end.
Lemma leaves_ok : CH2.leaves_all G.CPS G.TAGS lchk = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Definition xchk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TOther pc =>
      if Z.eqb pc RET_PC then
        (Z.eqb (SR.ps_pc ps) RET_PC && forallb (fun r => CL.ps_reg_is ps r (EVar r)) CSL
         && CL.ps_reg_is ps 4 (ELit TPV)
         && has (SR.ps_cells ps) (KWord (SA (EVar 10) 8) 8 (EAlu ALU_ADD (EVar 32) (ELit (if Nat.odd i then 4 else 3)))))%bool
      else true
  | _ => true
  end.
Lemma exits_ok : CH2.leaves_all G.CPS G.TAGS xchk = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma inl_sites : forall q, existsb (Z.eqb q) INL = true -> FPB.inl_step RSEGS q 4 [].
Proof.
  intros q Hq. unfold INL in Hq. cbn [existsb] in Hq.
  destruct (Z.eqb q 0xb326c) eqn:E1; [apply Z.eqb_eq in E1; subst q; exact Pm10FpSites.site_b13dc|].
  destruct (Z.eqb q 0xb3274) eqn:E2; [apply Z.eqb_eq in E2; subst q; exact Pm10FpSites.site_b13e4|].
  destruct (Z.eqb q 0xb3278) eqn:E3; [apply Z.eqb_eq in E3; subst q; exact Pm10FpSites.site_b13e8|].
  destruct (Z.eqb q 0xb3024) eqn:E4; [apply Z.eqb_eq in E4; subst q; exact Pm10FpSites.site_b1194|].
  discriminate Hq.
Qed.

Definition ghost (s CAN : Z) (n : nat) : word := match n with 32 => Z_to_bv 64 s | 33 => Z_to_bv 64 CAN | _ => Z_to_bv 64 0 end%nat.
Definition mkE (R : bvmap 5 word) (s CAN : Z) : env := Env (reg_ev R (ghost s CAN)) (fun _ => []).

Section Final.
Context {SCFG_P : ScfgP}.
Lemma exts_ok : CVF.vf_contract RSEGS XS_PC 16 None.
Proof. exact (CVF.vf_contract_weaken RSEGS 739324 0 16 None None ltac:(lia) ltac:(auto) Leaf_extendsftf2_csrc.ok). Qed.

Theorem floatscan_nf_ok : floatscan_nf_contract RSEGS PDCU.ubsan11 ENTRY.
Proof.
  intros fx R M model K sp F s CAN txt Hh Hl Hfp Rsp Hal Hrng Hdef RF R11 R12 R4 Hret Hfile Hfs Hguard Hgap Htext Htap Hin Herrw Himg HK.
  cbn [PDC.a_G PDC.a_TP PDC.a_img_lo PDC.a_img_hi PDCU.ubsan11] in *.
  destruct Hfile as (Hf8 & Hf184 & Hf192 & Hfw & HF1 & HF2). destruct Htext as (Tb & Tn & TQ1 & TQ2 & TQ3 & Td & Tr). destruct Htap as (Ta1 & Ta2 & Ta3).
  set (N := Z.of_nat (length txt)) in *.
  assert (HNv : N = 3 \/ N = 4) by (unfold N; destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn; lia).
  unfold PDC.STK_FLOOR, PSI.WIN, PDC.apart in *. cbn [PDC.a_TP PDCU.ubsan11] in Ta3.
  set (E0 := mkE R s CAN).
  assert (EVr : forall r, (r < 32)%nat -> ev E0 r = getr R (Z_to_bv 5 (Z.of_nat r))).
  { intros r Hr. unfold E0, mkE. cbn [ev]. unfold reg_ev. apply Nat.ltb_lt in Hr. rewrite Hr. reflexivity. }
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite EVr by lia; exact Rsp).
  assert (U10 : bv_unsigned (ev E0 10) = F) by (rewrite EVr by lia; exact RF).
  assert (U32 : bv_unsigned (ev E0 32) = s) by (change (ev E0 32) with (Z_to_bv 64 s); apply u64_of_Z; lia).

  set (XI := fun (i : nat) (_ : env) (_ : word -> option byte) => Nat.odd i = Nat.eqb (length txt) 4).
  set (AMB := CVX.AmbX NFs E0 M model F0 XI).
  assert (SUBF : forall c, CC.cp_F c = F0 -> CL.sub_F NFs E0 F0 c).
  { intros c HF Ex a Hagx Ho. rewrite HF. exact (CL.outside_agree_F0 NFs E0 F0 eq_refl Ex a Hagx Ho). }
  assert (OUT : forall x : word, SGP.outside E0 F0 x -> ~ (sp - 8672 <= bv_unsigned x < sp) /\ ~ (F + 8 <= bv_unsigned x < F + 16)).
  { intros x H. unfold SGP.outside, F0 in H. apply Forall_cons_iff in H as [B1 H]. apply Forall_cons_iff in H as [B2 _].
    rewrite (DOS.estart_reg E0 2 _ sp U2), (DOS.estart_reg E0 10 _ F U10) in * by lia. rewrite !DOS.elen_lit in * by lia. lia. }
  assert (OUT' : forall x : word, ~ (sp - 8672 <= bv_unsigned x < sp) -> ~ (F + 8 <= bv_unsigned x < F + 16) -> SGP.outside E0 F0 x).
  { intros x H1 H2. unfold SGP.outside, F0. repeat apply Forall_cons; [| | apply Forall_nil];
      rewrite ?(DOS.estart_reg E0 2 _ sp U2), ?(DOS.estart_reg E0 10 _ F U10); rewrite DOS.elen_lit by lia; lia. }
  set (c0 := nth (idx_of txt) G.CPS G.cp0).
  assert (Hc0 : nth_error G.CPS (idx_of txt) = Some c0) by (unfold c0; destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; reflexivity).
  assert (Hpc0 : CC.cp_pc c0 = ENTRY) by (unfold c0; destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; reflexivity).
  rewrite <- Hpc0.
  eapply (CC.cutcert_sound_tagged RSEGS G.CPS G.TAGS NFs AMB K FrmInv.fp_ok
            (fun fx1 fx2 R1 pc1 M1 R2 pc2 M2 H => FrmInv.msteps_fp_ok RSEGS Pm10FrmInv.text_safe fx1 fx2 R1 _ M1 _ R2 _ M2 _ H) (G.plans lems) G.tags_ok)
    with (i := idx_of txt) (c := c0) (E := E0).
  - intros i E M1 m1 H. exact (CVX.ambx_model NFs E0 M model F0 XI Hh Hl i E M1 m1 H).
  -
    intros i c1 tags k ps j sg Hc1 Htags Hps Htag. exfalso.
    pose proof (CH2.leaves_all_sound _ _ _ leaves_ok i c1 k ps (CC.TGoto j sg) (ex_intro _ tags (conj Hc1 (conj Htags (conj Hps Htag))))) as X. discriminate X.
  - intros i c1 tags k ps id Hc1 Htags Hps Htag.
    assert (IL : CH2.is_leaf G.CPS G.TAGS i c1 k ps (CC.TOther id)) by (exists tags; split; [exact Hc1|]; split; [exact Htags|]; split; [exact Hps | exact Htag]).
    pose proof (CH2.leaves_all_sound _ _ _ leaves_ok _ _ _ _ _ IL) as X. unfold lchk in X.
    pose proof (CH2.leaves_all_sound _ _ _ exits_ok _ _ _ _ _ IL) as XX. unfold xchk in XX.
    pose proof (foot_ok i c1 Hc1) as HFc. pose proof (G.NF_le i c1 Hc1) as Hnx.
    destruct (Z.eqb_spec id RET_PC) as [->|Hne].
    +
      clear X. do 3 (apply andb_prop in XX as [XX ?Y]). apply Z.eqb_eq in XX.
      intros fx' E R1 M1 m1 E' R' M' HAt1 [HAmb1 HX1] HFP Hag HLF _.
      assert (HA' : CL.pure_amb NFs E0 M model F0 0%nat E' M' m1).
      { eapply CL.pure_amb_step with (c := c1); [exact (SUBF c1 HFc) | exact Hnx | exact HAmb1 | exact Hag | exact HLF | apply CC.env_agree_refl]. }
      destruct HA' as (-> & Hag0 & Hfr & Hgr).
      assert (Hkeep : forall n, In n CSL -> getr R' (Z_to_bv 5 (Z.of_nat n)) = getr R (Z_to_bv 5 (Z.of_nat n))).
      { intros n Hn. pose proof (csl_lt n Hn) as Hn32. rewrite forallb_forall in Y1. rewrite (CL.ps_reg_is_sound RSEGS c1 ps E' R' M1 M' n _ HLF (Y1 n Hn)). cbn [edenot].
        rewrite <- (proj1 Hag0 n) by (unfold NFs; lia). apply EVr. exact Hn32. }
      assert (Hra : getr R' 1%bv = getr R 1%bv).
      { replace (1%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 1)) by (apply bv_eq; reflexivity). apply Hkeep. exact csl_1. }
      rewrite XX.
      eapply CL.ret_cps; [exact ret_pc_ok | exact Hh | exact Hl | rewrite Hra; exact Hret |].
      rewrite Hra. apply HK; [exact HFP | | | exact Hgr |].
      * intros x Hx. unfold PDC.reg_of.
        assert (Htp : getr R' (Z_to_bv 5 (Z.of_nat 4)) = getr R (Z_to_bv 5 (Z.of_nat 4))).
        { rewrite (CL.ps_reg_is_sound RSEGS c1 ps E' R' M1 M' 4 _ HLF Y0). cbn [edenot]. symmetry. exact (DOK.rz_word R 4 _ R4). }
        destruct (csaved_cases x Hx) as [->|Hx']; [exact Htp | exact (Hkeep x Hx')].
      * intros a A1 A2 A3. apply Hfr. apply OUT'; assumption.
      *
        pose proof (CC.lf_cells _ _ _ _ _ _ _ HLF _ (has_In _ _ Y)) as Z.
        assert (U10' : bv_unsigned (ev E' 10) = F) by (rewrite <- (proj1 Hag0 10%nat) by (unfold NFs; lia); exact U10).
        assert (U32' : bv_unsigned (ev E' 32) = s) by (rewrite <- (proj1 Hag0 32%nat) by (unfold NFs; lia); exact U32).
        assert (HN : (if Nat.odd i then 4 else 3) = N).
        { unfold XI in HX1. destruct (Nat.odd i); symmetry in HX1; [apply Nat.eqb_eq in HX1 | apply Nat.eqb_neq in HX1]; unfold N in *; destruct HNv as [E3|E4]; lia. }
        apply (CL5.kword64_elim RSEGS E' M' _ _ (F + 8) _ Z); [rewrite (DOS.estart_reg E' 10 8 F U10'); lia|].
        rewrite HN. cbn [edenot]. rewrite u_add64. rewrite U32'. rewrite !u64_of_Z by lia. apply Z.mod_small. lia.
    +
      clear XX. apply Z.eqb_neq in Hne. cbv beta iota in X. try rewrite Hne in X.
      apply existsb_exists in X as ([[[j i'] k'] pc'] & _ & X). do 5 (apply andb_prop in X as [X ?Y]).
      apply Nat.eqb_eq in X. apply Nat.eqb_eq in Y3. apply Z.eqb_eq in Y2. apply Bool.eqb_prop in Y1. apply Z.eqb_eq in Y0. subst i' k' pc'.
      destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate Y].
      destruct (existsb (Z.eqb id) INL) eqn:HI'.
      * assert (XL : CVX.xi_leaf NFs E0 XI i j c1) by (intros Ea Eb Ec Ma Mb HXa _ _ _ _; unfold XI in *; rewrite <- Y1; exact HXa).
        pose proof (inl_sites id HI') as Hst. rewrite <- Y0 in Hst.
        exact (CVX.inl_leaf_okX RSEGS G.CPS NFs E0 M model F0 K XI Hh Hl Pm10FrmInv.text_safe i c1 ps j cj 4 [] Hcj Y (SUBF c1 HFc) Hnx XL Hst).
      * apply andb_prop in Y as [Yx Y]. apply Z.eqb_eq in Yx.
        assert (XC : CVX.xi_call NFs E0 XI i j c1 (sp - 8672) sp) by (intros Ea Eb Ec Ma Mb Mc HXa _ _ _ _ _ _; unfold XI in *; rewrite <- Y1; exact HXa).
        refine (CVX.call_leaf_okX RSEGS G.CPS NFs E0 M model F0 K XI Hh Hl 8672 sp [(EVar 10, 8, ELit 8)] i c1 ps j cj 16 None ltac:(unfold NFs; lia) ltac:(lia) eq_refl
                  U2 Hal ltac:(lia) Hdef Hcj Y _ (SUBF c1 HFc) Hnx XC).
        rewrite Y0, Yx. exact exts_ok.
  - exact Hc0.
  -
    split.
    + assert (Rg : CC.cp_regs c0 = [EVar 0; EVar 1; EVar 2; EVar 3; ELit 878592; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; ELit 1; ELit 1; EVar 13; EVar 14; EVar 15;
                                    EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31])
        by (unfold c0; destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; reflexivity).
      rewrite Rg. apply DOK.regs_ok_tmpl. intros n Hn.
      pose proof (DOK.rz_word R 4 _ R4) as W4. pose proof (DOK.rz_word R 11 _ R11) as W11. pose proof (DOK.rz_word R 12 _ R12) as W12.
      do 32 (destruct n as [|n]; [first [lia | reflexivity | (symmetry; first [exact W4 | exact W11 | exact W12])]|]); lia.
    + assert (ES2 : forall o, estart E0 (SA (EVar 2) o) = sp + o) by (intros o; apply (DOS.estart_reg E0 2 o sp U2)).
      assert (ES10 : forall o, estart E0 (SA (EVar 10) o) = F + o) by (intros o; apply (DOS.estart_reg E0 10 o F U10)).
      assert (ES32 : forall o, estart E0 (SA (EVar 32) o) = s + o) by (intros o; apply (DOS.estart_reg E0 32 o s U32)).
      assert (EL : forall z, 0 <= z < 2 ^ 64 -> elenZ E0 (ELit z) = z) by (intros z Hz; apply DOS.elen_lit; exact Hz).
      assert (BYTE : forall i b, 0 <= i <= N -> nth (Z.to_nat i) (txt ++ [0]) 0 = b -> kentry_ok RSEGS E0 M (KWord (SA (EVar 32) i) 1 (ELit b))).
      { intros i b Hi Hb.
        assert (Hm : L5.u8_at RSEGS M (s + i) b /\ 0 <= b < 256).
        { subst b. destruct (Z.eq_dec i N) as [->|Hne].
          - rewrite app_nth2 by (unfold N; lia). replace (Z.to_nat N - length txt)%nat with 0%nat by (unfold N; lia). cbn [nth]. split; [exact Tn | lia].
          - assert (Hi' : (Z.to_nat i < length txt)%nat) by (unfold N in *; lia).
            rewrite app_nth1 by exact Hi'. split.
            + pose proof (Tb (Z.to_nat i) Hi') as B. rewrite Z2Nat.id in B by lia. exact B.
            + rewrite Forall_forall in Tr. apply Tr. apply nth_In. exact Hi'. }
        destruct Hm as [Hm Hbr].
        apply (DOK.kword8_intro RSEGS E0 M _ _ (s + i) b); [rewrite ES32; reflexivity | lia | lia | cbn [edenot]; apply u64_of_Z; lia | lia | exact Hm]. }
      assert (COMMON : forall n1 tail, n1 = N + 1 -> know_ok RSEGS E0 M tail ->
                know_ok RSEGS E0 M
                  ([KRange (EVar 2) 140735332491744 140737488355328; KAlign (EVar 2) 16; KImg 65536 801400; KWr (SA (EVar 2) (-8672)) (ELit 8672); KUnk (SA (EVar 2) (-8672)) (ELit 8672);
                    KWr (SA (EVar 10) 8) (ELit 8); KRange (EVar 10) 140735332483072 140737488355072; KDisj (SA (EVar 10) 8) (ELit 192) (SA (EVar 2) (-8672)) (ELit 8672);
                    KRange (EVar 32) 4096 140737488355328; KWord (SA (EVar 10) 8) 8 (EVar 32); KWord (SA (EVar 10) 184) 8 (ELit 18446744073709551615);
                    KWord (SA (EVar 10) 192) 8 (ELit 0); KWord (SA (ELit 0) 1010288) 8 (EVar 33);
                    KDisj (SA (EVar 32) 0) (ELit n1) (SA (EVar 2) (-8672)) (ELit 8672); KDisj (SA (EVar 32) 0) (ELit n1) (SA (EVar 10) 8) (ELit 192)] ++ tail)).
      { intros n1 tail Hn1 Htail. subst n1. unfold know_ok. cbn [app].
        apply Forall_cons; [cbn [kentry_ok edenot]; rewrite U2; lia|].
        apply Forall_cons; [cbn [kentry_ok edenot]; rewrite U2; split; [lia | exact Hal]|].
        apply Forall_cons; [cbn [kentry_ok]; split; [lia | split; [lia | exact Himg]]|].
        apply Forall_cons; [apply (DOK.kwr_of_writable RSEGS E0 M _ _ (sp - 8672) 8672); [rewrite ES2; lia | apply EL; lia | lia | lia | lia | lia | apply (L5C.writable_of_defined RSEGS M _ _ Hdef); lia]|].
        apply Forall_cons; [apply (CL5.kunk_intro RSEGS E0 M _ _ (sp - 8672) 8672); [rewrite ES2; lia | apply EL; lia | lia | lia | lia | exact Hdef]|].
        apply Forall_cons; [apply (DOK.kwr_of_writable RSEGS E0 M _ _ (F + 8) 8); [rewrite ES10; lia | apply EL; lia | lia | lia | lia | lia | exact Hfw]|].
        apply Forall_cons; [cbn [kentry_ok edenot]; rewrite U10; lia|].
        apply Forall_cons; [cbn [kentry_ok]; rewrite ES10, ES2, !EL by lia; lia|].
        apply Forall_cons; [cbn [kentry_ok edenot]; rewrite U32; lia|].
        apply Forall_cons; [apply (CL5.kword64_intro RSEGS E0 M _ _ (F + 8) s); [rewrite ES10; lia | lia | lia | reflexivity | exact Hf8]|].
        apply Forall_cons; [apply (CL5.kword64_intro RSEGS E0 M _ _ (F + 184) (2 ^ 64 - 1)); [rewrite ES10; lia | lia | lia | reflexivity | exact Hf184]|].
        apply Forall_cons; [apply (CL5.kword64_intro RSEGS E0 M _ _ (F + 192) 0); [rewrite ES10; lia | lia | lia | reflexivity | exact Hf192]|].
        apply Forall_cons; [apply (CL5.kword64_intro RSEGS E0 M _ _ 1010288 CAN); [rewrite DOS.estart_lit by lia; lia | lia | lia | reflexivity | exact Hguard]|].
        apply Forall_cons; [cbn [kentry_ok]; rewrite ES32, ES2, !EL by lia; lia|].
        apply Forall_cons; [cbn [kentry_ok]; rewrite ES32, ES10, !EL by lia; lia|].
        exact Htail. }
      unfold c0. destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [idx_of nth];
        (match goal with |- know_ok _ _ _ (CC.cp_know ?c) => let k := eval vm_compute in (CC.cp_know c) in change (CC.cp_know c) with k end);
        (match goal with |- know_ok _ _ _ (?a1 :: ?a2 :: ?a3 :: ?a4 :: ?a5 :: ?a6 :: ?a7 :: ?a8 :: ?a9 :: ?a10 :: ?a11 :: ?a12 :: ?a13 :: ?a14 :: ?a15 :: ?t) =>
           change (know_ok RSEGS E0 M ([a1; a2; a3; a4; a5; a6; a7; a8; a9; a10; a11; a12; a13; a14; a15] ++ t)) end);
        (eapply COMMON; [unfold N; reflexivity|]); unfold know_ok;
        repeat (apply Forall_cons; [apply BYTE; [unfold N; cbn; lia | reflexivity] |]); apply Forall_nil.
  - split; [split; [reflexivity|]; split; [apply CC.env_agree_refl|]; split; [intros; reflexivity | apply mem_grows_refl]|].
    unfold XI. destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; reflexivity.
  - exact Hfp.
Qed.
End Final.
End FSIC.
