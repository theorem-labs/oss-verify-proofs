(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import L5Defs L5Core
  FrmInv. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10FrmInv_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import CutVF CutVFX DecIface DecIfaceU DecOkDefs DecOkSem ScanexpSem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import ScanexpLems_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.FCutCert Require Import CutCert CutOps CutHeap CutHeap2 CutAuto CutLib CutL5 CutOpsD CutAutoD. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.FCutCert Require Import Pm10CutKitD_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.FCutGen Require Import Cut_scanexp_csrc_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S. Import DOK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module SXO.
Definition RET_PC : Z := 0xb47f8.
Definition lchk := SXS.leaf_chk CPS RET_PC.
Lemma cuts_ok : CC.cps_all CPS (fun _ c => SXS.cut_chk c) = true.
Proof. vmc_refl. Qed.
Lemma leaves_ok : CH2.leaves_all CPS TAGS lchk = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ret_pc_ok : CL.is_ret_at RSEGS RET_PC.
Proof. CL.solve_is_ret. Qed.

Definition ghost (Q N : Z) (n : nat) : word := match n with 32 => Z_to_bv 64 Q | 33 => Z_to_bv 64 N | _ => Z_to_bv 64 0 end%nat.
Definition mkE (R : bvmap 5 word) (Q N : Z) : env := Env (reg_ev R (ghost Q N)) (fun _ => []).
Definition entry_ix (N : Z) : nat := if N =? 0 then 0%nat else if N =? 1 then 1%nat else 2%nat.
Definition entry_cp (N : Z) : CC.cutpoint := if N =? 0 then cp0 else if N =? 1 then cp1 else cp2.

Section Run.
Context {SCFG_P : ScfgP}.

Theorem scanexp_ok : PDC.scanexp_contract RSEGS PDCU.ubsan11.
Proof.
  unfold PDC.scanexp_contract. intros fx R M model K sp F P' txt Hh Hl Hfp Rsp Hal Hsp Hdef Hwr RF Ra1 Hret Hfile Hfs Htext Htap Himg HK.
  destruct Hfile as (Hf8 & Hf184 & Hf192 & Hfw & HF1 & HF2). destruct Htext as (Tb & Tn & TQ1 & TQ2 & TQ3 & Td & Tr). destruct Htap as (Ta1 & Ta2 & _).
  cbn [PDC.a_scanexp PDC.a_img_lo PDC.a_img_hi PDCU.ubsan11] in *. unfold PDC.STK_FLOOR in *.
  set (N := Z.of_nat (length txt)) in *. assert (HN0 : 0 <= N) by (unfold N; lia).
  set (E0 := mkE R P' N). set (c := entry_cp N).
  assert (U2 : bv_unsigned (ev E0 2) = sp) by exact Rsp.
  assert (U10 : bv_unsigned (ev E0 10) = F) by exact RF.
  assert (U32 : bv_unsigned (ev E0 32) = P') by (change (ev E0 32) with (Z_to_bv 64 P'); apply u64_of_Z; lia).
  assert (U33 : bv_unsigned (ev E0 33) = N) by (change (ev E0 33) with (Z_to_bv 64 N); apply u64_of_Z; lia).
  assert (R_SP : PDC.STK_FLOOR + 80 <= sp <= 2 ^ 47) by (unfold PDC.STK_FLOOR; lia).
  assert (R_F : PDC.STK_FLOOR <= F /\ F + 256 <= 2 ^ 47) by (unfold PDC.STK_FLOOR; lia).
  assert (R_Q : 4096 <= P' /\ P' + N < 2 ^ 47 /\ N < 2 ^ 26) by lia.
  set (XIf := SXS.XI CPS txt).
  set (AMB := SXS.Amb CPS txt E0 M model).
  assert (CUT : forall i0 c0, nth_error CPS i0 = Some c0 -> SXS.cut_chk c0 = true) by (intros i0 c0 Hc0; exact (CC.cps_all_sound _ _ cuts_ok i0 c0 Hc0)).
  assert (Hci : nth_error CPS (entry_ix N) = Some c /\ SXS.kind_of c = SXS.KE /\ CC.cp_pc c = 738700).
  { unfold c, entry_cp, entry_ix. destruct (N =? 0); [|destruct (N =? 1)]; (split; [reflexivity | split; vm_compute; reflexivity]). }
  destruct Hci as (Hci & Hki & Hpc). rewrite <- Hpc.
  eapply (CC.cutcert_sound_tagged RSEGS CPS TAGS SXS.NF AMB K FrmInv.fp_ok
            (fun fx1 fx2 R1 pc1 M1 R2 pc2 M2 H => FrmInv.msteps_fp_ok RSEGS Pm10FrmInv.text_safe fx1 fx2 R1 _ M1 _ R2 _ M2 _ H) ScanexpLems_u.plans_ok tags_ok)
    with (i := entry_ix N) (c := c) (E := E0).
  - intros i E M1 m1 H. exact (CVX.ambx_model SXS.NF E0 M model SXS.FOOT XIf Hh Hl i E M1 m1 H).
  -
    intros i c1 tags k ps j s Hc1 Htags Hps Htag.
    destruct (CC.tags_chk_go_nth CPS SXS.NF CPS TAGS i c1 tags_ok Hc1) as (tags' & Htags' & Hlv). rewrite Htags in Htags'. injection Htags' as <-.
    destruct (CC.leaves_chk_nth CPS SXS.NF c1 _ tags k ps Hlv Hps) as (t & Ht & Hg). rewrite Htag in Ht. injection Ht as <-. destruct Hg as (cj & Hcj & Hg).
    pose proof (CH2.leaves_all_nth CPS TAGS lchk leaves_ok i c1 tags k ps _ Hc1 Htags Hps Htag) as G2. unfold lchk, SXS.leaf_chk in G2. rewrite Hcj in G2.
    apply CVX.ambx_goto; [exact (SXS.sub_F_ok E0 c1 (CUT i c1 Hc1)) | exact (SXS.cut_nf c1 (CUT i c1 Hc1)) |].
    intros E R1 M1 m1 E' R' M' HAt1 HAmb1 Hag HLF.
    exact (SXS.xi_goto RSEGS CPS txt P' F sp E0 M model U2 U10 U32 U33 R_SP R_F R_Q Tb Tn Tr Ta1 Ta2 i c1 ps j cj s E R1 M1 m1 E' R' M' Hc1 Hcj (CUT i c1 Hc1) (CUT j cj Hcj) Hg G2 HAt1 HAmb1 Hag HLF).
  -
    intros i c1 tags k ps id Hc1 Htags Hps Htag.
    pose proof (CH2.leaves_all_nth CPS TAGS lchk leaves_ok i c1 tags k ps _ Hc1 Htags Hps Htag) as X. unfold lchk, SXS.leaf_chk in X.
    intros fx' E R1 M1 m1 E' R' M' HAt1 HAmb1 HFP Hag HLF _.
    destruct (SXS.exit_ok RSEGS CPS RET_PC txt P' F sp E0 M model U2 U10 U32 U33 R_SP R_F R_Q Tb Tn Tr Ta1 Ta2 i c1 ps E R1 M1 m1 E' R' M' Hc1 (CUT i c1 Hc1) X HAt1 HAmb1 Hag HLF)
      as (Hpc' & -> & Hcs & Hfr' & Hgr' & Hpost).
    assert (Hkeep : forall x : nat, In x SXS.CSAVED -> getr R' (PDC.reg_of x) = getr R (PDC.reg_of x)).
    { intros x Hx. unfold PDC.reg_of. rewrite (Hcs x Hx). unfold E0, mkE. cbn [ev]. unfold reg_ev.
      assert (Hlt : Nat.ltb x 32 = true) by (apply Nat.ltb_lt; unfold SXS.CSAVED in Hx; cbn [In] in Hx; lia). rewrite Hlt. reflexivity. }
    assert (Hra : getr R' 1%bv = getr R (PDC.reg_of 1)).
    { replace (1%bv : bv 5) with (PDC.reg_of 1) by (apply bv_eq; reflexivity). apply Hkeep. cbn; tauto. }
    rewrite Hpc'. eapply CL.ret_cps; [exact ret_pc_ok | exact Hh | exact Hl | rewrite Hra; exact Hret |]. rewrite Hra.
    apply HK; [exact HFP | | exact Hgr' | exact Hkeep | exact Hpost].
    intros a A1 A2. apply Hfr'. split; assumption.
  - exact Hci.
  -
    split.
    + apply DOK.regs_ok_tmpl. intros n Hn. pose proof (rz_word R 11 1 Ra1) as W11.
      unfold c, entry_cp. destruct (N =? 0); [|destruct (N =? 1)]; (do 32 (destruct n as [|n]; [first [lia | reflexivity | (symmetry; exact W11)]|]); lia).
    + assert (ES2 : forall o, estart E0 (SA (EVar 2) o) = sp + o) by (intros o; apply (DOS.estart_reg E0 2 o sp U2)).
      assert (ES10 : forall o, estart E0 (SA (EVar 10) o) = F + o) by (intros o; apply (DOS.estart_reg E0 10 o F U10)).
      assert (ES32 : forall o, estart E0 (SA (EVar 32) o) = P' + o) by (intros o; apply (DOS.estart_reg E0 32 o P' U32)).
      assert (EL : forall z, 0 <= z < 2 ^ 64 -> elenZ E0 (ELit z) = z) by (intros z Hz; apply DOS.elen_lit; exact Hz).
      assert (ELN : elenZ E0 (EVar 33) = N) by exact U33.
      assert (ELN1 : elenZ E0 (EAlu ALU_ADD (EVar 33) (ELit 1)) = N + 1).
      { unfold elenZ. cbn [edenot]. rewrite u_add64, U33. rewrite u64_of_Z by lia. apply Z.mod_small. lia. }
      assert (ESN : estart E0 (SA (EAlu ALU_ADD (EVar 32) (EVar 33)) 0) = P' + N).
      { unfold estart. cbn [a_base a_off edenot]. rewrite u_add64, U32, U33. rewrite Z.mod_small by lia. lia. }
      assert (KN : forall lo hi, lo <= N <= hi -> kentry_ok RSEGS E0 M (KRange (EVar 33) lo hi)) by (intros lo hi Hr; cbn [kentry_ok edenot]; rewrite U33; exact Hr).
      assert (REST : forall lo hi, lo <= N <= hi -> know_ok RSEGS E0 M
                [KRange (EVar 2) 140735332483152 140737488355328; KAlign (EVar 2) 16; KImg 65536 801400; KWr (SA (EVar 2) (-80)) (ELit 80); KWr (SA (EVar 10) 8) (ELit 8);
                 KRange (EVar 10) 140735332483072 140737488355072; KDisj (SA (EVar 10) 8) (ELit 192) (SA (EVar 2) (-80)) (ELit 80); KRange (EVar 32) 4096 140737488355328; KRange (EVar 33) lo hi;
                 KWord (SA (EVar 10) 184) 8 (ELit 18446744073709551615); KWord (SA (EVar 10) 192) 8 (ELit 0); KUnk (SA (EVar 32) 0) (EVar 33);
                 KZero (SA (EAlu ALU_ADD (EVar 32) (EVar 33)) 0) (ELit 1); KDisj (SA (EVar 32) 0) (EAlu ALU_ADD (EVar 33) (ELit 1)) (SA (EVar 2) (-80)) (ELit 80);
                 KDisj (SA (EVar 32) 0) (EAlu ALU_ADD (EVar 33) (ELit 1)) (SA (EVar 10) 8) (ELit 192); KWord (SA (EVar 10) 8) 8 (EVar 32); KUnk (SA (EVar 2) (-80)) (ELit 80)]).
      { intros lo hi Hr. unfold know_ok. unfold PDC.apart in *.
        apply Forall_cons; [cbn [kentry_ok edenot]; rewrite U2; lia|].
        apply Forall_cons; [cbn [kentry_ok edenot]; rewrite U2; split; [lia | exact Hal]|].
        apply Forall_cons; [cbn [kentry_ok]; split; [lia | split; [lia | exact Himg]]|].
        apply Forall_cons; [apply (DOK.kwr_of_writable RSEGS E0 M _ _ (sp - 80) 80); [rewrite ES2; lia | apply EL; lia | lia | lia | lia | lia | exact Hwr]|].
        apply Forall_cons; [apply (DOK.kwr_of_writable RSEGS E0 M _ _ (F + 8) 8); [rewrite ES10; lia | apply EL; lia | lia | lia | lia | lia | exact Hfw]|].
        apply Forall_cons; [cbn [kentry_ok edenot]; rewrite U10; lia|].
        apply Forall_cons; [cbn [kentry_ok]; rewrite ES10, ES2, !EL by lia; lia|].
        apply Forall_cons; [cbn [kentry_ok edenot]; rewrite U32; lia|].
        apply Forall_cons; [exact (KN lo hi Hr)|].
        apply Forall_cons; [apply (CL5.kword64_intro RSEGS E0 M _ _ (F + 184) (2 ^ 64 - 1)); [rewrite ES10; lia | lia | lia | reflexivity | exact Hf184]|].
        apply Forall_cons; [apply (CL5.kword64_intro RSEGS E0 M _ _ (F + 192) 0); [rewrite ES10; lia | lia | lia | reflexivity | exact Hf192]|].
        apply Forall_cons; [apply (CL5.kunk_intro RSEGS E0 M _ _ P' N); [rewrite ES32; lia | exact ELN | lia | lia | lia | intros d Hd; apply Td; lia]|].
        apply Forall_cons; [apply (DOK.kzero1_intro RSEGS E0 M _ (P' + N)); [rewrite ESN; lia | lia | lia | exact Tn | apply Td; lia]|].
        apply Forall_cons; [cbn [kentry_ok]; rewrite ES32, ES2, ELN1, !EL by lia; lia|].
        apply Forall_cons; [cbn [kentry_ok]; rewrite ES32, ES10, ELN1, !EL by lia; lia|].
        apply Forall_cons; [apply (CL5.kword64_intro RSEGS E0 M _ _ (F + 8) P'); [rewrite ES10; lia | lia | lia | reflexivity | exact Hf8]|].
        apply Forall_cons; [apply (CL5.kunk_intro RSEGS E0 M _ _ (sp - 80) 80); [rewrite ES2; lia | apply EL; lia | lia | lia | lia | exact Hdef] | constructor]. }
      unfold c, entry_cp. destruct (Z.eqb_spec N 0); [|destruct (Z.eqb_spec N 1)].
      * exact (REST 0 0 ltac:(lia)).
      * exact (REST 1 1 ltac:(lia)).
      * exact (REST 2 67108864 ltac:(lia)).
  - split; [split; [reflexivity | split; [apply CC.env_agree_refl | split; [reflexivity | apply mem_grows_refl]]]|].
    unfold SXS.XI. rewrite Hci, Hki. exact I.
  - exact Hfp.
Qed.
End Run.
End SXO.

