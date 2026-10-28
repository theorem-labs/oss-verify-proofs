(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import L5Defs L5Core
  FrmInv. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6FrmInv_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import CutVF. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import DecIface_u5 DecJson_u5 DecScanPure_u5 DecOkDefs_u5 DecOkSem_u5 DecfloatPre_u5 DecfloatAt_u5 StrtodPure_u5 StrtodIface_u5 FsHeadOk_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.FCutCert Require Import CutCert CutOps CutHeap CutAuto CutLib CutL5 CutOpsD CutAutoD. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.FCutCert Require Import Pm6CutKitD_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.FCutGen Require Import Cut_fshead_xsrc_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S. Import DOK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module FSO.
Definition ghost (s CAN va vb : Z) (n : nat) : word :=
  match n with 32 => Z_to_bv 64 s | 33 => Z_to_bv 64 CAN | 34 => Z_to_bv 64 va | 35 => Z_to_bv 64 vb | _ => Z_to_bv 64 0 end%nat.
Definition mkE (R : bvmap 5 word) (s CAN va vb : Z) : env := Env (reg_ev R (ghost s CAN va vb)) (fun _ => []).
Lemma not45 : forall c (r : list Z), c <> 45 -> match c :: r with 45 :: _ => 1 | _ => 0 end = 0.
Proof. intros c r H. destruct c as [|p|p]; try reflexivity. do 6 (destruct p as [p|p|]; try reflexivity). exfalso; apply H; reflexivity. Qed.

Section Final.
Context {SCFG_P : ScfgP}.
Hypothesis FMODL : CVF.vf_contract RSEGS 0xbb134 192 DFO.IMGc.
Hypothesis SCX : PDC.scanexp_contract RSEGS PDC.src11.

Theorem floatscan_ok : PSI.floatscan_contract RSEGS PDC.src11 0xb8fa0.
Proof.
  intros fx R M model K sp F s CAN txt Hh Hl Hfp Rsp Hal Hrng Hdef RF R11 R12 R4 Hret Hfile Hfs Hguard Hgap Htext Htap Hnf Herrw Himg HK.
  cbn [PDC.a_G PDC.a_TP PDC.a_img_lo PDC.a_img_hi PDC.src11] in *.
  pose proof (PDJ.json_full txt Hnf) as Hfull. cbv zeta in Hfull. fold (FHO.N txt) in Hfull. change (PDJ.len txt) with (FHO.N txt) in Hfull.
  destruct (PSP.final_after0 txt Hnf) as [A0 A1].
  pose proof Hfile as (Hf8 & Hf184 & Hf192 & Hfw & HF1 & HF2). pose proof Htext as (Tb & Tn & TQ1 & TQ2 & TQ3 & Td & Tr). pose proof Htap as (Ta1 & Ta2 & Ta3).
  fold (FHO.N txt) in Tn, TQ2, TQ3, Td, Ta1, Ta2. set (N := FHO.N txt) in *.
  (* [comment removed for export] *)
  assert (COMMON : forall va vb nb tail, 2 <= nb <= 3 -> nb <= N + 1 ->
            let E0 := mkE R s CAN va vb in know_ok RSEGS E0 M tail ->
            know_ok RSEGS E0 M
              ([KRange (EVar 2) 140735332491744 140737488355328; KAlign (EVar 2) 16; KImg 65536 827984; KWr (SA (EVar 2) (-8672)) (ELit 8672); KUnk (SA (EVar 2) (-8672)) (ELit 8672);
                KWr (SA (EVar 10) 8) (ELit 8); KRange (EVar 10) 140735332483072 140737488355072; KDisj (SA (EVar 10) 8) (ELit 192) (SA (EVar 2) (-8672)) (ELit 8672);
                KRange (EVar 32) 4096 140737488355328; KWord (SA (EVar 10) 8) 8 (EVar 32); KWord (SA (EVar 10) 184) 8 (ELit 18446744073709551615);
                KWord (SA (EVar 10) 192) 8 (ELit 0); KWord (SA (ELit 0) 1036928) 8 (EVar 33);
                KDisj (SA (EVar 32) 0) (ELit nb) (SA (EVar 2) (-8672)) (ELit 8672); KDisj (SA (EVar 32) 0) (ELit nb) (SA (EVar 10) 8) (ELit 192)] ++ tail)).
  { intros va vb nb tail Hnb HnbN E0 Htail. unfold PDC.STK_FLOOR, PSI.WIN, PDC.apart in *.
    assert (U2 : bv_unsigned (ev E0 2) = sp) by exact Rsp.
    assert (U10 : bv_unsigned (ev E0 10) = F) by exact RF.
    assert (U32 : bv_unsigned (ev E0 32) = s) by (change (ev E0 32) with (Z_to_bv 64 s); apply u64_of_Z; lia).
    assert (ES2 : forall o, estart E0 (SA (EVar 2) o) = sp + o) by (intros o; apply (DOS.estart_reg E0 2 o sp U2)).
    assert (ES10 : forall o, estart E0 (SA (EVar 10) o) = F + o) by (intros o; apply (DOS.estart_reg E0 10 o F U10)).
    assert (ES32 : forall o, estart E0 (SA (EVar 32) o) = s + o) by (intros o; apply (DOS.estart_reg E0 32 o s U32)).
    assert (EL : forall z, 0 <= z < 2 ^ 64 -> elenZ E0 (ELit z) = z) by (intros z Hz; apply DOS.elen_lit; exact Hz).
    unfold know_ok. cbn [app].
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
    apply Forall_cons; [apply (CL5.kword64_intro RSEGS E0 M _ _ 1036928 CAN); [rewrite DOS.estart_lit by lia; lia | lia | lia | reflexivity | exact Hguard]|].
    apply Forall_cons; [cbn [kentry_ok]; rewrite ES32, ES2, !EL by lia; lia|].
    apply Forall_cons; [cbn [kentry_ok]; rewrite ES32, ES10, !EL by lia; lia|].
    exact Htail. }
  assert (REGS : forall va vb regs, regs = CC.cp_regs cp0 -> regs_ok (mkE R s CAN va vb) regs R).
  { intros va vb regs ->. apply DOK.regs_ok_tmpl. intros n Hn.
    pose proof (DOK.rz_word R 4 _ R4) as W4. pose proof (DOK.rz_word R 11 _ R11) as W11. pose proof (DOK.rz_word R 12 _ R12) as W12.
    do 32 (destruct n as [|n]; [first [lia | reflexivity | (symmetry; first [exact W4 | exact W11 | exact W12])]|]); lia. }
  assert (BYTE : forall i, 0 <= i <= N -> L5.u8_at RSEGS M (s + i) (nth (Z.to_nat i) (FHO.txt' txt) 0) /\ 0 <= nth (Z.to_nat i) (FHO.txt' txt) 0 < 256).
  { intros i Hi. unfold FHO.txt'. destruct (Z.eq_dec i N) as [->|Hne].
    - rewrite app_nth2 by (unfold N, FHO.N; lia). replace (Z.to_nat N - length txt)%nat with 0%nat by (unfold N, FHO.N; lia). cbn [nth]. split; [exact Tn | lia].
    - assert (Hlt : (Z.to_nat i < length txt)%nat) by (unfold N, FHO.N in *; lia). rewrite app_nth1 by exact Hlt. split.
      + pose proof (Tb (Z.to_nat i) Hlt) as B. rewrite Z2Nat.id in B by lia. exact B.
      + rewrite Forall_forall in Tr. apply Tr. apply nth_In. exact Hlt. }
  assert (KB : forall va vb o cv v, 0 <= o <= N -> bv_unsigned (ev (mkE R s CAN va vb) cv) = v -> v = nth (Z.to_nat o) (FHO.txt' txt) 0 ->
            kentry_ok RSEGS (mkE R s CAN va vb) M (KWord (SA (EVar 32) o) 1 (EVar cv))).
  { intros va vb o cv v Ho Hv ->. destruct (BYTE o Ho) as [B1 B2]. unfold PDC.STK_FLOOR in *.
    apply (DOK.kword8_intro RSEGS (mkE R s CAN va vb) M (SA (EVar 32) o) (EVar cv) (s + o) (nth (Z.to_nat o) (FHO.txt' txt) 0)); [| lia | lia | exact Hv | exact B2 | exact B1].
    apply (DOS.estart_reg (mkE R s CAN va vb) 32 o s). change (ev (mkE R s CAN va vb) 32) with (Z_to_bv 64 s). apply u64_of_Z. lia. }
  assert (HK' : forall (fx' : FPState) R' M', FrmInv.fp_ok fx' ->
      (forall x : nat, In x PSI.CSAVED -> getr R' (PDC.reg_of x) = getr R (PDC.reg_of x)) ->
      (forall a : word, ~ (sp - PSI.WIN <= bv_unsigned a < sp) -> ~ (F + 8 <= bv_unsigned a < F + 16) -> ~ (FHO.TPV - 164 <= bv_unsigned a < FHO.TPV - 160) -> M' a = M a) ->
      mem_grows M M' -> L5.u64_at RSEGS M' (F + 8) (s + N) ->
      srealizes RSEGS SCFG (mkCfg (@mkst fx' R' (getr R (PDC.reg_of 1)) M' (seg_rom RSEGS)) model) K).
  { intros fx' R' M' X1 X2 X3 X4 X5. apply HK; assumption. }
  destruct (PSP.final_shape txt Hnf) as [(c0 & r & Et & Hd) | (c1 & r & Et & Hd)].
  - (* [comment removed for export] *)
    assert (Hc45 : c0 <> 45) by (intros ->; discriminate Hd).
    assert (HN1 : 1 <= N) by (unfold N, FHO.N; rewrite Et; cbn [length]; lia).
    assert (Hfull0 : 0 + PD.dec_len (skipn (Z.to_nat 0) txt) = N).
    { clear - Hfull Et Hc45. rewrite Et in Hfull |- *. destruct c0 as [|p|p]; try exact Hfull. do 6 (destruct p as [p|p|]; try exact Hfull). exfalso; apply Hc45; reflexivity. }
    clear Hfull. rename Hfull0 into Hfull.
    assert (Rc0 : 48 <= c0 <= 57) by (unfold PD.is_dig in Hd; apply andb_prop in Hd as [D1 D2]; apply Z.leb_le in D1, D2; lia).
    set (c1 := nth 1 (FHO.txt' txt) 0). destruct (BYTE 1 ltac:(lia)) as [_ Rc1]. change (Z.to_nat 1) with 1%nat in Rc1. fold c1 in Rc1.
    set (E0 := mkE R s CAN c0 c1).
    change (Z_to_bv 64 758688) with (Z_to_bv 64 (CC.cp_pc cp0)).
    refine (FHO.head_run FMODL SCX R M model K sp F s CAN txt E0 0 Hh Hl _ _ eq_refl Rsp Hal Hrng Hdef RF R4 Hret Hfile Hfs Hgap Htext Htap Herrw Himg _ Hfull _ HK' 0%nat (or_introl (conj eq_refl eq_refl)) fx cp0 eq_refl _ Hfp).
    + intros n Hn. unfold E0, mkE. cbn [ev]. unfold reg_ev. apply Nat.ltb_lt in Hn. rewrite Hn. reflexivity.
    + change (ev E0 32) with (Z_to_bv 64 s). apply u64_of_Z. unfold PDC.STK_FLOOR in *. lia.
    + fold N. lia.
    + intros H48. apply (A0 r). change (Z.to_nat 0) with 0%nat in H48. unfold FHO.txt' in H48. rewrite Et in H48. cbn [app nth] in H48. rewrite Et, H48. reflexivity.
    + split; [apply (REGS c0 c1); reflexivity|]. (let k := eval vm_compute in (CC.cp_know cp0) in change (CC.cp_know cp0) with k).
      apply (COMMON c0 c1 2 [KWord (SA (EVar 32) 0) 1 (EVar 34); KRange (EVar 34) 48 57; KWord (SA (EVar 32) 1) 1 (EVar 35); KRange (EVar 35) 0 255] ltac:(lia) ltac:(lia)).
      assert (V34 : bv_unsigned (ev E0 34) = c0) by (change (ev E0 34) with (Z_to_bv 64 c0); apply u64_of_Z; lia).
      assert (V35 : bv_unsigned (ev E0 35) = c1) by (change (ev E0 35) with (Z_to_bv 64 c1); apply u64_of_Z; lia).
      apply Forall_cons; [apply (KB c0 c1 0 34%nat c0 ltac:(lia) V34); unfold FHO.txt'; rewrite Et; reflexivity|].
      apply Forall_cons; [cbn [kentry_ok]; unfold E0 in V34; change (edenot ?e (EVar 34)) with (ev e 34); rewrite V34; lia|].
      apply Forall_cons; [apply (KB c0 c1 1 35%nat c1 ltac:(lia) V35); reflexivity|].
      apply Forall_cons; [cbn [kentry_ok]; unfold E0 in V35; change (edenot ?e (EVar 35)) with (ev e 35); rewrite V35; lia | constructor].
  - (* [comment removed for export] *)
    assert (HN2 : 2 <= N) by (unfold N, FHO.N; rewrite Et; cbn [length]; lia).
    assert (Hfull1 : 1 + PD.dec_len (skipn (Z.to_nat 1) txt) = N) by (clear - Hfull Et; rewrite Et in Hfull |- *; exact Hfull).
    clear Hfull. rename Hfull1 into Hfull.
    assert (Rc1 : 48 <= c1 <= 57) by (unfold PD.is_dig in Hd; apply andb_prop in Hd as [D1 D2]; apply Z.leb_le in D1, D2; lia).
    set (c2 := nth 2 (FHO.txt' txt) 0). destruct (BYTE 2 ltac:(lia)) as [_ Rc2]. change (Z.to_nat 2) with 2%nat in Rc2. fold c2 in Rc2.
    set (E0 := mkE R s CAN c1 c2).
    change (Z_to_bv 64 758688) with (Z_to_bv 64 (CC.cp_pc cp1)).
    refine (FHO.head_run FMODL SCX R M model K sp F s CAN txt E0 1 Hh Hl _ _ eq_refl Rsp Hal Hrng Hdef RF R4 Hret Hfile Hfs Hgap Htext Htap Herrw Himg _ Hfull _ HK' 1%nat (or_intror (conj eq_refl eq_refl)) fx cp1 eq_refl _ Hfp).
    + intros n Hn. unfold E0, mkE. cbn [ev]. unfold reg_ev. apply Nat.ltb_lt in Hn. rewrite Hn. reflexivity.
    + change (ev E0 32) with (Z_to_bv 64 s). apply u64_of_Z. unfold PDC.STK_FLOOR in *. lia.
    + fold N. lia.
    + intros H48. assert (E48 : c1 = 48) by (change (Z.to_nat 1) with 1%nat in H48; unfold FHO.txt' in H48; rewrite Et in H48; cbn [app nth] in H48; exact H48).
      subst c1. exact (A1 r Et).
    + split; [apply (REGS c1 c2); reflexivity|]. (let k := eval vm_compute in (CC.cp_know cp1) in change (CC.cp_know cp1) with k).
      apply (COMMON c1 c2 3 [KWord (SA (EVar 32) 0) 1 (ELit 45); KWord (SA (EVar 32) 1) 1 (EVar 34); KRange (EVar 34) 48 57; KWord (SA (EVar 32) 2) 1 (EVar 35); KRange (EVar 35) 0 255] ltac:(lia) ltac:(lia)).
      assert (V34 : bv_unsigned (ev E0 34) = c1) by (change (ev E0 34) with (Z_to_bv 64 c1); apply u64_of_Z; lia).
      assert (V35 : bv_unsigned (ev E0 35) = c2) by (change (ev E0 35) with (Z_to_bv 64 c2); apply u64_of_Z; lia).
      apply Forall_cons.
      { destruct (BYTE 0 ltac:(lia)) as [B1 B2]. unfold PDC.STK_FLOOR in *.
        apply (DOK.kword8_intro RSEGS E0 M _ _ (s + 0) 45); [| lia | lia | reflexivity | lia |].
        - apply (DOS.estart_reg E0 32 0 s). change (ev E0 32) with (Z_to_bv 64 s). apply u64_of_Z. lia.
        - change (Z.to_nat 0) with 0%nat in B1. unfold FHO.txt' in B1. rewrite Et in B1. cbn [app nth] in B1. exact B1. }
      apply Forall_cons; [apply (KB c1 c2 1 34%nat c1 ltac:(lia) V34); unfold FHO.txt'; rewrite Et; reflexivity|].
      apply Forall_cons; [cbn [kentry_ok]; unfold E0 in V34; change (edenot ?e (EVar 34)) with (ev e 34); rewrite V34; lia|].
      apply Forall_cons; [apply (KB c1 c2 2 35%nat c2 ltac:(lia) V35); reflexivity|].
      apply Forall_cons; [cbn [kentry_ok]; unfold E0 in V35; change (edenot ?e (EVar 35)) with (ev e 35); rewrite V35; lia | constructor].
Qed.
End Final.
End FSO.
