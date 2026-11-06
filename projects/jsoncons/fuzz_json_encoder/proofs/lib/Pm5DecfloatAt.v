(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StreamSim Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto HeapIface HeapIfaceA L5Defs L5Core L5LazyA
  Pm5PlanKit Pm5L5DefsA FrmInv PmHeapIfaceA CutVFXM DecIface DecScanPure DecOkDefsM DecOkSemM DecOkSemA DecIfaceA FloatLazyA DecOkLazyA Pm5DecKinds5 Pm5DecfloatPre.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutVF.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutHeap2 CutAuto CutLib CutL5 CutOpsD CutAutoD CutCertA CutHeapA CutL5A CutBridgeA CutPureA CutVFA Pm5CutKitD DecAssume.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_decfloat5_xboth.
Import ListNotations. Import AX2. Import AX2B. Import AX2S. Import DOK. Import DFOA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module DFAA.
(* [comment removed for export] *)
Definition hvf (regs : list expr) (R : bvmap 5 word) (n : nat) : word :=
  match find (fun r => expr_eqb (nth r regs (ELit 0)) (EVar n)) (seq 1 31) with Some r => getr R (Z_to_bv 5 (Z.of_nat r)) | None => Z_to_bv 64 0 end.
Definition ghost (Q CAN N : Z) (sv : nat -> Z) (regs : list expr) (R : bvmap 5 word) (n : nat) : word :=
  match n with
  | 32 => Z_to_bv 64 Q | 33 => Z_to_bv 64 CAN
  | 34 => Z_to_bv 64 (sv 1) | 35 => Z_to_bv 64 (sv 8) | 36 => Z_to_bv 64 (sv 9) | 37 => Z_to_bv 64 (sv 18) | 38 => Z_to_bv 64 (sv 19) | 39 => Z_to_bv 64 (sv 20)
  | 40 => Z_to_bv 64 (sv 21) | 41 => Z_to_bv 64 (sv 22) | 42 => Z_to_bv 64 (sv 23) | 43 => Z_to_bv 64 (sv 24) | 44 => Z_to_bv 64 (sv 25) | 45 => Z_to_bv 64 (sv 26)
  | 46 => Z_to_bv 64 (sv 27) | 47 => Z_to_bv 64 N
  | _ => hvf regs R n
  end%nat.
Definition mkE0 (Q CAN N : Z) (sv : nat -> Z) (regs : list expr) (R : bvmap 5 word) : env := Env (reg_ev R (ghost Q CAN N sv regs R)) (fun _ => []).
Lemma mkE0_ok : forall Q CAN N sv regs R, DOLA.E0_ok (mkE0 Q CAN N sv regs R) R Q CAN sv N.
Proof.
  intros. split; [intros x; apply CL5.ev_reg|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  intros r v Hin. unfold DOS.SAVE_VARS in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; reflexivity|]). destruct Hin.
Qed.

Definition kn0 : list kentry := Eval vm_compute in CC.cp_know cp0.
Definition kn1 : list kentry := Eval vm_compute in CC.cp_know cp1.
Definition kn2 : list kentry := Eval vm_compute in CC.cp_know cp2.
Definition rg0 : list expr := Eval vm_compute in CC.cp_regs cp0.
Definition rg1 : list expr := Eval vm_compute in CC.cp_regs cp1.
Definition rg2 : list expr := Eval vm_compute in CC.cp_regs cp2.
Definition entry_cp (e2 : bool) (N : Z) : CC.cutpoint := if e2 then (if N =? 1 then cp1 else cp2) else cp0.
Definition entry_ix (e2 : bool) (N : Z) : nat := if e2 then (if N =? 1 then 1%nat else 2%nat) else 0%nat.
Lemma entry_ok : forall e2 N, nth_error CPS (entry_ix e2 N) = Some (entry_cp e2 N) /\ DOSA.kind_of CPS RETS DK5.DKINDS SCANEXP (entry_ix e2 N) = KEnt
  /\ CC.cp_pc (entry_cp e2 N) = (if e2 then PDC.a_E2 AD else PDC.a_E1 AD).
Proof. intros e2 N. unfold entry_ix, entry_cp. destruct e2; [destruct (N =? 1)|]; (split; [reflexivity | split; [vm_compute; reflexivity | reflexivity]]). Qed.
(* [comment removed for export] *)
Lemma errno_wseg : wseg_ok RSEGS (Z_to_bv 64 ERRNO) 4 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma errno_writable : forall M : word -> option byte, L5.writable RSEGS M ERRNO 4.
Proof.
  intros M d k Hd Hk. apply (store_ok_sub RSEGS M (Z_to_bv 64 ERRNO) (Z_to_bv 64 (ERRNO + d)) 4 k); rewrite ?L5.unsigned_lit by (unfold ERRNO; lia); unfold ERRNO in *; try lia.
  apply store_ok_wseg. exact errno_wseg.
Qed.

Ltac in_saves := cbv; repeat (first [left; reflexivity | right]).

Section Final.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout. Variable ar : asan_run. Variable C : asan_statics_cells. Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis TP : hl_tp L = TPV.

(* [comment removed for export] *)
Lemma entry_at : forall e2 LB FF LK cr A R (M : PDCA.mem) model SP F P Q CAN sv txt,
  ri_inv HI LB FF LK cr A M (vml_of model) -> CHA.astk ar M (SP + PDC.FRAME) (PDC.SCR_D + PDC.FRAME) -> PDCA.dec_preA L ar AD e2 LB FF R M SP F P Q CAN sv txt ->
  let N := Z.of_nat (length txt) in let c := entry_cp e2 N in
  CC.At (hl_segs L) c (mkE0 Q CAN N sv (CC.cp_regs c) R) R (CCA.vis A model M).
Proof.
  intros e2 LB FF LK cr A R M model SP F P Q CAN sv txt HH Hstk (Hpre & HspF & Hfd8 & Hblk & RCAN & RAOK) N c.
  pose proof (L5A.aly_segs L C LAY) as LS. pose proof (L5A.aly_img_lo L C LAY) as ILO. pose proof (L5A.aly_img_hi L C LAY) as IHI.
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO) by (rewrite ILO, IHI; unfold BIGSHADOW_LO; lia).
  destruct Hpre as (Rsp & Hal & Hfloor & Htop & RF & R23 & R18 & R22 & R24 & R9 & R20 & R4 & Hdef & Hwr & Hsaves & Hret & Hcan & Hguard & Hgap & Hfile & Hfs & Htext & Htap & Herrw & Himg & Hent).
  destruct Hfile as (Hf8 & Hf184 & Hf192 & Hfw & HF1 & HF2). destruct Htext as (Tb & Tn & TQ1 & TQ2 & TQ3 & Td & Tr). destruct Htap as (Ta1 & Ta2 & Ta3).
  fold N in Tn, TQ2, TQ3, Td, Ta1, Ta2, Ta3, Hblk. unfold PDC.STK_FLOOR, PDC.FRAME, PDC.SCR_D, PDC.apart in *. cbn [PDC.a_G PDC.a_TP PDC.a_img_lo PDC.a_img_hi AD PDCA.xboth] in *.
  rewrite LS in *. destruct Hstk as (S1 & S2 & S3 & S4 & S5 & S6).
  pose proof (FLA.rng L ar C HI HIok _ _ _ _ _ _ _ HH) as RFx. destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & C8). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & SP16).
  assert (HN0 : 0 <= N) by (unfold N; lia).
  set (E0 := mkE0 Q CAN N sv (CC.cp_regs c) R). set (H := ahid A model). set (Mv := CCA.vis A model M). change (CCA.vis A model M) with Mv.
  assert (U2 : bv_unsigned (ev E0 2) = SP) by exact Rsp.
  assert (U4 : bv_unsigned (ev E0 4) = TPV) by exact R4.
  assert (U21 : bv_unsigned (ev E0 21) = F) by exact RF.
  assert (U32 : bv_unsigned (ev E0 32) = Q) by (change (ev E0 32) with (Z_to_bv 64 Q); apply u64_of_Z; lia).
  assert (U47 : bv_unsigned (ev E0 47) = N) by (change (ev E0 47) with (Z_to_bv 64 N); apply u64_of_Z; lia).
  assert (ES2 : forall o, estart E0 (SA (EVar 2) o) = SP + o) by (intros o; unfold estart; cbn [a_base a_off edenot]; rewrite U2; reflexivity).
  assert (ES4 : forall o, estart E0 (SA (EVar 4) o) = TPV + o) by (intros o; unfold estart; cbn [a_base a_off edenot]; rewrite U4; reflexivity).
  assert (ES21 : forall o, estart E0 (SA (EVar 21) o) = F + o) by (intros o; unfold estart; cbn [a_base a_off edenot]; rewrite U21; reflexivity).
  assert (ES32 : forall o, estart E0 (SA (EVar 32) o) = Q + o) by (intros o; unfold estart; cbn [a_base a_off edenot]; rewrite U32; reflexivity).
  assert (ESL : forall a o, 0 <= a < 2 ^ 64 -> estart E0 (SA (ELit a) o) = a + o) by (intros a o Ha; unfold estart; cbn [a_base a_off edenot]; rewrite u64_of_Z by lia; reflexivity).
  assert (ESQN : forall o, estart E0 (SA (EAlu ALU_ADD (EVar 32) (EVar 47)) o) = Q + N + o).
  { intros o. unfold estart. cbn [a_base a_off edenot]. rewrite u_add64, U32, U47. rewrite Z.mod_small by lia. reflexivity. }
  assert (EL : forall z, 0 <= z < 2 ^ 64 -> elenZ E0 (ELit z) = z) by (intros z Hz; unfold elenZ; cbn [edenot]; apply u64_of_Z; lia).
  assert (ELN : elenZ E0 (EVar 47) = N) by exact U47.
  assert (ELN1 : elenZ E0 (EAlu ALU_ADD (EVar 47) (ELit 1)) = N + 1).
  { unfold elenZ. cbn [edenot]. rewrite u_add64, U47. rewrite u64_of_Z by lia. apply Z.mod_small. lia. }
  (* [comment removed for export] *)
  assert (VS : CL5A.visr H (SP - 256) 8672) by (apply (FLA.stk_visr L ar C HI HIok _ _ _ _ _ _ _ _ _ HH); lia).
  assert (VF : CL5A.visr H (F + 8) 192) by (apply (FLA.stk_visr L ar C HI HIok _ _ _ _ _ _ _ _ _ HH); lia).
  assert (VT : CL5A.visr H Q (N + 1)) by (exact (FLA.txt_visr_h L ar C HI HIok LYI _ _ _ _ _ _ _ (SP + 8416) _ _ HH ltac:(lia) Hblk)).
  assert (VI : forall a n, 0 <= a -> a + n <= hl_img_hi L -> CL5A.visr H a n).
  { intros a n Ha Hn i Hi. apply (CHA.img_vis L ar C HI HIok LYI 48%nat SP ltac:(lia) _ _ _ _ _ _ _ (a + i) HH). lia. }
  rewrite IHI in VI.
  assert (DS : L5.defined Mv (SP - 256) 8672) by (exact (CL5A.defined_vis H M _ _ VS Hdef)).
  assert (DT : L5.defined Mv Q (N + 1)) by (exact (CL5A.defined_vis H M _ _ VT Td)).
  assert (DF8 : L5.defined Mv (F + 8) 8) by (apply (CL5A.defined_vis H M); [apply (CL5A.visr_sub _ (F + 8) 192 (F + 8) 8 VF); lia | exact Hfd8]).
  assert (U64S : forall o v, -256 <= o -> o + 8 <= 8416 -> L5.u64_at RSEGS M (SP + o) v -> L5.u64_at RSEGS Mv (SP + o) v).
  { intros o v H1 H2 Hu. apply (CL5A.u64_vis RSEGS H M); [lia | lia | apply (CL5A.visr_sub _ (SP - 256) 8672 (SP + o) 8 VS); lia | exact Hu]. }
  assert (U64F : forall o v, 8 <= o -> o + 8 <= 200 -> L5.u64_at RSEGS M (F + o) v -> L5.u64_at RSEGS Mv (F + o) v).
  { intros o v H1 H2 Hu. apply (CL5A.u64_vis RSEGS H M); [lia | lia | apply (CL5A.visr_sub _ (F + 8) 192 (F + o) 8 VF); lia | exact Hu]. }
  assert (HNUL : Mv (Z_to_bv 64 (Q + N)) <> None) by (apply DT; lia).
  (* [comment removed for export] *)
  assert (SVK : forall (r : nat) (o : Z) (n : nat), In (r, o) PDC.SAVES -> edenot E0 (EVar n) = Z_to_bv 64 (sv r) -> kentry_ok RSEGS E0 Mv (KWord (SA (EVar 2) (6384 + o)) 8 (EVar n))).
  { intros r o n Hin Hg. pose proof (proj1 (Hsaves r o Hin)) as Hs.
    assert (Ho : 1928 <= o <= 2024) by (unfold PDC.SAVES in Hin; cbn [In] in Hin; repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|]); destruct Hin).
    apply (CL5.kword64_intro RSEGS E0 Mv _ _ (SP + (6384 + o)) (sv r)); [rewrite ES2; lia | lia | lia | exact Hg |].
    apply U64S; [lia | lia |]. rewrite <- Z.add_assoc in Hs. exact Hs. }
  (* [comment removed for export] *)
  assert (COMMON : forall nlo nhi pv tail, nlo <= N <= nhi -> bv_unsigned (edenot E0 pv) = P -> know_ok RSEGS E0 Mv tail ->
            know_ok RSEGS E0 Mv
              ([KRange (EVar 2) 140735332483328 140737488346912; KAlign (EVar 2) 16; KImg IMG_LO IMG_HI; KWr (SA (EVar 2) (-256)) (ELit 256); KWr (SA (EVar 2) 0) (ELit 8416); KWr (SA (EVar 21) 8) (ELit 8);
                KWr (SA (EVar 4) (-164)) (ELit 4); KRange (EVar 4) TPV 6953105; KRange (EVar 21) 140735332483072 140737488355072; KDisj (SA (EVar 21) 8) (ELit 192) (SA (EVar 2) (-256)) (ELit 8672);
                KRange (EVar 32) 4096 140737488355328; KRange (EVar 47) nlo nhi;
                KWord (SA (EVar 2) 8408) 8 (EVar 34); KWord (SA (EVar 2) 8400) 8 (EVar 35); KWord (SA (EVar 2) 8392) 8 (EVar 36); KWord (SA (EVar 2) 8384) 8 (EVar 37);
                KWord (SA (EVar 2) 8376) 8 (EVar 38); KWord (SA (EVar 2) 8368) 8 (EVar 39); KWord (SA (EVar 2) 8360) 8 (EVar 40); KWord (SA (EVar 2) 8352) 8 (EVar 41);
                KWord (SA (EVar 2) 8344) 8 (EVar 42); KWord (SA (EVar 2) 8336) 8 (EVar 43); KWord (SA (EVar 2) 8328) 8 (EVar 44); KWord (SA (EVar 2) 8320) 8 (EVar 45);
                KWord (SA (EVar 2) 8312) 8 (EVar 46); KWord (SA (EVar 2) 8296) 8 (EVar 33); KWord (SA (ELit 0) GA) 8 (EVar 33);
                KWord (SA (EVar 21) 8) 8 pv; KWord (SA (EVar 21) 184) 8 (ELit 18446744073709551615); KWord (SA (EVar 21) 192) 8 (ELit 0);
                KUnk (SA (EVar 2) (-256)) (ELit 256); KUnk (SA (EVar 2) 0) (ELit 8296); KUnk (SA (EVar 2) 8304) (ELit 8); KUnk (SA (EVar 32) 0) (EVar 47); KZero (SA (EAlu ALU_ADD (EVar 32) (EVar 47)) 0) (ELit 1);
                KDisj (SA (EVar 32) 0) (EAlu ALU_ADD (EVar 47) (ELit 1)) (SA (EVar 2) (-256)) (ELit 8672);
                KDisj (SA (EVar 32) 0) (EAlu ALU_ADD (EVar 47) (ELit 1)) (SA (EVar 21) 8) (ELit 192);
                KDisj (SA (EVar 32) 0) (EAlu ALU_ADD (EVar 47) (ELit 1)) (SA (EVar 4) (-164)) (ELit 4)] ++ tail)).
  { intros nlo nhi pv tail HNr Hpv Htail. unfold know_ok. cbn [app]. unfold IMG_LO, IMG_HI, GA, TPV, ERRNO in *.
    destruct (FLA.txt_facts_h L ar C HI HIok LYI _ _ _ _ _ _ _ (SP + 8416) Q (N + 1) HH ltac:(lia) Hblk ltac:(lia)) as (TB1 & TB2 & TB3 & TB4 & TB5). rewrite ILO, IHI in TB4.
    apply Forall_cons; [cbn [kentry_ok edenot]; rewrite U2; lia|].
    apply Forall_cons; [cbn [kentry_ok edenot]; rewrite U2; split; [lia | exact Hal]|].
    apply Forall_cons; [cbn [kentry_ok]; split; [lia | split; [lia |]]; intros a Ha; unfold Mv, CCA.vis, mrestrict; destruct (ahid A model (Z_to_bv 64 a)); [reflexivity | exact (Himg a Ha)]|].
    apply Forall_cons; [apply (CL5.kwr_intro RSEGS E0 Mv _ _ (SP - 256) 256); [rewrite ES2; lia | apply EL; lia | lia | lia | lia | apply (L5.defined_sub Mv (SP - 256) 8672 (SP - 256) 256 DS); lia]|].
    apply Forall_cons; [apply (CL5.kwr_intro RSEGS E0 Mv _ _ SP 8416); [rewrite ES2; lia | apply EL; lia | lia | lia | lia | apply (L5.defined_sub Mv (SP - 256) 8672 SP 8416 DS); lia]|].
    apply Forall_cons; [apply (CL5.kwr_intro RSEGS E0 Mv _ _ (F + 8) 8); [rewrite ES21; lia | apply EL; lia | lia | lia | lia | exact DF8]|].
    apply Forall_cons; [apply (DOK.kwr_of_writable RSEGS E0 Mv _ _ (TPV - 164) 4); [rewrite ES4; unfold TPV; lia | apply EL; lia | unfold TPV; lia | lia | unfold TPV; lia | unfold TPV; lia |]|].
    { apply (CPA.writable_vis RSEGS H M); [unfold TPV; lia | unfold TPV; lia | apply VI; unfold TPV; lia | exact (errno_writable M)]. }
    apply Forall_cons; [cbn [kentry_ok edenot]; rewrite U4; unfold TPV; lia|].
    apply Forall_cons; [cbn [kentry_ok edenot]; rewrite U21; lia|].
    apply Forall_cons; [cbn [kentry_ok]; rewrite ES21, ES2, !EL by lia; lia|].
    apply Forall_cons; [cbn [kentry_ok edenot]; rewrite U32; lia|].
    apply Forall_cons; [cbn [kentry_ok edenot]; rewrite U47; lia|].
    apply Forall_cons; [apply (SVK 1%nat 2024 34%nat); [in_saves | reflexivity] |].
    apply Forall_cons; [apply (SVK 8%nat 2016 35%nat); [in_saves | reflexivity] |].
    apply Forall_cons; [apply (SVK 9%nat 2008 36%nat); [in_saves | reflexivity] |].
    apply Forall_cons; [apply (SVK 18%nat 2000 37%nat); [in_saves | reflexivity] |].
    apply Forall_cons; [apply (SVK 19%nat 1992 38%nat); [in_saves | reflexivity] |].
    apply Forall_cons; [apply (SVK 20%nat 1984 39%nat); [in_saves | reflexivity] |].
    apply Forall_cons; [apply (SVK 21%nat 1976 40%nat); [in_saves | reflexivity] |].
    apply Forall_cons; [apply (SVK 22%nat 1968 41%nat); [in_saves | reflexivity] |].
    apply Forall_cons; [apply (SVK 23%nat 1960 42%nat); [in_saves | reflexivity] |].
    apply Forall_cons; [apply (SVK 24%nat 1952 43%nat); [in_saves | reflexivity] |].
    apply Forall_cons; [apply (SVK 25%nat 1944 44%nat); [in_saves | reflexivity] |].
    apply Forall_cons; [apply (SVK 26%nat 1936 45%nat); [in_saves | reflexivity] |].
    apply Forall_cons; [apply (SVK 27%nat 1928 46%nat); [in_saves | reflexivity] |].
    apply Forall_cons; [apply (CL5.kword64_intro RSEGS E0 Mv _ _ (SP + 8296) CAN); [rewrite ES2; lia | lia | lia | reflexivity | apply U64S; [lia | lia | exact Hcan]]|].
    apply Forall_cons; [apply (CL5.kword64_intro RSEGS E0 Mv _ _ 7084240 CAN); [rewrite ESL by lia; lia | lia | lia | reflexivity |]|].
    { apply (CL5A.u64_vis RSEGS H M); [lia | lia | apply VI; lia | exact Hguard]. }
    apply Forall_cons; [apply (CL5.kword64_intro RSEGS E0 Mv _ _ (F + 8) P); [rewrite ES21; lia | lia | lia | rewrite <- Hpv; rewrite Z_to_bv_bv_unsigned; reflexivity | apply U64F; [lia | lia | exact Hf8]]|].
    apply Forall_cons; [apply (CL5.kword64_intro RSEGS E0 Mv _ _ (F + 184) (2 ^ 64 - 1)); [rewrite ES21; lia | lia | lia | reflexivity | apply U64F; [lia | lia | exact Hf184]]|].
    apply Forall_cons; [apply (CL5.kword64_intro RSEGS E0 Mv _ _ (F + 192) 0); [rewrite ES21; lia | lia | lia | reflexivity | apply U64F; [lia | lia | exact Hf192]]|].
    apply Forall_cons; [apply (CL5.kunk_intro RSEGS E0 Mv _ _ (SP - 256) 256); [rewrite ES2; lia | apply EL; lia | lia | lia | lia | apply (L5.defined_sub Mv (SP - 256) 8672 (SP - 256) 256 DS); lia]|].
    apply Forall_cons; [apply (CL5.kunk_intro RSEGS E0 Mv _ _ SP 8296); [rewrite ES2; lia | apply EL; lia | lia | lia | lia | apply (L5.defined_sub Mv (SP - 256) 8672 SP 8296 DS); lia]|].
    apply Forall_cons; [apply (CL5.kunk_intro RSEGS E0 Mv _ _ (SP + 8304) 8); [rewrite ES2; lia | apply EL; lia | lia | lia | lia | apply (L5.defined_sub Mv (SP - 256) 8672 (SP + 8304) 8 DS); lia]|].
    apply Forall_cons; [apply (CL5.kunk_intro RSEGS E0 Mv _ _ Q N); [rewrite ES32; lia | exact ELN | lia | lia | lia | apply (L5.defined_sub Mv Q (N + 1) Q N DT); lia]|].
    apply Forall_cons; [apply (DOK.kzero1_intro RSEGS E0 Mv _ (Q + N)); [rewrite ESQN; lia | lia | lia | | exact HNUL]|].
    { apply (CL5A.u8_vis RSEGS H M); [lia | lia | apply (CL5A.visr_sub _ Q (N + 1) (Q + N) 1 VT); lia | exact Tn]. }
    apply Forall_cons; [cbn [kentry_ok]; rewrite ES32, ES2, ELN1, !EL by lia; lia|].
    apply Forall_cons; [cbn [kentry_ok]; rewrite ES32, ES21, ELN1, !EL by lia; lia|].
    apply Forall_cons; [cbn [kentry_ok]; rewrite ES32, ES4, ELN1, !EL by lia; unfold TPV in *; lia|].
    exact Htail. }
  (* [comment removed for export] *)
  assert (REGS : forall regs, regs = CC.cp_regs c -> (regs = rg0 \/ regs = rg1 \/ regs = rg2) -> regs_ok (mkE0 Q CAN N sv regs R) regs R).
  { intros regs _ Hrg. apply DOK.regs_ok_tmpl. intros n Hn.
    pose proof (DOK.rz_word R 18 _ R18) as W18. pose proof (DOK.rz_word R 20 _ R20) as W20. pose proof (DOK.rz_word R 22 _ R22) as W22.
    pose proof (DOK.rz_word R 23 _ R23) as W23. pose proof (DOK.rz_word R 24 _ R24) as W24.
    destruct Hrg as [-> | [-> | ->]];
      do 32 (destruct n as [|n]; [first [reflexivity | (symmetry; first [exact W18 | exact W20 | exact W22 | exact W23 | exact W24]) | lia]|]); lia. }
  split.
  - apply REGS; [reflexivity|]. unfold c, entry_cp. destruct e2; [destruct (N =? 1)|]; [right; left | right; right | left]; reflexivity.
  - unfold c, entry_cp in *. destruct e2.
    + destruct Hent as (HQ & r0 & Et). assert (HN1 : 1 <= N) by (unfold N; rewrite Et; cbn [length]; lia).
      destruct (Z.eqb_spec N 1) as [E1|E1].
      * change (CC.cp_know cp1) with kn1. unfold kn1. rewrite <- (app_nil_r [KDisj (SA (EVar 32) 0) (EAlu ALU_ADD (EVar 47) (ELit 1)) (SA (EVar 4) (-164)) (ELit 4)]).
        apply (COMMON 1 1 (EAlu ALU_ADD (EVar 32) (ELit 2)) [] ltac:(lia)); [|constructor].
        cbn [edenot]. rewrite u_add64, U32. rewrite u64_of_Z by lia. rewrite Z.mod_small by lia. lia.
      * change (CC.cp_know cp2) with kn2. unfold kn2. rewrite <- (app_nil_r [KDisj (SA (EVar 32) 0) (EAlu ALU_ADD (EVar 47) (ELit 1)) (SA (EVar 4) (-164)) (ELit 4)]).
        apply (COMMON 2 67108864 (EAlu ALU_ADD (EVar 32) (ELit 2)) [] ltac:(lia)); [|constructor].
        cbn [edenot]. rewrite u_add64, U32. rewrite u64_of_Z by lia. rewrite Z.mod_small by lia. lia.
    + destruct Hent as (HQ & c0 & r0 & Et & Hc0 & Ra0). assert (HN1 : 1 <= N) by (unfold N; rewrite Et; cbn [length]; lia).
      change (CC.cp_know cp0) with kn0. unfold kn0.
      apply (COMMON 1 67108864 (EAlu ALU_ADD (EVar 32) (ELit 1)) [KRange (EVar 48) 49 57; KWord (SA (EAlu ALU_ADD (EVar 32) (ELit (-1))) 1) 1 (EVar 48)] ltac:(lia)).
      * cbn [edenot]. rewrite u_add64, U32. rewrite u64_of_Z by lia. rewrite Z.mod_small by lia. lia.
      * assert (U48 : bv_unsigned (ev E0 48) = c0) by exact Ra0.
        apply Forall_cons; [cbn [kentry_ok edenot]; rewrite U48; lia|]. apply Forall_cons; [|constructor].
        apply (DOK.kword8_intro RSEGS E0 Mv _ _ Q c0); [| lia | lia | exact U48 | lia |].
        -- unfold estart. cbn [a_base a_off edenot]. rewrite u_add64, U32. change (bv_unsigned (Z_to_bv 64 (-1))) with (2 ^ 64 - 1).
           replace (Q + (2 ^ 64 - 1)) with (Q - 1 + 1 * 2 ^ 64) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
        -- pose proof (Tb 0%nat ltac:(rewrite Et; cbn; lia)) as B. rewrite Et in B. cbn [nth] in B. replace (Q + Z.of_nat 0) with Q in B by lia.
           apply (CL5A.u8_vis RSEGS H M); [lia | lia | apply (CL5A.visr_sub _ Q (N + 1) Q 1 VT); lia | exact B].
Qed.
End Final.
End DFAA.
