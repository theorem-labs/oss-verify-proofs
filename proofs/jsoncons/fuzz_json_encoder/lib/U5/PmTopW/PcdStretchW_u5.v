(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutL5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmTop Require Import TopKit_u5 TopKit2_u5 TopSpecs_u5 ReadKit_u5 ChunkKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Cut_pcd_a_xsrc_u5 Cut_pcd_b_xsrc_u5 Cut_pcd_c_xsrc_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmTop Require Import PcdStretch_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmRef_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Module PSW.
Import PS.
Module GB := Cut_pcd_b_xsrc_u5.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
(* [comment removed for export] *)
Definition mtest (b : Z) : word := alu64 ALU_AND (alu64 ALU_SRL (Z_to_bv 64 PT.MASK) (Z_to_bv 64 b)) (Z_to_bv 64 1).
Lemma ws_tab : forallb (fun n => Bool.eqb (negb (Z.eqb (bv_unsigned (mtest (Z.of_nat n))) 0)) (PMR.is_ws (Z.of_nat n))) (seq 0 33) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ws_of_mask : forall b, 0 <= b <= 32 -> PMR.is_ws b = negb (Z.eqb (bv_unsigned (mtest b)) 0).
Proof.
  intros b Hb. pose proof ws_tab as T. rewrite forallb_forall in T. specialize (T (Z.to_nat b) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in T by lia.
  apply Bool.eqb_prop in T. symmetry. exact T.
Qed.
Lemma ws_mask1 : forall b, 0 <= b <= 32 -> mtest b <> Z_to_bv 64 0 -> PMR.is_ws b = true.
Proof.
  intros b Hb H. rewrite (ws_of_mask b Hb). destruct (Z.eqb_spec (bv_unsigned (mtest b)) 0) as [X|X]; [|reflexivity]. exfalso. apply H. apply bv_eq. rewrite X. reflexivity.
Qed.
Lemma ws_mask0 : forall b, 0 <= b <= 32 -> mtest b = Z_to_bv 64 0 -> PMR.is_ws b = false.
Proof. intros b Hb H. rewrite (ws_of_mask b Hb), H. reflexivity. Qed.
Lemma nws_big : forall b, 33 <= b -> PMR.is_ws b = false.
Proof.
  intros b Hb. unfold PMR.is_ws. destruct (Z.eqb_spec b 32); [lia|]. destruct (Z.eqb_spec b 9); [lia|]. destruct (Z.eqb_spec b 10); [lia|]. destruct (Z.eqb_spec b 13); [lia|]. reflexivity.
Qed.

Section S.
Context {SCFG_P : ScfgP}.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.

Lemma s_pcd_loopw : forall (fx : FPState) R M model K sp1 P E p e b mo,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 80) -> CK.spok sp1 -> pcd_live R P E -> pcd_cur R p e ->
  2 ^ 40 <= P <= 2 ^ 47 -> 0 <= E < 2 ^ 64 -> 2 ^ 12 <= p <= 2 ^ 47 -> 0 <= e < 2 ^ 64 -> 0 <= b <= 255 -> 0 <= mo < 2 ^ 64 ->
  L5.u8_at RSEGS M p b -> L5.u64_at RSEGS M (P + 128) (P + 96) -> L5.u64_at RSEGS M (P + 96) PML.VT_FUNC -> PML.img_ro M -> L5.u8_at RSEGS M (P + 211) mo ->
  L5.defined M (P + 211) 1 -> L5.defined M (sp1 - 80 + 12) 4 -> sp1 <= P -> p + 1 <= sp1 - 80 -> P mod 8 = 0 ->
  (PMR.is_ws b = true -> forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 80) -> pcd_live R' P E -> pcd_cur R' p e -> TK.keepsR KO4 R R' ->
      L5.u8_at RSEGS M' (P + 211) mo -> TK.samem (fun a => ~ (sp1 - 80 + 12 <= a < sp1 - 80 + 16) /\ ~ (P + 211 <= a < P + 212)) M M' -> mem_grows M M' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PT.INC M' model) K) ->
  (PMR.is_ws b = false -> forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 80) -> getr R' 1%bv = Z_to_bv 64 PT.R_SETEC -> getr R' 10%bv = Z_to_bv 64 E -> getr R' 11%bv = Z_to_bv 64 4 ->
      TK.keepsR KO4 R R' -> L5.u8_at RSEGS M' (P + 211) 0 -> TK.samem (fun a => ~ (sp1 - 80 + 12 <= a < sp1 - 80 + 16) /\ ~ (P + 211 <= a < P + 212)) M M' -> mem_grows M M' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_SET_EC M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R PT.LOOP M model) K.
Proof.
  intros fx R M model K sp1 P E p e b mo Hh Hl Hfp H2 [Hsp Hal] (H9 & H8 & H18 & H19 & H20 & H21 & H22) H10 HP HE Hp He Hb Hmo Cb C128 C96 RO C211 D211 DT J1 J2 PAL Kinc Kerr.
  change PT.LOOP with (CC.cp_pc GB.cp0). unfold PT.MASK in H22. unfold pcd_cur in H10.
  pose proof (r18_this sp1 R [b; mo] (fun _ : nat => @nil byte) P H9 H18 ltac:(lia) ltac:(lia)) as X18.
  ck_openX FPM GB.cp0 (GB.plans 0%nat _ eq_refl) (-80) [b; mo] (fun _ : nat => @nil byte) [(19%nat, 32); (20%nat, 4); (21%nat, 1); (22%nat, 4294977024)] [(18%nat, APC.eaddz (EVar 41) 96)] sp1 R M fx model K Hh Hl Hfp H2 ck_pins ltac:(ck_xpins X18).
  - ck_reg E0 (9%bv : reg) H9. ck_reg E0 (10%bv : reg) H10. ck_gh E0 0%nat b. ck_gh E0 1%nat mo.
    unfold know_ok, GB.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_range. + e_range. + ck_kw8 p b Cb. + e_range. + ck_kw64 (P + 128) (P + 96) C128. + unfold PML.VT_FUNC in C96. ck_kw64 (P + 96) 804528 C96. + tk_kimg RO.
    + ck_kw8 (P + 211) mo C211. + e_wr. + e_unk. + e_wr. + e_disj. + e_disj. + e_disj. + e_align PAL.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E0 (9%bv : reg) H9. ck_reg E0 (8%bv : reg) H8. ck_reg E0 (10%bv : reg) H10. ck_gh E0 0%nat b. ck_gh E0 1%nat mo.
    ck_leaf Hag E'.
    assert (FRM : TK.samem (fun a => ~ (sp1 - 80 + 12 <= a < sp1 - 80 + 16) /\ ~ (P + 211 <= a < P + 212)) M M').
    { apply (TK.frame_samem _ _ _ _ _ _ _ HLF). intros a Ha [Hk1 Hk2]. cbn [CC.cp_F]. tk_outside. }
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    assert (ERR : srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_SET_EC M' model) K -> srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_SET_EC M' model) K) by (intros X; exact X).
    assert (GB64 : ev E' 64%nat = Z_to_bv 64 b) by (match goal with U : bv_unsigned (ev E' 64%nat) = b |- _ => exact (RK.w_of_u _ _ U) end).
    ck_leaf_k k Hnth; [|ck_leaf_k k Hnth; [|ck_leaf_k k Hnth; [|ck_leaf_end k Hnth]]]; ck_probes HLF PF.
    + pose proof (CK.lf_cell _ _ _ _ _ _ (KRange (EVar 64) 33 255) HLF ltac:(vm_compute; reflexivity)) as BR. cbn [kentry_ok edenot] in BR. rewrite GB64, u64_of_Z in BR by lia.
      apply (Kerr (nws_big b ltac:(lia)) fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold PT.R_SETEC; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg) | tk_lin HLF (11%bv : reg) | ck_keeps HLF Hag64 KO4 | | exact FRM | exact MG].
      ck_cell8 HLF (EVar 41) 211 (ELit 0). reflexivity.
    + pose proof (CK.lf_cell _ _ _ _ _ _ (KRange (EVar 64) 0 32) HLF ltac:(vm_compute; reflexivity)) as BR. cbn [kentry_ok edenot] in BR. rewrite GB64, u64_of_Z in BR by lia.
      destruct PF as (PF & _). rewrite GB64 in PF.
      apply (Kerr (ws_mask0 b BR PF) fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold PT.R_SETEC; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg) | tk_lin HLF (11%bv : reg) | ck_keeps HLF Hag64 KO4 | | exact FRM | exact MG].
      ck_cell8 HLF (EVar 41) 211 (ELit 0). reflexivity.
    + pose proof (CK.lf_cell _ _ _ _ _ _ (KRange (EVar 64) 0 32) HLF ltac:(vm_compute; reflexivity)) as BR. cbn [kentry_ok edenot] in BR. rewrite GB64, u64_of_Z in BR by lia.
      destruct PF as (PF & _). rewrite GB64 in PF.
      apply (Kinc (ws_mask1 b BR PF) fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | | | ck_keeps HLF Hag64 KO4 | | exact FRM | exact MG].
      * unfold pcd_live, PT.MASK. repeat split; [tk_lin HLF (9%bv : reg) | tk_lin HLF (8%bv : reg) | tk_lin HLF (18%bv : reg) | tk_lin HLF (19%bv : reg) | tk_lin HLF (20%bv : reg) | tk_lin HLF (21%bv : reg) | tk_lin HLF (22%bv : reg)].
      * unfold pcd_cur. tk_lin HLF (10%bv : reg).
      * ck_cell8 HLF (EVar 41) 211 (EVar 65). ck_atom.
Qed.

End S.
End PSW.
