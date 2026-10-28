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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutL5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmTop Require Import TopKit_u5 TopKit2_u5 TopSpecs_u5 ReadKit_u5 ChunkKit_u5 ChunkStretch_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Cut_iosb_xsrc_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module ID.
Module G := Cut_iosb_xsrc_u5.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Definition R_LOC : Z := 0x6facc.  Definition R_F1 : Z := 0x6fad4.  Definition R_F2 : Z := 0x6fadc.  Definition R_F3 : Z := 0x6fae4.
(* [comment removed for export] *)
Definition KALL : list nat := CK.CSR.
Lemma ko_sub : forall q, In q CS.KO -> In q KALL.
Proof. intros q H. unfold CS.KO, KALL, CK.CSR in *. cbn [In] in *. tauto. Qed.
Lemma kall_rp : forall R R', regs_preserved R R' -> TK.keepsR KALL R R'.
Proof. intros R R' RP. apply TK.keepsR_preserved; [exact RP|]. intros q Hq. unfold KALL, CK.CSR in Hq. unfold callee_saved_idx. cbn [In] in *. intuition (subst; cbn; tauto). Qed.

Section S.
Context {SCFG_P : ScfgP}.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.

(* [comment removed for export] *)
Lemma s_id_entry : forall (fx : FPState) R M model K sp1 B rav,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx ->
  getr R 2%bv = Z_to_bv 64 sp1 -> CK.spok sp1 -> getr R 1%bv = Z_to_bv 64 rav -> 0 <= rav < 2 ^ 64 -> getr R 10%bv = Z_to_bv 64 B -> 2 ^ 40 <= B <= 2 ^ 47 ->
  L5.u64_at RSEGS M (B + 48) PML.CLASSIC_IMP -> L5.u64_at RSEGS M (B + 72) 0 -> L5.defined M B 8 -> L5.defined M (sp1 - 48) 48 -> sp1 <= B ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 48) -> getr R' 1%bv = Z_to_bv 64 R_LOC -> getr R' 10%bv = Z_to_bv 64 (B + 48) ->
      getr R' 8%bv = Z_to_bv 64 B -> CS.rc_frame M' sp1 rav R -> TK.keepsR CS.KO R R' -> TK.samem (fun a => ~ (sp1 - 48 <= a < sp1) /\ ~ (B <= a < B + 8)) M M' -> mem_grows M M' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_LOCALE_DTOR M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R PML.PC_IOSB_DTOR M model) K.
Proof.
  intros fx R M model K sp1 B rav Hh Hl Hfp H2 [Hsp Hal] H1 Hrav H10 HB C48 C72 DB DF J1 Hcont.
  change PML.PC_IOSB_DTOR with (CC.cp_pc G.cp0).
  ck_open FPM G.cp0 (G.plans 0%nat _ eq_refl) 0 (@nil Z) (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_reg E (10%bv : reg) H10.
    unfold know_ok, G.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_unk. + e_wr. + e_range.
    + unfold PML.CLASSIC_IMP in C48. ck_kw64 (B + 48) 900688 C48. + ck_kw64 (B + 72) 0 C72. + e_unk. + e_wr. + e_disj.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E (10%bv : reg) H10. ck_reg E (1%bv : reg) H1.
    ck_leaf Hag E'.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (Hcont fx' R' M' Hfp').
    + tk_lin HLF (2%bv : reg). + unfold R_LOC. tk_lin HLF (1%bv : reg). + tk_lin HLF (10%bv : reg). + tk_lin HLF (8%bv : reg).
    + unfold CS.rc_frame. repeat split.
      * ck_cell64 HLF (EVar 2) (-8) (EVar 33). ck_atom.
      * ck_saved HLF Hag64 (-16) 40%nat (8%bv : reg).
      * ck_saved HLF Hag64 (-24) 41%nat (9%bv : reg).
      * ck_saved HLF Hag64 (-32) 50%nat (18%bv : reg).
      * ck_saved HLF Hag64 (-40) 51%nat (19%bv : reg).
    + ck_keeps HLF Hag64 CS.KO.
    + apply (TK.frame_samem _ _ _ _ _ _ _ HLF). intros a Ha [Hk1 Hk2]. cbn [CC.cp_F]. tk_outside.
    + exact (CC.lf_grows _ _ _ _ _ _ _ HLF).
Qed.

(* [comment removed for export] *)
Ltac id_mid cp plans off nxt sp1 B R M fx model K Hh Hl Hfp H2 H8 C Hal Hcont :=
  ck_open FPM cp plans (-48) (@nil Z) (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins;
  [ match goal with E0 := CK.hvB _ _ _ _ |- _ => ck_reg E0 (8%bv : reg) H8 end;
    unfold know_ok; cbn [CC.cp_know]; repeat (apply Forall_cons); [e_range | e_align Hal | e_range | ck_kw64 (B + off) 0 C | apply Forall_nil]
  | let fx' := fresh "fx'" in let E' := fresh "E'" in let R' := fresh "R'" in let M' := fresh "M'" in let k := fresh "k" in let ps := fresh "ps" in
    let Hnth := fresh "Hnth" in let Hag := fresh "Hag" in let HLF := fresh "HLF" in let Hfp' := fresh "Hfp'" in
    intros fx' E' R' M' k ps Hnth Hag HLF Hfp';
    match goal with E0 := CK.hvB _ _ _ _ |- _ => ck_reg E0 (8%bv : reg) H8 end;
    ck_leaf Hag E'; rewrite (TK.frame_nil _ _ _ _ _ _ HLF eq_refl);
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth];
    apply (Hcont fx' R' Hfp'); [tk_lin HLF (2%bv : reg) | unfold nxt; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg) | match goal with Hag64 : env_agree 64 _ _ |- _ => ck_keeps HLF Hag64 KALL end] ].
Lemma s_id_r_loc : forall (fx : FPState) R M model K sp1 B,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 48) -> CK.spok sp1 -> getr R 8%bv = Z_to_bv 64 B -> 2 ^ 40 <= B <= 2 ^ 47 ->
  L5.u64_at RSEGS M (B + 56) 0 ->
  (forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 48) -> getr R' 1%bv = Z_to_bv 64 R_F1 -> getr R' 10%bv = Z_to_bv 64 0 -> TK.keepsR KALL R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_FREE M model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R R_LOC M model) K.
Proof.
  intros fx R M model K sp1 B Hh Hl Hfp H2 [Hsp Hal] H8 HB C Hcont. change R_LOC with (CC.cp_pc G.cp1).
  id_mid G.cp1 (G.plans 1%nat _ eq_refl) 56 R_F1 sp1 B R M fx model K Hh Hl Hfp H2 H8 C Hal Hcont.
Qed.
Lemma s_id_r_f1 : forall (fx : FPState) R M model K sp1 B,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 48) -> CK.spok sp1 -> getr R 8%bv = Z_to_bv 64 B -> 2 ^ 40 <= B <= 2 ^ 47 ->
  L5.u64_at RSEGS M (B + 64) 0 ->
  (forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 48) -> getr R' 1%bv = Z_to_bv 64 R_F2 -> getr R' 10%bv = Z_to_bv 64 0 -> TK.keepsR KALL R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_FREE M model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R R_F1 M model) K.
Proof.
  intros fx R M model K sp1 B Hh Hl Hfp H2 [Hsp Hal] H8 HB C Hcont. change R_F1 with (CC.cp_pc G.cp2).
  id_mid G.cp2 (G.plans 2%nat _ eq_refl) 64 R_F2 sp1 B R M fx model K Hh Hl Hfp H2 H8 C Hal Hcont.
Qed.
Lemma s_id_r_f2 : forall (fx : FPState) R M model K sp1 B,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 48) -> CK.spok sp1 -> getr R 8%bv = Z_to_bv 64 B -> 2 ^ 40 <= B <= 2 ^ 47 ->
  L5.u64_at RSEGS M (B + 88) 0 ->
  (forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 48) -> getr R' 1%bv = Z_to_bv 64 R_F3 -> getr R' 10%bv = Z_to_bv 64 0 -> TK.keepsR KALL R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_FREE M model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R R_F2 M model) K.
Proof.
  intros fx R M model K sp1 B Hh Hl Hfp H2 [Hsp Hal] H8 HB C Hcont. change R_F2 with (CC.cp_pc G.cp3).
  id_mid G.cp3 (G.plans 3%nat _ eq_refl) 88 R_F3 sp1 B R M fx model K Hh Hl Hfp H2 H8 C Hal Hcont.
Qed.

(* [comment removed for export] *)
Lemma s_id_r_f3 : forall (fx : FPState) R M model K sp1 B rav R0,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 48) -> CK.spok sp1 -> getr R 8%bv = Z_to_bv 64 B -> 2 ^ 40 <= B <= 2 ^ 47 ->
  L5.u64_at RSEGS M (B + 112) 0 -> CS.rc_frame M sp1 rav R0 -> 0 <= rav < 2 ^ 64 ->
  (forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 sp1 -> getr R' 1%bv = Z_to_bv 64 rav -> getr R' 10%bv = Z_to_bv 64 0 -> CS.same_s03 R0 R' -> TK.keepsR CS.KO R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_FREE M model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R R_F3 M model) K.
Proof.
  intros fx R M model K sp1 B rav R0 Hh Hl Hfp H2 [Hsp Hal] H8 HB C (F1 & F2 & F3 & F4 & F5) Hrav Hcont. change R_F3 with (CC.cp_pc G.cp4).
  pose proof (fun q : reg => bv_unsigned_in_range _ (getr R0 q)) as RG. change (bv_modulus 64) with (2 ^ 64) in RG.
  pose proof (RG 8%bv) as G8. pose proof (RG 9%bv) as G9. pose proof (RG 18%bv) as G18. pose proof (RG 19%bv) as G19.
  set (gl := [rav; bv_unsigned (getr R0 8%bv); bv_unsigned (getr R0 9%bv); bv_unsigned (getr R0 18%bv); bv_unsigned (getr R0 19%bv)]).
  ck_open FPM G.cp4 (G.plans 4%nat _ eq_refl) (-48) gl (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_reg E (8%bv : reg) H8. ck_gh E 0%nat rav. ck_gh E 1%nat (bv_unsigned (getr R0 8%bv)). ck_gh E 2%nat (bv_unsigned (getr R0 9%bv)). ck_gh E 3%nat (bv_unsigned (getr R0 18%bv)). ck_gh E 4%nat (bv_unsigned (getr R0 19%bv)).
    unfold know_ok, G.cp4. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_range. + ck_kw64 (B + 112) 0 C.
    + ck_kw64 (sp1 - 8) rav F1. + ck_kw64 (sp1 - 16) (bv_unsigned (getr R0 8%bv)) F2. + ck_kw64 (sp1 - 24) (bv_unsigned (getr R0 9%bv)) F3. + ck_kw64 (sp1 - 32) (bv_unsigned (getr R0 18%bv)) F4.
    + ck_kw64 (sp1 - 40) (bv_unsigned (getr R0 19%bv)) F5.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    assert (GH : forall j z, nth_error gl j = Some z -> ev E' (64 + j) = Z_to_bv 64 z).
    { intros j z Hj. assert (Hj8 : (j < 5)%nat) by (change 5%nat with (length gl); apply nth_error_Some; rewrite Hj; discriminate). change (CC.cp_nx G.cp4) with 69%nat in Hag.
      rewrite <- (proj1 Hag (64 + j)%nat) by lia. exact (CK.hvB_gh_w _ _ _ _ j z Hj). }
    ck_leaf Hag E'. rewrite (TK.frame_nil _ _ _ _ _ _ HLF eq_refl).
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (Hcont fx' R' Hfp').
    + tk_lin HLF (2%bv : reg). + tk_reg HLF (1%bv : reg). exact (GH 0%nat _ eq_refl). + tk_lin HLF (10%bv : reg).
    + unfold CS.same_s03. repeat split.
      * tk_reg HLF (8%bv : reg). etransitivity; [exact (GH 1%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      * tk_reg HLF (9%bv : reg). etransitivity; [exact (GH 2%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      * tk_reg HLF (18%bv : reg). etransitivity; [exact (GH 3%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      * tk_reg HLF (19%bv : reg). etransitivity; [exact (GH 4%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
    + ck_keeps HLF Hag64 CS.KO.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Thm.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis LOCDTOR : PMS.locale_dtor_spec L.

Lemma ret_ok_lit : forall z, 0 <= z < 2 ^ 64 -> z mod 2 = 0 -> Hoare.ret_ok (Z_to_bv 64 z).
Proof. intros z Hz He. apply Hoare.ret_ok_even. rewrite u64_of_Z by lia. exact He. Qed.

(* [comment removed for export] *)
Lemma free_null : forall (fx : FPState) R M model K rc, m_halted model = None -> m_vm_lazy model = [] -> K [] ->
  getr R 10%bv = Z_to_bv 64 0 -> getr R 1%bv = Z_to_bv 64 rc -> 0 <= rc < 2 ^ 64 -> rc mod 2 = 0 ->
  (forall R', regs_preserved R R' -> srealizes RSEGS SCFG (@PML.cfg fx R' rc M model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R PML.PC_FREE M model) K.
Proof.
  intros fx R M model K rc Hh Hl HK0 H10 H1 Hrc He Hcont.
  pose proof (hio_free_null L SCFG HI HIok fx R M model K Hh Hl H10 ltac:(rewrite H1; exact (ret_ok_lit rc Hrc He)) HK0) as X.
  rewrite (PmLayout.ly_segs L LAY), (PmLayout.ly_free L LAY), H1 in X. apply X. exact Hcont.
Qed.

Theorem iosb_dtor_ok : TPS.iosb_dtor_spec L.
Proof.
  intros B rd rb sp r fx R M model K Hh Hl HK0 Hfp (EN & A0 & IOSB & OS) Hcont.
  destruct EN as (Hra & Hrok & Hsp & Htp & STK). pose proof STK as (S1 & S2 & S3 & S4 & S5). destruct OS as (O1 & O2 & O3).
  destruct IOSB as (_ & _ & _ & C48 & CK0 & DB). unfold TPS.IOSB_SCR in *. unfold PML.a0 in A0.
  assert (SPOK : CK.spok sp) by (split; [lia | exact S1]).
  assert (Hrav : 0 <= r < 2 ^ 64) by (destruct Hrok; lia).
  pose proof (CK0 0 ltac:(lia)) as C56. pose proof (CK0 1 ltac:(lia)) as C64. pose proof (CK0 2 ltac:(lia)) as C72. pose proof (CK0 4 ltac:(lia)) as C88. pose proof (CK0 7 ltac:(lia)) as C112.
  replace (B + 56 + 8 * 0) with (B + 56) in C56 by lia. replace (B + 56 + 8 * 1) with (B + 64) in C64 by lia. replace (B + 56 + 8 * 2) with (B + 72) in C72 by lia.
  replace (B + 56 + 8 * 4) with (B + 88) in C88 by lia. replace (B + 56 + 8 * 7) with (B + 112) in C112 by lia.
  apply (s_id_entry fx R M model K sp B r Hh Hl Hfp Hsp SPOK Hra Hrav A0 ltac:(lia) C48 C72 ltac:(eapply L5.defined_sub; [exact DB | lia | lia]) ltac:(eapply L5.defined_sub; [exact S5 | lia | lia]) O1).
  intros fx1 R1 M1 Hfp1 H2a H1a H10a H8a FR1 KO1 AG1 MG1.
  assert (TP1 : getr R1 4%bv = Z_to_bv 64 PML.TP) by (rewrite (KO1 4%bv ltac:(ck_in)); exact Htp).
  assert (CELL : forall off, 48 <= off -> off + 8 <= 152 -> forall v, L5.u64_at RSEGS M (B + off) v -> L5.u64_at RSEGS M1 (B + off) v).
  { intros off H1 H2 v C. apply (TK.u64_samem _ M M1 _ _ AG1); [lia | intros i Hi; cbn beta; lia | exact C]. }
  apply (LOCDTOR (B + 48) (sp - 48) R_LOC fx1 R1 M1 model K Hh Hl HK0 Hfp1).
  { split; [apply (CK.mk_entry L R1 M1 (sp - 48) _ _ H1a ltac:(unfold R_LOC; split; [lia | reflexivity]) H2a TP1); apply (CK.sub_stk _ M M1 sp 64 _ _ STK MG1); [apply CK.al16; [exact S1 | reflexivity] | lia | lia | lia]|].
    split; [exact H10a|]. split; [lia|]. apply CELL; [lia | lia | exact C48]. }
  intros fx2 R2 M2 Hfp2 _ RP2 FB2 MG2.
  assert (EQ2 : M2 = M1).
  { apply FunctionalExtensionality.functional_extensionality. intros x. apply FB2. intros w [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. lia. }
  subst M2.
  apply (s_id_r_loc fx2 R2 M1 model K sp B Hh Hl Hfp2 ltac:(rewrite (CS.sp_rp _ _ RP2); exact H2a) SPOK ltac:(rewrite (RP2 8%bv ltac:(ck_in)); exact H8a) ltac:(lia) ltac:(apply CELL; [lia | lia | exact C56])).
  intros fx3 R3 Hfp3 H2c H1c H10c K3.
  apply (free_null fx3 R3 M1 model K R_F1 Hh Hl HK0 H10c H1c ltac:(unfold R_F1; lia) eq_refl). intros R4 RP4.
  assert (K24 : TK.keepsR KALL R2 R4) by (apply (TK.keepsR_trans _ _ _ _ K3); exact (kall_rp _ _ RP4)).
  apply (s_id_r_f1 fx3 R4 M1 model K sp B Hh Hl Hfp3 ltac:(rewrite (CS.sp_rp _ _ RP4); exact H2c) SPOK ltac:(rewrite (K24 8%bv ltac:(ck_in)), (RP2 8%bv ltac:(ck_in)); exact H8a) ltac:(lia) ltac:(apply CELL; [lia | lia | exact C64])).
  intros fx5 R5 Hfp5 H2e H1e H10e K5.
  apply (free_null fx5 R5 M1 model K R_F2 Hh Hl HK0 H10e H1e ltac:(unfold R_F2; lia) eq_refl). intros R6 RP6.
  assert (K26 : TK.keepsR KALL R2 R6) by (apply (TK.keepsR_trans _ _ _ _ (TK.keepsR_trans _ _ _ _ K24 K5)); exact (kall_rp _ _ RP6)).
  apply (s_id_r_f2 fx5 R6 M1 model K sp B Hh Hl Hfp5 ltac:(rewrite (CS.sp_rp _ _ RP6); exact H2e) SPOK ltac:(rewrite (K26 8%bv ltac:(ck_in)), (RP2 8%bv ltac:(ck_in)); exact H8a) ltac:(lia) ltac:(apply CELL; [lia | lia | exact C88])).
  intros fx7 R7 Hfp7 H2g H1g H10g K7.
  apply (free_null fx7 R7 M1 model K R_F3 Hh Hl HK0 H10g H1g ltac:(unfold R_F3; lia) eq_refl). intros R8 RP8.
  assert (K28 : TK.keepsR KALL R2 R8) by (apply (TK.keepsR_trans _ _ _ _ (TK.keepsR_trans _ _ _ _ K26 K7)); exact (kall_rp _ _ RP8)).
  apply (s_id_r_f3 fx7 R8 M1 model K sp B r R Hh Hl Hfp7 ltac:(rewrite (CS.sp_rp _ _ RP8); exact H2g) SPOK ltac:(rewrite (K28 8%bv ltac:(ck_in)), (RP2 8%bv ltac:(ck_in)); exact H8a) ltac:(lia) ltac:(apply CELL; [lia | lia | exact C112]) FR1 Hrav).
  intros fx9 R9 Hfp9 H2i H1i H10i SS9 KO9.
  apply (free_null fx9 R9 M1 model K r Hh Hl HK0 H10i H1i Hrav ltac:(destruct Hrok; assumption)). intros R10 RP10.
  apply (Hcont fx9 R10 M1 Hfp9 I).
  - assert (KO29 : TK.keepsR CS.KO R2 R9).
    { apply (TK.keepsR_trans _ _ _ _ (CK.keepsR_sub _ _ _ _ K28 ko_sub) KO9). }
    assert (RP09 : regs_preserved R R9).
    { apply CS.rp_final; [rewrite H2i, Hsp; reflexivity | exact SS9 |]. apply (TK.keepsR_trans _ _ _ _ (TK.keepsR_trans _ _ _ _ KO1 (CS.ko_rp _ _ RP2)) KO29). }
    intros q Hq. rewrite (RP10 q Hq). exact (RP09 q Hq).
  - apply (CK.samem_frame_but _ _ M M1 AG1). intros a Ha. pose proof (Ha (sp - 64, 64) ltac:(ck_in)) as X1. pose proof (Ha (B, 8) ltac:(ck_in)) as X2. unfold L5.in_rng in *. cbn [fst snd] in *. lia.
  - exact MG1.
Qed.
End Thm.
End S.
End ID.
