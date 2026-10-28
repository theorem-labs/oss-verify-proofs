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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmTop Require Import TopKit_u5 TopKit2_u5 TopSpecs_u5 ReadKit_u5 ChunkKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Cut_sdtor_xsrc_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Module SDT.
Definition R1 : Z := 0x3ae70.      Definition R2 : Z := 0x3aea8.      Definition R3 : Z := 0x3aebc.
Definition FRAME : Z := 32.
End SDT.

Module SDS.
Module G := Cut_sdtor_xsrc_u5.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).

(* [comment removed for export] *)
Definition KO3 : list nat := [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Definition SV : list nat := [8; 9; 18]%nat.
Definition sd_live (R : bvmap 5 word) (Rr : Z) : Prop := getr R 8%bv = Z_to_bv 64 Rr /\ getr R 9%bv = Z_to_bv 64 (Rr + 8) /\ getr R 18%bv = Z_to_bv 64 (Rr + 88).
Definition same_s02 (R0 R' : bvmap 5 word) : Prop := getr R' 8%bv = getr R0 8%bv /\ getr R' 9%bv = getr R0 9%bv /\ getr R' 18%bv = getr R0 18%bv.
Definition sd_frame (M : mem) (sp1 rav : Z) (R0 : bvmap 5 word) : Prop :=
  L5.u64_at RSEGS M (sp1 - 8) rav /\ L5.u64_at RSEGS M (sp1 - 16) (bv_unsigned (getr R0 8%bv)) /\ L5.u64_at RSEGS M (sp1 - 24) (bv_unsigned (getr R0 9%bv)) /\
  L5.u64_at RSEGS M (sp1 - 32) (bv_unsigned (getr R0 18%bv)).
Lemma sd_frame_x : forall (K : Z -> Prop) (M M' : mem) sp1 rav R0, TK.samem K M M' -> 2 ^ 40 <= sp1 <= 2 ^ 47 -> (forall i, sp1 - 32 <= i < sp1 -> K i) -> sd_frame M sp1 rav R0 -> sd_frame M' sp1 rav R0.
Proof. intros K M M' sp1 rav R0 AG Hsp HK (F1 & F2 & F3 & F4). repeat split; (eapply (TK.u64_samem K M M'); [exact AG | lia | intros i Hi; apply HK; lia | assumption]). Qed.
Lemma sv_rp : forall R R', regs_preserved R R' -> forall q : reg, In (ridx q) SV -> getr R' q = getr R q.
Proof. intros R R' RP. apply (TK.keepsR_preserved SV R R' RP). intros q Hq. unfold SV in Hq. unfold callee_saved_idx. cbn [In] in *. intuition (subst; cbn; tauto). Qed.
Lemma sd_live_keep : forall R R' Rr, (forall q : reg, In (ridx q) SV -> getr R' q = getr R q) -> sd_live R Rr -> sd_live R' Rr.
Proof. intros R R' Rr HK (H8 & H9 & H18). unfold sd_live. rewrite (HK 8%bv ltac:(ck_in)), (HK 9%bv ltac:(ck_in)), (HK 18%bv ltac:(ck_in)). repeat split; assumption. Qed.
Lemma rp_final : forall R0 R' : bvmap 5 word, getr R' 2%bv = getr R0 2%bv -> same_s02 R0 R' -> TK.keepsR KO3 R0 R' -> regs_preserved R0 R'.
Proof.
  intros R0 R' H2 (Q8 & Q9 & Q18) HK. apply CK.rp_of_keeps; [exact H2|]. intros q Hq. unfold CK.CSR in Hq. cbn [In] in Hq.
  assert (QQ : forall m : nat, m = ridx q -> q = Z_to_bv 5 (Z.of_nat m)) by (intros m ->; symmetry; apply ridx_roundtrip).
  assert (HK' : In (ridx q) KO3 -> getr R' q = getr R0 q) by (apply HK). unfold KO3 in HK'. cbn [In] in HK'.
  destruct Hq as [Hq|[Hq|[Hq|[Hq|[Hq|Hq]]]]]; [apply HK'; tauto | apply HK'; tauto | rewrite (QQ _ Hq); exact Q8 | rewrite (QQ _ Hq); exact Q9 | rewrite (QQ _ Hq); exact Q18 | apply HK'; tauto].
Qed.
Lemma ko3_rp : forall R R', regs_preserved R R' -> TK.keepsR KO3 R R'.
Proof. intros R R' RP. apply TK.keepsR_preserved; [exact RP|]. intros q Hq. unfold KO3 in Hq. unfold callee_saved_idx. cbn [In] in *. intuition (subst; cbn; tauto). Qed.
Lemma sp_rp : forall (R R' : bvmap 5 word), regs_preserved R R' -> getr R' 2%bv = getr R 2%bv.
Proof. intros R R' RP. apply RP. ck_in. Qed.

Section S.
Context {SCFG_P : ScfgP}.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.

(* [comment removed for export] *)
Definition KV (Rr : Z) (a : Z) : Prop := ~ (Rr + 8 <= a < Rr + 16) /\ ~ (Rr + 24 <= a < Rr + 32) /\ ~ (Rr + 88 <= a < Rr + 96).

(* [comment removed for export] *)
Lemma s_sd_entry : forall (fx : FPState) R M model K sp1 Rr ch csz rav,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx ->
  getr R 2%bv = Z_to_bv 64 sp1 -> CK.spok sp1 -> getr R 1%bv = Z_to_bv 64 rav -> L5.ra_ok rav -> getr R 10%bv = Z_to_bv 64 Rr ->
  2 ^ 40 <= Rr <= 2 ^ 47 - 592 -> 4096 <= ch <= 2 ^ 47 -> 0 <= csz < 2 ^ 64 ->
  L5.u64_at RSEGS M (Rr + 264) ch -> L5.u64_at RSEGS M (Rr + 272) csz -> L5.defined M (sp1 - 32) 32 -> sp1 <= Rr ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 32) -> getr R' 1%bv = Z_to_bv 64 SDT.R1 -> getr R' 10%bv = Z_to_bv 64 ch -> getr R' 8%bv = Z_to_bv 64 Rr ->
      sd_frame M' sp1 rav R -> TK.keepsR KO3 R R' -> TK.samem (fun a => ~ (sp1 - 32 <= a < sp1)) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_OPDEL_SIZED M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R PML.PC_SOURCE_DTOR M model) K.
Proof.
  intros fx R M model K sp1 Rr ch csz rav Hh Hl Hfp H2 [Hsp Hal] H1 Hra H10 HR Hch Hcsz C264 C272 DF J1 Kdel.
  change PML.PC_SOURCE_DTOR with (CC.cp_pc G.cp0).
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  ck_open FPM G.cp0 (G.plans 0%nat _ eq_refl) 0 [ch; csz] (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_reg E (10%bv : reg) H10. ck_gh E 0%nat ch. ck_gh E 1%nat csz.
    unfold know_ok, G.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_unk. + e_wr. + e_range. + ck_kw64 (Rr + 264) ch C264. + e_range. + ck_kw64 (Rr + 272) csz C272. + e_disj.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E (10%bv : reg) H10. ck_reg E (1%bv : reg) H1. ck_gh E 0%nat ch.
    ck_leaf Hag E'.
    assert (FRM : TK.samem (fun a => ~ (sp1 - 32 <= a < sp1)) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha Hk1; cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (Kdel fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold SDT.R1; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg) | tk_lin HLF (8%bv : reg) | | ck_keeps HLF Hag64 KO3 | exact FRM | exact MG].
    unfold sd_frame. repeat split; [ck_cell64 HLF (EVar 2) (-8) (EVar 33); ck_atom | ck_saved HLF Hag64 (-16) 40%nat (8%bv : reg) | ck_saved HLF Hag64 (-24) 41%nat (9%bv : reg) | ck_saved HLF Hag64 (-32) 50%nat (18%bv : reg)].
Qed.

(* [comment removed for export] *)
Lemma s_sd_r1 : forall (fx : FPState) R M model K sp1 Rr,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 32) -> CK.spok sp1 -> getr R 8%bv = Z_to_bv 64 Rr ->
  2 ^ 40 <= Rr <= 2 ^ 47 - 592 -> PML.img_ro M -> L5.defined M Rr 96 ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 32) -> getr R' 1%bv = Z_to_bv 64 SDT.R2 -> getr R' 10%bv = Z_to_bv 64 (Rr + 32) -> sd_live R' Rr ->
      TK.keepsR KO3 R R' -> TK.samem (KV Rr) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_LOCALE_DTOR M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R SDT.R1 M model) K.
Proof.
  intros fx R M model K sp1 Rr Hh Hl Hfp H2 [Hsp Hal] H8 HR RO DR Kloc.
  change SDT.R1 with (CC.cp_pc G.cp1).
  ck_open FPM G.cp1 (G.plans 1%nat _ eq_refl) (-32) (@nil Z) (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_reg E (8%bv : reg) H8.
    unfold know_ok, G.cp1. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_range. + tk_kimg RO. + e_unk. + e_wr. + e_unk. + e_wr. + e_unk. + e_wr.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E (8%bv : reg) H8.
    ck_leaf Hag E'.
    assert (FRM : TK.samem (KV Rr) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha (Hk1 & Hk2 & Hk3); cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (Kloc fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold SDT.R2; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg) | | ck_keeps HLF Hag64 KO3 | exact FRM | exact MG].
    unfold sd_live. repeat split; [tk_lin HLF (8%bv : reg) | tk_lin HLF (9%bv : reg) | tk_lin HLF (18%bv : reg)].
Qed.

(* [comment removed for export] *)
Lemma s_sd_r2 : forall (fx : FPState) R M model K sp1 Rr,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 32) -> CK.spok sp1 -> sd_live R Rr -> 2 ^ 40 <= Rr <= 2 ^ 47 - 592 ->
  (forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 32) -> getr R' 1%bv = Z_to_bv 64 SDT.R3 -> sd_live R' Rr -> TK.keepsR KO3 R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_ISTREAM_DTOR M model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R SDT.R2 M model) K.
Proof.
  intros fx R M model K sp1 Rr Hh Hl Hfp H2 [Hsp Hal] (H8 & H9 & H18) HR Kis.
  change SDT.R2 with (CC.cp_pc G.cp2).
  ck_open FPM G.cp2 (G.plans 2%nat _ eq_refl) (-32) (@nil Z) (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - unfold know_ok, G.cp2. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_leaf Hag E'. pose proof (TK.frame_nil _ _ _ _ _ _ HLF eq_refl) as EQ. subst M'.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (Kis fx' R' Hfp'); [tk_lin HLF (2%bv : reg) | unfold SDT.R3; tk_lin HLF (1%bv : reg) | | ck_keeps HLF Hag64 KO3].
    apply (sd_live_keep R R' Rr); [|repeat split; assumption]. ck_keeps HLF Hag64 SV.
Qed.

(* [comment removed for export] *)
Lemma s_sd_r3 : forall (fx : FPState) R M model K sp1 Rr rav R0,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 32) -> CK.spok sp1 -> sd_live R Rr -> 2 ^ 40 <= Rr <= 2 ^ 47 - 592 ->
  sd_frame M sp1 rav R0 -> L5.ra_ok rav ->
  (forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 sp1 -> getr R' 1%bv = Z_to_bv 64 rav -> getr R' 10%bv = Z_to_bv 64 (Rr + 88) -> same_s02 R0 R' -> TK.keepsR KO3 R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_IOSB_DTOR M model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R SDT.R3 M model) K.
Proof.
  intros fx R M model K sp1 Rr rav R0 Hh Hl Hfp H2 [Hsp Hal] (H8 & H9 & H18) HR (F1 & F2 & F3 & F4) Hra Kio.
  change SDT.R3 with (CC.cp_pc G.cp3).
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  pose proof (fun q : reg => bv_unsigned_in_range _ (getr R0 q)) as RG. change (bv_modulus 64) with (2 ^ 64) in RG.
  pose proof (RG 8%bv) as G8. pose proof (RG 9%bv) as G9. pose proof (RG 18%bv) as G18.
  set (gl := [rav; bv_unsigned (getr R0 8%bv); bv_unsigned (getr R0 9%bv); bv_unsigned (getr R0 18%bv)]).
  ck_open FPM G.cp3 (G.plans 3%nat _ eq_refl) (-32) gl (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_gh E 0%nat rav. ck_gh E 1%nat (bv_unsigned (getr R0 8%bv)). ck_gh E 2%nat (bv_unsigned (getr R0 9%bv)). ck_gh E 3%nat (bv_unsigned (getr R0 18%bv)).
    unfold know_ok, G.cp3. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + ck_kw64 (sp1 - 8) rav F1. + ck_kw64 (sp1 - 16) (bv_unsigned (getr R0 8%bv)) F2. + ck_kw64 (sp1 - 24) (bv_unsigned (getr R0 9%bv)) F3.
    + ck_kw64 (sp1 - 32) (bv_unsigned (getr R0 18%bv)) F4.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E (18%bv : reg) H18.
    assert (GH : forall j z, nth_error gl j = Some z -> ev E' (64 + j) = Z_to_bv 64 z).
    { intros j z Hj. assert (Hj8 : (j < 4)%nat) by (change 4%nat with (length gl); apply nth_error_Some; rewrite Hj; discriminate). change (CC.cp_nx G.cp3) with 68%nat in Hag.
      rewrite <- (proj1 Hag (64 + j)%nat) by lia. exact (CK.hvB_gh_w _ _ _ _ j z Hj). }
    ck_leaf Hag E'. pose proof (TK.frame_nil _ _ _ _ _ _ HLF eq_refl) as EQ. subst M'.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (Kio fx' R' Hfp'); [tk_lin HLF (2%bv : reg) | tk_reg HLF (1%bv : reg); exact (GH 0%nat _ eq_refl) | tk_lin HLF (10%bv : reg) | | ck_keeps HLF Hag64 KO3].
    unfold same_s02. repeat split.
    + tk_reg HLF (8%bv : reg). etransitivity; [exact (GH 1%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
    + tk_reg HLF (9%bv : reg). etransitivity; [exact (GH 2%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
    + tk_reg HLF (18%bv : reg). etransitivity; [exact (GH 3%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
Qed.
End S.
End SDS.
