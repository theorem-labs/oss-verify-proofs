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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Cut_pdtor_xsrc_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Module PDT.
Definition R1 : Z := 0x3acd4.      Definition LONG2 : Z := 0x3ace0.      Definition R2 : Z := 0x3acf0.      Definition RET : Z := 0x3ad84.
Definition FRAME : Z := 32.
End PDT.

Module PDS.
Module G := Cut_pdtor_xsrc_u5.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Lemma ret_pd : CL.is_ret_at RSEGS PDT.RET. Proof. CL.solve_is_ret. Qed.

(* [comment removed for export] *)
Definition KO1 : list nat := [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Definition pd_frame (M : mem) (sp1 rav : Z) (R0 : bvmap 5 word) (P : Z) : Prop :=
  L5.u64_at RSEGS M (sp1 - 8) rav /\ L5.u64_at RSEGS M (sp1 - 16) (bv_unsigned (getr R0 8%bv)) /\ L5.u64_at RSEGS M (sp1 - 24) (P + 248).
Lemma pd_frame_x : forall (K : Z -> Prop) (M M' : mem) sp1 rav R0 P, TK.samem K M M' -> 2 ^ 40 <= sp1 <= 2 ^ 47 -> (forall i, sp1 - 24 <= i < sp1 -> K i) -> pd_frame M sp1 rav R0 P -> pd_frame M' sp1 rav R0 P.
Proof. intros K M M' sp1 rav R0 P AG Hsp HK (F1 & F2 & F3). split; [|split]; (eapply (TK.u64_samem K M M'); [exact AG | lia | intros i Hi; apply HK; lia | assumption]). Qed.
Lemma rp_final : forall R0 R' : bvmap 5 word, getr R' 2%bv = getr R0 2%bv -> getr R' 8%bv = getr R0 8%bv -> TK.keepsR KO1 R0 R' -> regs_preserved R0 R'.
Proof.
  intros R0 R' H2 H8 HK. apply CK.rp_of_keeps; [exact H2|]. intros q Hq. unfold CK.CSR in Hq. cbn [In] in Hq.
  assert (QQ : forall m : nat, m = ridx q -> q = Z_to_bv 5 (Z.of_nat m)) by (intros m ->; symmetry; apply ridx_roundtrip).
  assert (HK' : In (ridx q) KO1 -> getr R' q = getr R0 q) by (apply HK). unfold KO1 in HK'. cbn [In] in HK'.
  destruct Hq as [Hq|[Hq|[Hq|Hq]]]; [apply HK'; tauto | apply HK'; tauto | rewrite (QQ _ Hq); exact H8 | apply HK'; tauto].
Qed.
Lemma ko1_rp : forall R R', regs_preserved R R' -> TK.keepsR KO1 R R'.
Proof. intros R R' RP. apply TK.keepsR_preserved; [exact RP|]. intros q Hq. unfold KO1 in Hq. unfold callee_saved_idx. cbn [In] in *. intuition (subst; cbn; tauto). Qed.
Lemma s0_rp : forall (R R' : bvmap 5 word), regs_preserved R R' -> getr R' 8%bv = getr R 8%bv.
Proof. intros R R' RP. apply RP. ck_in. Qed.
Lemma sp_rp : forall (R R' : bvmap 5 word), regs_preserved R R' -> getr R' 2%bv = getr R 2%bv.
Proof. intros R R' RP. apply RP. ck_in. Qed.

Section S.
Context {SCFG_P : ScfgP}.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.

(* [comment removed for export] *)
Definition KE (sp1 P : Z) (a : Z) : Prop := ~ (sp1 - 32 <= a < sp1) /\ ~ (P <= a < P + 8) /\ ~ (P + 256 <= a < P + 264).

(* [comment removed for export] *)
Lemma s_pd_entry : forall (fx : FPState) R M model K sp1 P sb se n rav,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx ->
  getr R 2%bv = Z_to_bv 64 sp1 -> CK.spok sp1 -> getr R 1%bv = Z_to_bv 64 rav -> L5.ra_ok rav -> getr R 10%bv = Z_to_bv 64 P ->
  2 ^ 40 <= P <= 2 ^ 47 - 272 -> 4096 <= sb <= 2 ^ 47 -> 0 <= se < 2 ^ 64 ->
  L5.u64_at RSEGS M (P + 248) sb -> L5.u64_at RSEGS M (P + 256) (sb + n) -> L5.u64_at RSEGS M (P + 264) se -> 0 <= n <= 4096 -> P mod 8 = 0 ->
  L5.defined M (sp1 - 32) 32 -> L5.defined M P 272 -> sp1 <= P ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 32) -> getr R' 1%bv = Z_to_bv 64 PDT.R1 -> getr R' 10%bv = Z_to_bv 64 sb -> getr R' 8%bv = Z_to_bv 64 P ->
      pd_frame M' sp1 rav R P -> TK.keepsR KO1 R R' -> TK.samem (KE sp1 P) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_OPDEL_SIZED M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R PML.PC_PARSER_DTOR M model) K.
Proof.
  intros fx R M model K sp1 P sb se n rav Hh Hl Hfp H2 [Hsp Hal] H1 Hra H10 HP Hsb Hse C248 C256 C264 Hn HP8 DF DP J1 Kdel.
  change PML.PC_PARSER_DTOR with (CC.cp_pc G.cp0).
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  ck_open FPM G.cp0 (G.plans 0%nat _ eq_refl) 0 [sb; se; n] (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_reg E (10%bv : reg) H10. ck_gh E 0%nat sb. ck_gh E 1%nat se. ck_gh E 2%nat n.
    unfold know_ok, G.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_unk. + e_wr. + e_range. + ck_kw64 (P + 248) sb C248. + e_range. + ck_kw64 (P + 264) se C264. + e_unk. + e_wr.
    + ck_kw64 (P + 256) (sb + n) C256. + e_wr. + e_disj. + e_align HP8. + e_range.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E (10%bv : reg) H10. ck_reg E (1%bv : reg) H1. ck_gh E 0%nat sb. ck_gh E 1%nat se.
    ck_leaf Hag E'.
    assert (FRM : TK.samem (KE sp1 P) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha (Hk1 & Hk2 & Hk3); cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    ck_leaf_k k Hnth; [|ck_leaf_k k Hnth; [|ck_leaf_end k Hnth]];
    (apply (Kdel fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold PDT.R1; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg) | tk_lin HLF (8%bv : reg) | | ck_keeps HLF Hag64 KO1 | exact FRM | exact MG];
     split; [ck_cell64 HLF (EVar 2) (-8) (EVar 33); ck_atom | split; [ck_saved HLF Hag64 (-16) 40%nat (8%bv : reg) | ck_cell64 HLF (EVar 2) (-24) (EAlu ALU_ADD (EVar 42) (ELit 248)); ck_vlin]]).
Qed.

(* [comment removed for export] *)
Lemma s_pd_r1 : forall (fx : FPState) R M model K sp1 P b,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 32) -> CK.spok sp1 -> getr R 8%bv = Z_to_bv 64 P ->
  2 ^ 40 <= P <= 2 ^ 47 - 272 -> 0 <= b <= 255 -> Z.land b 1 = 1 -> L5.u8_at RSEGS M (P + 224) b ->
  (forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 32) -> getr R' 8%bv = Z_to_bv 64 P -> TK.keepsR KO1 R R' -> srealizes RSEGS SCFG (@PML.cfg fx' R' PDT.LONG2 M model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R PDT.R1 M model) K.
Proof.
  intros fx R M model K sp1 P b Hh Hl Hfp H2 [Hsp Hal] H8 HP Hb Hodd Cb Klong.
  change PDT.R1 with (CC.cp_pc G.cp1).
  ck_open FPM G.cp1 (G.plans 1%nat _ eq_refl) (-32) [b] (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_reg E (8%bv : reg) H8. ck_gh E 0%nat b.
    unfold know_ok, G.cp1. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_range. + ck_kw8 (P + 224) b Cb. + e_range.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E (8%bv : reg) H8. ck_gh E 0%nat b.
    ck_leaf Hag E'. pose proof (TK.frame_nil _ _ _ _ _ _ HLF eq_refl) as EQ. subst M'.
    (ck_leaf_k k Hnth; [|ck_leaf_k k Hnth; [|ck_leaf_end k Hnth]]); ck_probes HLF PF.
    + exfalso. destruct PF as (PF & _). ck_w2z PF. rewrite RK.and_lit in PF by lia. apply RK.w_inj in PF; [lia | | lia].
      rewrite Hodd. lia.
    + apply (Klong fx' R' Hfp'); [tk_lin HLF (2%bv : reg) | tk_lin HLF (8%bv : reg) | ck_keeps HLF Hag64 KO1].
Qed.

(* [comment removed for export] *)
Lemma s_pd_long2 : forall (fx : FPState) R M model K sp1 P w0 bptr,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 32) -> CK.spok sp1 -> getr R 8%bv = Z_to_bv 64 P ->
  2 ^ 40 <= P <= 2 ^ 47 - 272 -> 0 <= w0 < 2 ^ 64 -> 0 <= bptr < 2 ^ 64 -> L5.u64_at RSEGS M (P + 224) w0 -> L5.u64_at RSEGS M (P + 240) bptr ->
  (forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 32) -> getr R' 1%bv = Z_to_bv 64 PDT.R2 -> getr R' 10%bv = Z_to_bv 64 bptr -> getr R' 8%bv = Z_to_bv 64 P ->
      TK.keepsR KO1 R R' -> srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_OPDEL_SIZED M model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R PDT.LONG2 M model) K.
Proof.
  intros fx R M model K sp1 P w0 bptr Hh Hl Hfp H2 [Hsp Hal] H8 HP Hw0 Hbp C224 C240 Kdel.
  change PDT.LONG2 with (CC.cp_pc G.cp2).
  ck_open FPM G.cp2 (G.plans 2%nat _ eq_refl) (-32) [w0; bptr] (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_reg E (8%bv : reg) H8. ck_gh E 0%nat w0. ck_gh E 1%nat bptr.
    unfold know_ok, G.cp2. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_range. + ck_kw64 (P + 224) w0 C224. + ck_kw64 (P + 240) bptr C240.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E (8%bv : reg) H8. ck_gh E 0%nat w0. ck_gh E 1%nat bptr.
    ck_leaf Hag E'. pose proof (TK.frame_nil _ _ _ _ _ _ HLF eq_refl) as EQ. subst M'.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (Kdel fx' R' Hfp'); [tk_lin HLF (2%bv : reg) | unfold PDT.R2; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg) | tk_lin HLF (8%bv : reg) | ck_keeps HLF Hag64 KO1].
Qed.

(* [comment removed for export] *)
Lemma s_pd_r2 : forall (fx : FPState) R M model K sp1 P rav R0,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 32) -> CK.spok sp1 -> getr R 8%bv = Z_to_bv 64 P ->
  2 ^ 40 <= P <= 2 ^ 47 - 272 -> L5.u64_at RSEGS M (P + 128) (P + 96) -> L5.u64_at RSEGS M (P + 96) PML.VT_FUNC -> PML.img_ro M ->
  L5.u8_at RSEGS M (P + 72) 0 -> L5.u8_at RSEGS M (P + 48) 0 -> L5.u8_at RSEGS M (P + 24) 0 -> pd_frame M sp1 rav R0 P -> L5.ra_ok rav ->
  (forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 sp1 -> getr R' 8%bv = getr R0 8%bv -> TK.keepsR KO1 R R' -> srealizes RSEGS SCFG (@PML.cfg fx' R' rav M model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R PDT.R2 M model) K.
Proof.
  intros fx R M model K sp1 P rav R0 Hh Hl Hfp H2 [Hsp Hal] H8 HP C128 C96 RO C72 C48 C24 (F1 & F2 & F3) Hra Kret.
  change PDT.R2 with (CC.cp_pc G.cp3).
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  pose proof (bv_unsigned_in_range _ (getr R0 8%bv)) as G8. change (bv_modulus 64) with (2 ^ 64) in G8.
  set (gl := [rav; bv_unsigned (getr R0 8%bv); P + 248]).
  ck_open FPM G.cp3 (G.plans 3%nat _ eq_refl) (-32) gl (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_reg E (8%bv : reg) H8. ck_gh E 0%nat rav. ck_gh E 1%nat (bv_unsigned (getr R0 8%bv)). ck_gh E 2%nat (P + 248).
    unfold know_ok, G.cp3. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + ck_kw64 (sp1 - 8) rav F1. + ck_kw64 (sp1 - 16) (bv_unsigned (getr R0 8%bv)) F2. + ck_kw64 (sp1 - 24) (P + 248) F3. + e_range.
    + ck_kw64 (P + 128) (P + 96) C128. + unfold PML.VT_FUNC in C96. ck_kw64 (P + 96) 804528 C96. + tk_kimg RO.
    + ck_kw8 (P + 72) 0 C72. + ck_kw8 (P + 48) 0 C48. + ck_kw8 (P + 24) 0 C24.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    assert (GH : forall j z, nth_error gl j = Some z -> ev E' (64 + j) = Z_to_bv 64 z).
    { intros j z Hj. assert (Hj8 : (j < 3)%nat) by (change 3%nat with (length gl); apply nth_error_Some; rewrite Hj; discriminate). change (CC.cp_nx G.cp3) with 67%nat in Hag.
      rewrite <- (proj1 Hag (64 + j)%nat) by lia. exact (CK.hvB_gh_w _ _ _ _ j z Hj). }
    ck_leaf Hag E'. pose proof (TK.frame_nil _ _ _ _ _ _ HLF eq_refl) as EQ. subst M'.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    assert (R1 : getr R' 1%bv = Z_to_bv 64 rav) by (tk_reg HLF (1%bv : reg); exact (GH 0%nat _ eq_refl)).
    apply (CK.ret_leaf fx' R' _ M model K rav ret_pd Hh Hl R1 Hra).
    apply (Kret fx' R' Hfp'); [tk_lin HLF (2%bv : reg) | | ck_keeps HLF Hag64 KO1].
    tk_reg HLF (8%bv : reg). etransitivity; [exact (GH 1%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
Qed.
End S.
End PDS.
