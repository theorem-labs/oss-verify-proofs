(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutL5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmTop Require Import TopKit_u5 TopKit2_u5 TopSpecs_u5 ReadKit_u5 ReadBase_u5 ChunkKit_u5 TopKitX_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Cut_enc_dtor_xsrc_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module EDX.
Module G := Cut_enc_dtor_xsrc_u5.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Definition BR : Z := 0x3e6e0.      Definition JOIN : Z := 0x3abe4.      Definition RET : Z := 0x3ac08.      Definition LOOP : Z := 0x3e6f0.
Definition VT_OPTS_D : Z := 803360.   (* [comment removed for export] *)
Definition VT_COMMON_D : Z := 803504. (* [comment removed for export] *)
Lemma ret_ed : CL.is_ret_at RSEGS RET. Proof. CL.solve_is_ret. Qed.
Lemma ra_ok_lit : forall z, (0 <=? z) && (z <? 2 ^ 47) && (z mod 2 =? 0) = true -> L5.ra_ok z.
Proof. intros z H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.eqb_eq in H3. split; [lia | exact H3]. Qed.

(* [comment removed for export] *)
Definition KO1 : list nat := [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Definition ed_frame (M : mem) (sp1 rav : Z) (R0 : bvmap 5 word) : Prop :=
  L5.u64_at RSEGS M (sp1 - 8) rav /\ L5.u64_at RSEGS M (sp1 - 16) (bv_unsigned (getr R0 8%bv)).
Lemma ed_frame_x : forall (K : Z -> Prop) (M M' : mem) sp1 rav R0, TK.samem K M M' -> 2 ^ 40 <= sp1 <= 2 ^ 47 -> (forall i, sp1 - 16 <= i < sp1 -> K i) -> ed_frame M sp1 rav R0 -> ed_frame M' sp1 rav R0.
Proof. intros K M M' sp1 rav R0 AG Hsp HK (F1 & F2). split; (eapply (TK.u64_samem K M M'); [exact AG | lia | intros i Hi; apply HK; lia | assumption]). Qed.
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

(* [comment removed for export] *)
Definition tail_cells (M : mem) (V : Z) : Prop :=
  L5.u64_at RSEGS M (V + 48) 2562 /\
  (L5.u64_at RSEGS M (V + 96) 0 /\ L5.u64_at RSEGS M (V + 120) 0 /\ L5.u64_at RSEGS M (V + 144) 0 /\ L5.u64_at RSEGS M (V + 168) 0 /\ L5.u64_at RSEGS M (V + 192) 0 /\ L5.u64_at RSEGS M (V + 216) 0) /\
  L5.defined M (V + 16) 8 /\ L5.defined M (V + 80) 8.
Lemma tail_cells_x : forall (K : Z -> Prop) (M M' : mem) V, TK.samem K M M' -> 2 ^ 40 <= V <= 2 ^ 47 - 408 -> (forall i, V + 16 <= i < V + 240 -> K i) ->
  (forall i, V + 16 <= i < V + 88 -> M (Z_to_bv 64 i) <> None -> M' (Z_to_bv 64 i) <> None) ->
  tail_cells M V -> tail_cells M' V.
Proof.
  intros K M M' V AG HV HK DEF (C48 & C6 & D16 & D80). split; [|split; [|split]].
  - apply (TK.u64_samem K M M' _ _ AG); [lia | intros i Hi; apply HK; lia | exact C48].
  - destruct C6 as (C1 & C2 & C3 & C4 & C5 & C6). repeat split; (apply (TK.u64_samem K M M' _ _ AG); [lia | intros j Hj; apply HK; lia | assumption]).
  - intros i Hi. apply DEF; [lia | apply D16; exact Hi].
  - intros i Hi. apply DEF; [lia | apply D80; exact Hi].
Qed.

Section S.
Context {SCFG_P : ScfgP}.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.

(* [comment removed for export] *)
Lemma s_ed_entry : forall (fx : FPState) R M model K sp1 V b rav,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx ->
  getr R 2%bv = Z_to_bv 64 sp1 -> CK.spok sp1 -> getr R 1%bv = Z_to_bv 64 rav -> L5.ra_ok rav -> getr R 10%bv = Z_to_bv 64 V ->
  2 ^ 40 <= V <= 2 ^ 47 - 408 -> V mod 8 = 0 -> 0 <= b < 2 ^ 64 -> L5.u64_at RSEGS M (V + 264) b -> L5.defined M (sp1 - 32) 32 -> sp1 <= V ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 32) -> getr R' 1%bv = Z_to_bv 64 JOIN -> getr R' 10%bv = Z_to_bv 64 b -> getr R' 8%bv = Z_to_bv 64 V ->
      getr R' 12%bv = Z_to_bv 64 (V + 264) ->
      ed_frame M' sp1 rav R -> TK.keepsR KO1 R R' -> TK.samem (fun a => ~ (sp1 - 32 <= a < sp1)) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' BR M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R PMES.PC_ENC_DTOR M model) K.
Proof.
  intros fx R M model K sp1 V b rav Hh Hl Hfp H2 [Hsp Hal] H1 Hra H10 HV HV8 Hb C264 DF J1 Kbr.
  change PMES.PC_ENC_DTOR with (CC.cp_pc G.cp0).
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  ck_open FPM G.cp0 (G.plans 0%nat _ eq_refl) 0 [b] (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_reg E (10%bv : reg) H10. ck_gh E 0%nat b.
    unfold know_ok, G.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_unk. + e_wr. + e_range. + e_align HV8. + ck_kw64 (V + 264) b C264. + e_disj.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E (10%bv : reg) H10. ck_reg E (1%bv : reg) H1. ck_gh E 0%nat b.
    ck_leaf Hag E'.
    assert (FRM : TK.samem (fun a => ~ (sp1 - 32 <= a < sp1)) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha Hk1; cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (Kbr fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold JOIN; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg) | tk_lin HLF (8%bv : reg) | tk_lin HLF (12%bv : reg)
      | | ck_keeps HLF Hag64 KO1 | exact FRM | exact MG].
    split; [ck_cell64 HLF (EVar 2) (-8) (EVar 33); ck_atom | ck_saved HLF Hag64 (-16) 40%nat (8%bv : reg)].
Qed.

Lemma s_ed_loop : forall n (fx : FPState) R M model K sp1 V b e j,
  j < Z.of_nat n ->
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 32) -> CK.spok sp1 -> getr R 1%bv = Z_to_bv 64 JOIN ->
  getr R 8%bv = Z_to_bv 64 V -> getr R 10%bv = Z_to_bv 64 b -> getr R 11%bv = Z_to_bv 64 (b + 32 * j) -> getr R 12%bv = Z_to_bv 64 (V + 264) -> getr R 13%bv = Z_to_bv 64 32 ->
  2 ^ 40 <= V <= 2 ^ 47 - 408 -> 4096 <= b <= 2 ^ 47 -> 0 <= e < 2 ^ 64 -> L5.u64_at RSEGS M (V + 280) e -> L5.defined M (V + 272) 8 -> 1 <= j <= 1024 -> sp1 <= V ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 32) -> getr R' 1%bv = Z_to_bv 64 JOIN -> getr R' 10%bv = Z_to_bv 64 b ->
      getr R' 8%bv = Z_to_bv 64 V -> TK.keepsR KO1 R R' ->
      TK.samem (fun a => ~ (V + 272 <= a < V + 280)) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_OPDEL_SIZED M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R LOOP M model) K.
Proof.
  induction n as [|n IH]; intros fx R M model K sp1 V b e j Hn Hh Hl Hfp H2 [Hsp Hal] H1 H8 H10 H11 H12 H13 HV Hb He C280 D272 Hj J1 Kdel; [lia|].
  change LOOP with (CC.cp_pc G.cp4).
  set (E := CK.hvB sp1 R [e; j] (fun _ : nat => @nil byte)).
  assert (U2 : bv_unsigned (ev E 2) = sp1) by (apply CK.hvB_sp; lia).
  ck_reg E (8%bv : reg) H8. ck_reg E (10%bv : reg) H10. ck_gh E 0%nat e. ck_gh E 1%nat j.
  apply (TK.stretch_cps FPM G.cp4 fx E R M model K (G.plans 4%nat _ eq_refl) Hh Hl Hfp).
  - apply (TKX.regs_ok_hvX _ (-32) [(1%nat, ELit JOIN); (11%nat, APC.eadd (EVar 42) (APC.escale 32 (EVar 65))); (12%nat, APC.eaddz (EVar 40) 264); (13%nat, ELit 32)]);
      [vm_compute; reflexivity | lia | lia | exact H2 |].
    intros q x X. cbn [In] in X. destruct X as [X|[X|[X|[X|[]]]]]; injection X as <- <-; fold E.
    + exact H1.
    + rewrite (TK.edenot_lin _ _ (b + 32 * j)); [exact H11 | lin_eval; rw_atoms; lia | lia].
    + rewrite (TK.edenot_lin _ _ (V + 264)); [exact H12 | lin_eval; rw_atoms; lia | lia].
    + exact H13.
  - unfold know_ok, G.cp4. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_range. + e_range. + ck_kw64 (V + 280) e C280. + e_unk. + e_wr. + e_range. + e_range. + e_disj.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_leaf Hag E'.
    assert (FRM : TK.samem (fun a => ~ (V + 272 <= a < V + 280)) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha Hk1; cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    ck_leaf_k k Hnth; [| ck_leaf_k k Hnth; [| ck_leaf_end k Hnth]].
    + apply (Kdel fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold JOIN; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg) | tk_lin HLF (8%bv : reg) | ck_keeps HLF Hag64 KO1 | exact FRM | exact MG].
    + assert (KOl : TK.keepsR KO1 R R') by (ck_keeps HLF Hag64 KO1).
      pose proof (CK.lf_cell _ _ _ _ _ _ (KRange (APC.eaddz (EVar 65) (-1)) 1 1024) HLF ltac:(vm_compute; reflexivity)) as RJ.
      cbn [kentry_ok] in RJ. ck_rlin RJ.
      apply (IH fx' R' M' model K sp1 V b e (j - 1)); [lia | exact Hh | exact Hl | exact Hfp' | tk_lin HLF (2%bv : reg) | split; [exact Hsp | exact Hal]
        | unfold JOIN; tk_lin HLF (1%bv : reg) | tk_lin HLF (8%bv : reg) | tk_lin HLF (10%bv : reg) | tk_lin HLF (11%bv : reg) | tk_lin HLF (12%bv : reg) | tk_lin HLF (13%bv : reg)
        | exact HV | exact Hb | exact He | ck_cell64 HLF (EVar 40) 280 (EVar 64); ck_atom | exact (L5.defined_grows M M' _ _ MG D272) | lia | exact J1 |].
      intros fx2 R2 M2 Hfp2 H2b H1b H10b H8b KO2 AG2 MG2.
      exact (Kdel fx2 R2 M2 Hfp2 H2b H1b H10b H8b (TK.keepsR_trans _ _ _ _ KOl KO2) (TK.samem_trans _ _ _ _ FRM AG2) (mem_grows_trans _ _ _ MG MG2)).
Qed.

(* [comment removed for export] *)
Lemma s_ed_long : forall (fx : FPState) R M model K sp1 V b e d,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 32) -> CK.spok sp1 -> getr R 1%bv = Z_to_bv 64 JOIN ->
  getr R 8%bv = Z_to_bv 64 V -> getr R 10%bv = Z_to_bv 64 b -> getr R 12%bv = Z_to_bv 64 (V + 264) ->
  2 ^ 40 <= V <= 2 ^ 47 - 408 -> 4096 <= b <= 2 ^ 47 -> 0 <= e < 2 ^ 64 -> L5.u64_at RSEGS M (V + 280) e ->
  0 <= d <= 1024 -> L5.u64_at RSEGS M (V + 272) (b + 32 * d) -> L5.defined M (V + 272) 8 -> sp1 <= V ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 32) -> getr R' 1%bv = Z_to_bv 64 JOIN -> getr R' 10%bv = Z_to_bv 64 b ->
      getr R' 8%bv = Z_to_bv 64 V -> TK.keepsR KO1 R R' ->
      TK.samem (fun a => ~ (V + 272 <= a < V + 280)) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_OPDEL_SIZED M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R BR M model) K.
Proof.
  intros fx R M model K sp1 V b e d Hh Hl Hfp H2 [Hsp Hal] H1 H8 H10 H12 HV Hb He C280 Hd C272 D272 J1 Kdel.
  change BR with (CC.cp_pc G.cp1).
  set (E := CK.hvB sp1 R [e; d] (fun _ : nat => @nil byte)).
  assert (U2 : bv_unsigned (ev E 2) = sp1) by (apply CK.hvB_sp; lia).
  ck_reg E (8%bv : reg) H8. ck_reg E (10%bv : reg) H10. ck_gh E 0%nat e. ck_gh E 1%nat d.
  apply (TK.stretch_cps FPM G.cp1 fx E R M model K (G.plans 1%nat _ eq_refl) Hh Hl Hfp).
  - apply (TKX.regs_ok_hvX _ (-32) [(1%nat, ELit JOIN); (12%nat, APC.eaddz (EVar 40) 264)]); [vm_compute; reflexivity | lia | lia | exact H2 |].
    intros q x X. cbn [In] in X. destruct X as [X|[X|[]]]; injection X as <- <-; fold E; [exact H1 | rewrite (TK.edenot_lin _ _ (V + 264)); [exact H12 | lin_eval; rw_atoms; lia | lia]].
  - unfold know_ok, G.cp1. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_range. + e_range. + ck_kw64 (V + 280) e C280. + ck_kw64 (V + 272) (b + 32 * d) C272. + e_wr. + e_range. + e_range. + e_disj.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_leaf Hag E'.
    assert (FRM : TK.samem (fun a => ~ (V + 272 <= a < V + 280)) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha Hk1; cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    ck_leaf_k k Hnth; [| ck_leaf_k k Hnth; [| ck_leaf_end k Hnth]].
    + apply (Kdel fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold JOIN; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg) | tk_lin HLF (8%bv : reg) | ck_keeps HLF Hag64 KO1 | exact FRM | exact MG].
    + assert (KOl : TK.keepsR KO1 R R') by (ck_keeps HLF Hag64 KO1).
      pose proof (CK.lf_cell _ _ _ _ _ _ (KRange (EVar 65) 1 1024) HLF ltac:(vm_compute; reflexivity)) as RJ.
      cbn [kentry_ok] in RJ. ck_rlin RJ.
      apply (s_ed_loop (Z.to_nat 1025) fx' R' M' model K sp1 V b e d); [rewrite Z2Nat.id by lia; lia | exact Hh | exact Hl | exact Hfp' | tk_lin HLF (2%bv : reg) | split; [exact Hsp | exact Hal]
        | unfold JOIN; tk_lin HLF (1%bv : reg) | tk_lin HLF (8%bv : reg) | tk_lin HLF (10%bv : reg) | tk_lin HLF (11%bv : reg) | tk_lin HLF (12%bv : reg) | tk_lin HLF (13%bv : reg)
        | exact HV | exact Hb | exact He | ck_cell64 HLF (EVar 40) 280 (EVar 64); ck_atom | exact (L5.defined_grows M M' _ _ MG D272) | lia | exact J1 |].
      intros fx2 R2 M2 Hfp2 H2b H1b H10b H8b KO2 AG2 MG2.
      exact (Kdel fx2 R2 M2 Hfp2 H2b H1b H10b H8b (TK.keepsR_trans _ _ _ _ KOl KO2) (TK.samem_trans _ _ _ _ FRM AG2) (mem_grows_trans _ _ _ MG MG2)).
Qed.

(* [comment removed for export] *)
Lemma s_ed_short : forall (fx : FPState) R M model K sp1 V rav R0,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 32) -> CK.spok sp1 -> getr R 1%bv = Z_to_bv 64 JOIN ->
  getr R 8%bv = Z_to_bv 64 V -> getr R 10%bv = Z_to_bv 64 0 -> getr R 12%bv = Z_to_bv 64 (V + 264) ->
  2 ^ 40 <= V <= 2 ^ 47 - 408 -> PML.img_ro M -> tail_cells M V -> ed_frame M sp1 rav R0 -> L5.ra_ok rav -> L5.defined M (sp1 - 48) 48 -> sp1 <= V ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 32) -> getr R' 8%bv = Z_to_bv 64 V -> TK.keepsR KO1 R R' ->
      tail_cells M' V -> ed_frame M' sp1 rav R0 -> TK.samem (fun a => ~ (sp1 - 48 <= a < sp1) /\ ~ (V + 16 <= a < V + 24) /\ ~ (V + 80 <= a < V + 88)) M M' -> mem_grows M M' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' JOIN M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R BR M model) K.
Proof.
  intros fx R M model K sp1 V rav R0 Hh Hl Hfp H2 [Hsp Hal] H1 H8 H10 H12 HV RO (C48 & C6 & D16 & D80) (F1 & F2) Hra DF J1 Kr1.
  change BR with (CC.cp_pc G.cp2).
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  pose proof (bv_unsigned_in_range _ (getr R0 8%bv)) as G8. change (bv_modulus 64) with (2 ^ 64) in G8.
  set (gl := [rav; bv_unsigned (getr R0 8%bv)]).
  set (E := CK.hvB sp1 R gl (fun _ : nat => @nil byte)).
  assert (U2 : bv_unsigned (ev E 2) = sp1) by (apply CK.hvB_sp; lia).
  ck_reg E (8%bv : reg) H8. ck_gh E 0%nat rav. ck_gh E 1%nat (bv_unsigned (getr R0 8%bv)).
  apply (TK.stretch_cps FPM G.cp2 fx E R M model K (G.plans 2%nat _ eq_refl) Hh Hl Hfp).
  - apply (TKX.regs_ok_hvX _ (-32) [(1%nat, ELit JOIN); (10%nat, ELit 0); (12%nat, APC.eaddz (EVar 40) 264)]); [vm_compute; reflexivity | lia | lia | exact H2 |].
    intros q x X. cbn [In] in X. destruct X as [X|[X|[X|[]]]]; injection X as <- <-; fold E; [exact H1 | exact H10 | rewrite (TK.edenot_lin _ _ (V + 264)); [exact H12 | lin_eval; rw_atoms; lia | lia]].
  - unfold know_ok, G.cp2. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_wr. + e_range. + tk_kimg RO. + ck_kw64 (V + 48) 2562 C48.
    + ck_kw64 (V + 96) 0 (proj1 C6). + ck_kw64 (V + 120) 0 (proj1 (proj2 C6)). + ck_kw64 (V + 144) 0 (proj1 (proj2 (proj2 C6))).
    + ck_kw64 (V + 168) 0 (proj1 (proj2 (proj2 (proj2 C6)))). + ck_kw64 (V + 192) 0 (proj1 (proj2 (proj2 (proj2 (proj2 C6))))). + ck_kw64 (V + 216) 0 (proj2 (proj2 (proj2 (proj2 (proj2 C6))))).
    + ck_kw64 (sp1 - 8) rav F1. + ck_kw64 (sp1 - 16) (bv_unsigned (getr R0 8%bv)) F2.
    + e_unk. + e_unk. + e_wr. + e_unk. + e_wr. + e_disj.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    assert (GH : forall j z, nth_error gl j = Some z -> ev E' (64 + j) = Z_to_bv 64 z).
    { intros j z Hj. assert (Hj8 : (j < 2)%nat) by (change 2%nat with (length gl); apply nth_error_Some; rewrite Hj; discriminate). change (CC.cp_nx G.cp2) with 66%nat in Hag.
      rewrite <- (proj1 Hag (64 + j)%nat) by lia. exact (CK.hvB_gh_w _ _ _ _ j z Hj). }
    ck_leaf Hag E'.
    assert (FRM : TK.samem (fun a => ~ (sp1 - 48 <= a < sp1) /\ ~ (V + 16 <= a < V + 24) /\ ~ (V + 80 <= a < V + 88)) M M').
    { apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha (Hk1 & Hk2 & Hk3); cbn [CC.cp_F]; tk_outside. }
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (Kr1 fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | tk_lin HLF (8%bv : reg) | ck_keeps HLF Hag64 KO1 | | | exact FRM | exact MG].
    + split; [ck_cell64 HLF (EVar 40) 48 (ELit 2562); reflexivity|]. split.
      { split; [ck_cell64 HLF (EVar 40) 96 (ELit 0); reflexivity|]. split; [ck_cell64 HLF (EVar 40) 120 (ELit 0); reflexivity|]. split; [ck_cell64 HLF (EVar 40) 144 (ELit 0); reflexivity|].
        split; [ck_cell64 HLF (EVar 40) 168 (ELit 0); reflexivity|]. split; [ck_cell64 HLF (EVar 40) 192 (ELit 0); reflexivity | ck_cell64 HLF (EVar 40) 216 (ELit 0); reflexivity]. }
      split; [exact (L5.defined_grows M M' _ _ MG D16) | exact (L5.defined_grows M M' _ _ MG D80)].
    + split; [ck_cell64 HLF (EVar 2) (-8) (EVar 64); cbn [edenot]; rewrite <- (u64_of_Z rav) by lia; f_equal; exact (GH 0%nat _ eq_refl)
             | ck_cell64 HLF (EVar 2) (-16) (EVar 65); cbn [edenot]; etransitivity; [| apply (u64_of_Z (bv_unsigned (getr R0 8%bv))); lia]; f_equal; exact (GH 1%nat _ eq_refl)].
Qed.

(* [comment removed for export] *)
Lemma s_ed_r1 : forall (fx : FPState) R M model K sp1 V rav R0,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 32) -> CK.spok sp1 -> getr R 8%bv = Z_to_bv 64 V ->
  2 ^ 40 <= V <= 2 ^ 47 - 408 -> PML.img_ro M -> tail_cells M V -> ed_frame M sp1 rav R0 -> L5.ra_ok rav -> L5.defined M (sp1 - 48) 48 -> sp1 <= V ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 sp1 -> getr R' 8%bv = getr R0 8%bv -> TK.keepsR KO1 R R' ->
      L5.u64_at RSEGS M' (V + 16) VT_OPTS_D -> L5.u64_at RSEGS M' (V + 80) VT_COMMON_D ->
      TK.samem (fun a => ~ (sp1 - 48 <= a < sp1) /\ ~ (V + 16 <= a < V + 24) /\ ~ (V + 80 <= a < V + 88)) M M' -> mem_grows M M' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' rav M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R JOIN M model) K.
Proof.
  intros fx R M model K sp1 V rav R0 Hh Hl Hfp H2 [Hsp Hal] H8 HV RO (C48 & C6 & D16 & D80) (F1 & F2) Hra DF J1 Kret.
  change JOIN with (CC.cp_pc G.cp3).
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  pose proof (bv_unsigned_in_range _ (getr R0 8%bv)) as G8. change (bv_modulus 64) with (2 ^ 64) in G8.
  set (gl := [rav; bv_unsigned (getr R0 8%bv)]).
  ck_open FPM G.cp3 (G.plans 3%nat _ eq_refl) (-32) gl (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_reg E (8%bv : reg) H8. ck_gh E 0%nat rav. ck_gh E 1%nat (bv_unsigned (getr R0 8%bv)).
    unfold know_ok, G.cp3. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_wr. + e_range. + tk_kimg RO. + ck_kw64 (V + 48) 2562 C48.
    + ck_kw64 (V + 96) 0 (proj1 C6). + ck_kw64 (V + 120) 0 (proj1 (proj2 C6)). + ck_kw64 (V + 144) 0 (proj1 (proj2 (proj2 C6))).
    + ck_kw64 (V + 168) 0 (proj1 (proj2 (proj2 (proj2 C6)))). + ck_kw64 (V + 192) 0 (proj1 (proj2 (proj2 (proj2 (proj2 C6))))). + ck_kw64 (V + 216) 0 (proj2 (proj2 (proj2 (proj2 (proj2 C6))))).
    + ck_kw64 (sp1 - 8) rav F1. + ck_kw64 (sp1 - 16) (bv_unsigned (getr R0 8%bv)) F2.
    + e_unk. + e_unk. + e_wr. + e_unk. + e_wr. + e_disj.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    assert (GH : forall j z, nth_error gl j = Some z -> ev E' (64 + j) = Z_to_bv 64 z).
    { intros j z Hj. assert (Hj8 : (j < 2)%nat) by (change 2%nat with (length gl); apply nth_error_Some; rewrite Hj; discriminate). change (CC.cp_nx G.cp3) with 66%nat in Hag.
      rewrite <- (proj1 Hag (64 + j)%nat) by lia. exact (CK.hvB_gh_w _ _ _ _ j z Hj). }
    ck_reg E (8%bv : reg) H8. ck_gh E 0%nat rav. ck_gh E 1%nat (bv_unsigned (getr R0 8%bv)).
    ck_leaf Hag E'.
    assert (FRM : TK.samem (fun a => ~ (sp1 - 48 <= a < sp1) /\ ~ (V + 16 <= a < V + 24) /\ ~ (V + 80 <= a < V + 88)) M M').
    { apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha (Hk1 & Hk2 & Hk3); cbn [CC.cp_F]; tk_outside. }
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    assert (RA : getr R' 1%bv = Z_to_bv 64 rav) by (tk_reg HLF (1%bv : reg); exact (GH 0%nat _ eq_refl)).
    apply (CK.ret_leaf fx' R' _ M' model K rav ret_ed Hh Hl RA Hra).
    apply (Kret fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | | ck_keeps HLF Hag64 KO1 | | | exact FRM | exact MG].
    + tk_reg HLF (8%bv : reg). etransitivity; [exact (GH 1%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
    + unfold VT_OPTS_D. ck_cell64 HLF (EVar 40) 16 (ELit 803360). reflexivity.
    + unfold VT_COMMON_D. ck_cell64 HLF (EVar 40) 80 (ELit 803504). reflexivity.
Qed.
End S.

(* [comment removed for export] *)
Section H.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis OPDELS : PMS.opdel_sized_spec L HI.

Theorem enc_dtor_ok : PMES.enc_dtor_spec L HI.
Proof.
  intros LBo cr sp r V S2 g fx R M model K HH (Hh & Hl & Hmat) HK0 Hfp (EN & A0 & EI & OI & DEFV & OBJ & RO) Hcont.
  destruct EN as (Hra & Hrok & Hsp & Htp & STK). pose proof STK as (S1 & S2' & S3 & S4 & S5). destruct OBJ as ((OV1 & OV2 & OV3) & (OS1 & OS2 & OS3) & AVS).
  pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI. pose proof (PmLayout.ly_errno L LAY) as ERR.
  unfold PML.a0 in A0. unfold PMES.ENC_SIZE in *. unfold PML.apart in AVS.
  set (SCR := PMES.ENC_DTOR_SCR) in *. assert (HSCR : SCR = 8288) by reflexivity.
  assert (SPOK : CK.spok sp) by (split; [unfold hl_ceil in *; lia | exact S1]).
  destruct EI as (EO & SA & SK & GLEN & DMAX).
  destruct SA as (A264 & A272 & A280 & Acap & Ak & _). unfold PMES.O_STACK, PML.u64 in A264, A272, A280.
  replace (V + 264 + 8) with (V + 272) in A272 by lia. replace (V + 264 + 16) with (V + 280) in A280 by lia.
  pose proof EO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C48 & _). unfold PMES.O_NL_CHARS, PML.u64 in C48.
  destruct OI as (O1 & O2 & O3 & O4 & O5 & O6). unfold PML.u64 in O1, O2, O3, O4, O5, O6.
  pose proof (TK2.blocks_ok_heap L HI HIok _ _ _ _ HH) as BOK.
  set (LBf := LBo ++ PML.srep_blocks (PMES.g_rep g)).
  assert (ELB : LBo ++ PMES.g_lbv g = LBf ++ PMES.stack_blocks (PMES.g_sb g) (PMES.g_scap g)) by (unfold LBf, PMES.g_lbv; rewrite app_assoc; reflexivity).
  assert (BOKf : TK2.blocks_ok L LBf) by (intros b Hb; apply BOK; rewrite ELB; apply in_or_app; left; exact Hb).
  unfold hl_ceil in *.
  assert (DEPTH : 0 <= PMES.depth (PMES.g_es g)) by (unfold PMES.depth; lia).
  assert (TC : tail_cells M V).
  { split; [exact C48|]. split; [|split; [eapply L5.defined_sub; [exact DEFV | lia | lia] | eapply L5.defined_sub; [exact DEFV | lia | lia]]].
    repeat split; assumption. }
  (* [comment removed for export] *)
  set (foot := fun a : Z => V <= a < V + 408).
  assert (WF : forall w a, In w [(V, 408)] -> L5.in_rng w a -> foot a) by (intros w a [<-|[]] Hin; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; exact Hin).
  assert (FR0 : TK2.FR L LBf sp SCR foot M M) by (split; [intros a _ _ _ _; reflexivity | intros a Ha; replace a with (sp - SCR + (a - (sp - SCR))) by lia; apply S5; lia]).
  assert (CLI : forall a LBx spc scr, foot a -> sp - SCR <= spc - scr -> spc <= sp -> client_addr L LBx spc scr a /\ ~ in_errno L a).
  { intros a LBx spc scr Hf H1 H2. unfold foot in Hf. split; [right; left; unfold hl_ceil; lia | unfold in_errno; rewrite ERR; lia]. }
  assert (Hsb : 0 <= PMES.g_sb g < 2 ^ 64).
  { destruct Ak as [[_ E0]|(k & Hk & Hc)]; [rewrite E0; lia|]. destruct (BOK (PMES.g_sb g, PMES.g_scap g)) as (B0 & B1 & B2 & B3 & B4); [|cbn [fst snd] in *; unfold hl_ceil in B4; lia].
    rewrite ELB. apply in_or_app. right. unfold PMES.stack_blocks. destruct (Z.eqb_spec (PMES.g_scap g) 0); [pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)); lia | left; reflexivity]. }
  (* [comment removed for export] *)
  apply (s_ed_entry FPM fx R M model K sp V (PMES.g_sb g) r Hh Hl Hfp Hsp SPOK Hra Hrok A0 ltac:(lia) OV3 Hsb A264 ltac:(eapply L5.defined_sub; [exact S5 | lia | lia]) OV1).
  intros fx1 R1 M1 Hfp1 H2a H1a H10a H8a H12a FRM1 KO1a AG1 MG1.
  assert (AGS1 : TK.samem (fun a => ~ (sp - 32 <= a < hl_sptop L)) M M1) by (apply (TK.samem_weaken _ _ _ _ AG1); intros a Ha; lia).
  pose proof (TK2.heap_stack_write L HI HIok LAY _ _ M M1 _ (sp - 32) (hl_sptop L) HH ltac:(lia) ltac:(unfold hl_ceil; lia) ltac:(lia) AGS1 MG1) as HH1.
  assert (FR1 : TK2.FR L LBf sp SCR foot M M1) by (apply (TK2.FR_grows L LAY LBf sp SCR foot M M M1 _ FR0 AG1 MG1 BOKf ltac:(unfold hl_ceil; lia) ltac:(lia)); intros a Ha; unfold foot; apply NNPP in Ha; lia).
  assert (TP1 : getr R1 4%bv = Z_to_bv 64 PML.TP) by (rewrite (KO1a 4%bv ltac:(ck_in)); exact Htp).
  assert (STK1 : L5C.stk (hl_sptop L) M1 (sp - 32) PMS.OPDEL_SCR).
  { apply (CK.sub_stk _ M M1 sp SCR _ _ STK MG1); [apply CK.al16; [exact S1 | reflexivity] | unfold PMS.OPDEL_SCR, PML.HEAP_STACK; lia | lia | unfold PMS.OPDEL_SCR, PML.HEAP_STACK; lia]. }
  assert (TC1 : tail_cells M1 V) by (apply (tail_cells_x _ M M1 V AG1); [lia | intros i Hi; lia | intros i Hi; apply MG1 | exact TC]).
  assert (RO1 : PML.img_ro M1) by (apply (TK.img_clear_samem _ M M1 _ _ AG1); [lia | unfold PML.IMG_RO_HI; lia | intros i Hi; unfold PML.IMG_RO_HI in Hi; lia | exact RO]).
  assert (A280' : L5.u64_at RSEGS M1 (V + 280) (PMES.g_sb g + PMES.g_scap g)) by (apply (TK.u64_samem _ M M1 _ _ AG1); [lia | intros i Hi; lia | exact A280]).
  assert (A272' : L5.u64_at RSEGS M1 (V + 272) (PMES.g_sb g + 32 * PMES.depth (PMES.g_es g))) by (apply (TK.u64_samem _ M M1 _ _ AG1); [lia | intros i Hi; lia | exact A272]).
  assert (DF1 : L5.defined M1 (sp - 48) 48) by (apply (L5.defined_grows M M1 _ _ MG1); eapply L5.defined_sub; [exact S5 | lia | lia]).
  (* [comment removed for export] *)
  assert (TAIL : forall (fxk : FPState) Rk Mk modelk, PML.fp_ok fxk -> getr Rk 2%bv = Z_to_bv 64 (sp - 32) -> getr Rk 8%bv = Z_to_bv 64 V -> TK.keepsR KO1 R Rk ->
            PML.img_ro Mk -> tail_cells Mk V -> ed_frame Mk sp r R -> TK2.FR L LBf sp SCR foot M Mk ->
            hi_heap HI LBf cr Mk (m_vmmaps modelk) -> model_but_vm model modelk -> PML.model_ok modelk ->
            (forall a, 0 <= a < 2 ^ 64 -> foot a -> M (Z_to_bv 64 a) <> None -> Mk (Z_to_bv 64 a) <> None) ->
            TK.samem (fun a => S2 <= a < S2 + 24 \/ in_block LBf a) M Mk ->
            srealizes RSEGS SCFG (@PML.cfg fxk Rk JOIN Mk modelk) K).
  { intros fxk Rk Mk modelk Hfpk Rksp Rks0 KOk ROk TCk EFk FRk HHk BVk (Hhk & Hlk & Hmatk) CDEF AGk.
    assert (DFk : L5.defined Mk (sp - 48) 48) by (destruct FRk as [_ FD]; intros i Hi; apply FD; lia).
    apply (s_ed_r1 FPM fxk Rk Mk modelk K sp V r R Hhk Hlk Hfpk Rksp SPOK Rks0 ltac:(lia) ROk TCk EFk Hrok DFk OV1).
    intros fx4 R4 M4 Hfp4 H2d H8d KO4 C16 C80 AG4 MG4.
    assert (AGS4 : TK.samem (fun a => ~ (sp - 48 <= a < hl_sptop L)) Mk M4) by (apply (TK.samem_weaken _ _ _ _ AG4); intros a Ha; lia).
    pose proof (TK2.heap_stack_write L HI HIok LAY _ _ Mk M4 _ (sp - 48) (hl_sptop L) HHk ltac:(lia) ltac:(unfold hl_ceil; lia) ltac:(lia) AGS4 MG4) as HH4.
    assert (FR4 : TK2.FR L LBf sp SCR foot M M4).
    { apply (TK2.FR_grows L LAY LBf sp SCR foot M Mk M4 _ FRk AG4 MG4 BOKf ltac:(unfold hl_ceil; lia) ltac:(lia)). intros a Ha. unfold foot.
      destruct (classic (sp - 48 <= a < sp)); [left; lia|]. right. destruct (classic (V + 16 <= a < V + 24)); [lia|]. destruct (classic (V + 80 <= a < V + 88)); [lia|]. exfalso. apply Ha. tauto. }
    apply (Hcont fx4 R4 M4 modelk LBf cr LBf [(V, 408)] Hfp4).
    - split; [| repeat split; reflexivity].
      pose proof SK as (SK1 & SK2 & SK3).
      assert (AGS : L5C.agree_on Mk M4 S2 24) by (intros i Hi; apply AG4; lia).
      assert (AGS0 : L5C.agree_on M Mk S2 24) by (intros i Hi; apply AGk; [lia | left; lia]).
      split; [|split; [exact (L5.defined_grows _ _ _ _ MG4 (L5C.defined_agree M Mk S2 24 AGS0 SK2)) | exact SK3]].
      apply (EK.str_at_agree Mk M4 S2 _ ltac:(lia) ltac:(lia) AGS).
      { destruct (PMES.g_rep g) as [s|cap p s] eqn:Er; [exact I|]. destruct (BOKf (p, cap)) as (B0 & B1 & B2 & B3 & B4); [unfold LBf; apply in_or_app; right; cbn; left; reflexivity|].
        cbn [fst snd] in *. unfold hl_ceil in B4. split; [lia|]. split; [lia|]. intros i Hi. apply AG4; lia. }
      apply (EK.str_at_agree M Mk S2 _ ltac:(lia) ltac:(lia) AGS0); [|exact SK1].
      destruct (PMES.g_rep g) as [s|cap p s] eqn:Er; [exact I|]. destruct (BOKf (p, cap)) as (B0 & B1 & B2 & B3 & B4); [unfold LBf; apply in_or_app; right; cbn; left; reflexivity|].
      cbn [fst snd] in *. unfold hl_ceil in B4. split; [lia|]. split; [lia|]. intros i Hi. apply AGk; [lia | right; exists (p, cap); split; [unfold LBf; apply in_or_app; right; cbn; left; reflexivity | cbn [fst snd]; lia]].
    - apply rp_final; [rewrite H2d, Hsp; reflexivity | exact H8d | exact (TK.keepsR_trans _ _ _ _ KOk KO4)].
    - destruct FR4 as [F1 F2]. apply L5C.hpres_intro.
      + intros a (Ha & HC & HE & HO). apply F1; [exact Ha | exact HC | | exact HE]. intros X. apply (HO (V, 408) (or_introl eq_refl)). unfold L5.in_rng. cbn [fst snd]. exact X.
      + intros i Hi. apply F2. lia.
      + intros a Ha HC HE Hd. destruct (classic (foot a)) as [Y|N]; [|rewrite (F1 a Ha HC N HE); exact Hd]. apply MG4. exact (CDEF a Ha Y Hd).
    - exact BVk.
    - exact HH4. }
  destruct (Z.eq_dec (PMES.g_scap g) 0) as [Z0|Z0].
  - (* [comment removed for export] *)
    assert (SB0 : PMES.g_sb g = 0) by (destruct Ak as [[_ E]|(k & Hk & Hc)]; [exact E | exfalso; pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)); lia]).
    rewrite SB0 in H10a.
    assert (ELB0 : LBo ++ PMES.g_lbv g = LBf) by (rewrite ELB; unfold PMES.stack_blocks; rewrite Z0; cbn; rewrite app_nil_r; reflexivity).
    rewrite ELB0 in HH1.
    apply (s_ed_short FPM fx1 R1 M1 model K sp V r R Hh Hl Hfp1 H2a SPOK H1a H8a H10a H12a ltac:(lia) RO1 TC1 FRM1 Hrok DF1 OV1).
    intros fx2 R2 M2 Hfp2 H2b H8b KO2 TC2 EF2 AG2 MG2.
    assert (AGS2 : TK.samem (fun a => ~ (sp - 48 <= a < hl_sptop L)) M1 M2) by (apply (TK.samem_weaken _ _ _ _ AG2); intros a Ha; lia).
    pose proof (TK2.heap_stack_write L HI HIok LAY _ _ M1 M2 _ (sp - 48) (hl_sptop L) HH1 ltac:(lia) ltac:(unfold hl_ceil; lia) ltac:(lia) AGS2 MG2) as HH2.
    assert (FR2 : TK2.FR L LBf sp SCR foot M M2).
    { apply (TK2.FR_grows L LAY LBf sp SCR foot M M1 M2 _ FR1 AG2 MG2 BOKf ltac:(unfold hl_ceil; lia) ltac:(lia)). intros a Ha. unfold foot.
      destruct (classic (sp - 48 <= a < sp)); [left; lia|]. right. destruct (classic (V + 16 <= a < V + 24)); [lia|]. destruct (classic (V + 80 <= a < V + 88)); [lia|]. exfalso. apply Ha. tauto. }
    assert (RO2 : PML.img_ro M2) by (apply (TK.img_clear_samem _ M1 M2 _ _ AG2); [lia | unfold PML.IMG_RO_HI; lia | intros i Hi; unfold PML.IMG_RO_HI in Hi; lia | exact RO1]).
    apply (TAIL fx2 R2 M2 model Hfp2 H2b H8b (TK.keepsR_trans _ _ _ _ KO1a KO2) RO2 TC2 EF2 FR2 HH2 (L5C.model_but_vm_refl _) (conj Hh (conj Hl Hmat))).
    + intros a Ha Hf Hd. apply MG2, MG1. exact Hd.
    + apply (CK.samem_weaken2 _ _ _ M M1 M2 AG1 AG2). intros a [Ha|(b & Hb & Hr)]; [lia|].
      destruct (BOKf b Hb) as (B0 & B1 & B2 & B3 & B4). unfold hl_ceil in B4. lia.
  - (* [comment removed for export] *)
    assert (INB : In (PMES.g_sb g, PMES.g_scap g) (LBo ++ PMES.g_lbv g)) by (rewrite ELB; apply in_or_app; right; unfold PMES.stack_blocks; rewrite (proj2 (Z.eqb_neq _ _) Z0); left; reflexivity).
    destruct (BOK _ INB) as (SB0 & SB1 & SB2 & SB3 & SB4). cbn [fst snd] in SB0, SB1, SB2, SB3, SB4. unfold hl_ceil in SB4.
    apply (s_ed_long FPM fx1 R1 M1 model K sp V (PMES.g_sb g) (PMES.g_sb g + PMES.g_scap g) (PMES.depth (PMES.g_es g)) Hh Hl Hfp1 H2a SPOK H1a H8a H10a H12a
             ltac:(lia) ltac:(lia) ltac:(lia) A280' ltac:(split; [exact DEPTH | exact DMAX]) A272'
             ltac:(apply (L5.defined_grows M M1 _ _ MG1); eapply L5.defined_sub; [exact DEFV | lia | lia]) OV1).
    intros fx2 R2 M2 Hfp2 H2b H1b H10b H8b KO2 AG2 MG2.
    assert (AGS2 : TK.samem (fun a => ~ (sp - 32 <= a < hl_sptop L)) M1 M2) by (apply (TK.samem_weaken _ _ _ _ AG2); intros a Ha; lia).
    pose proof (TK2.heap_stack_write L HI HIok LAY _ _ M1 M2 _ (sp - 32) (hl_sptop L) HH1 ltac:(lia) ltac:(unfold hl_ceil; lia) ltac:(lia) AGS2 MG2) as HH2.
    assert (FR2 : TK2.FR L LBf sp SCR foot M M2) by (apply (TK2.FR_grows L LAY LBf sp SCR foot M M1 M2 _ FR1 AG2 MG2 BOKf ltac:(unfold hl_ceil; lia) ltac:(lia)); intros a Ha; unfold foot; apply NNPP in Ha; lia).
    assert (TP2 : getr R2 4%bv = Z_to_bv 64 PML.TP) by (rewrite (KO2 4%bv ltac:(ck_in)); exact TP1).
    assert (STK2 : L5C.stk (hl_sptop L) M2 (sp - 32) PMS.OPDEL_SCR).
    { apply (CK.sub_stk _ M1 M2 (sp - 32) PMS.OPDEL_SCR _ _ STK1 MG2); [apply CK.al16; [exact S1 | reflexivity] | lia | lia | unfold PMS.OPDEL_SCR, PML.HEAP_STACK; lia]. }
    apply (OPDELS (LBo ++ PMES.g_lbv g) cr (PMES.g_sb g) (PMES.g_scap g) (sp - 32) JOIN fx2 R2 M2 model K HH2 (conj Hh (conj Hl Hmat)) HK0 Hfp2).
    { split; [exact (CK.mk_entry L R2 M2 (sp - 32) _ _ H1b (ra_ok_lit JOIN eq_refl) H2b TP2 STK2)|]. split; [exact H10b | exact INB]. }
    intros fx3 R3 M3 model3 LB3 cr3 LBk3 W3 Hfp3 (-> & -> & -> & ->) RP3 HP3 BV3 HH3.
    assert (LBE : lb_remove (PMES.g_sb g) (LBo ++ PMES.g_lbv g) = LBf).
    { destruct (hio_wf L SCFG HI HIok _ _ _ _ HH2) as (_ & ND & _). rewrite ELB in ND |- *. unfold PMES.stack_blocks in ND |- *. rewrite (proj2 (Z.eqb_neq _ _) Z0) in ND |- *.
      apply TKX.lb_remove_last. intros b Hb. exact (TKX.nodup_last _ (PMES.g_sb g, PMES.g_scap g) ND b Hb). }
    rewrite LBE in HP3, HH3.
    pose proof (TK2.hpres_samem L LAY _ (sp - 32) _ _ M2 M3 HP3 BOKf STK2 ltac:(unfold PMS.OPDEL_SCR, PML.HEAP_STACK; lia)) as AG3.
    assert (KH : forall a, sp - 32 <= a -> TK2.keepH L LBf [] (sp - 32) PMS.OPDEL_SCR a) by (intros a Ha; split; [intros w [] | left; exact Ha]).
    assert (FR3 : TK2.FR L LBf sp SCR foot M M3).
    { apply (TK2.FR_hpres L LAY LBf sp SCR foot M M2 M3 _ (sp - 32) _ _ FR2 HP3 BOKf); [intros b Hb; exact Hb | unfold hl_ceil; lia | lia | lia | unfold PMS.OPDEL_SCR, PML.HEAP_STACK; lia | lia | unfold PMS.OPDEL_SCR, PML.HEAP_STACK; lia | intros w a []]. }
    assert (MOK3 : PML.model_ok model3) by (split; [rewrite (L5C.halted_but_vm _ _ BV3); exact Hh | split; [rewrite (L5C.lazy_but_vm _ _ BV3); exact Hl | rewrite (L5C.materialized_but_vm _ _ BV3); exact Hmat]]).
    assert (CDEF3 : forall a, 0 <= a < 2 ^ 64 -> sp - 32 <= a < hl_sptop L -> M2 (Z_to_bv 64 a) <> None -> M3 (Z_to_bv 64 a) <> None).
    { intros a Ha Hr Hd. apply (L5C.hpres_cdef _ _ _ _ _ _ _ a HP3 Ha); [right; left; unfold hl_ceil; lia | unfold in_errno; rewrite ERR; lia | exact Hd]. }
    assert (RO3 : PML.img_ro M3).
    { apply (TK.img_clear_samem _ M2 M3 _ _ AG3); [lia | unfold PML.IMG_RO_HI; lia | intros i Hi; unfold PML.IMG_RO_HI in Hi; split; [intros w [] | right; right; right; lia]|].
      apply (TK.img_clear_samem _ M1 M2 _ _ AG2); [lia | unfold PML.IMG_RO_HI; lia | intros i Hi; unfold PML.IMG_RO_HI in Hi; lia | exact RO1]. }
    apply (TAIL fx3 R3 M3 model3 Hfp3 ltac:(rewrite (sp_rp _ _ RP3); exact H2b) ltac:(rewrite (s0_rp _ _ RP3); exact H8b)
             (TK.keepsR_trans _ _ _ _ (TK.keepsR_trans _ _ _ _ KO1a KO2) (ko1_rp _ _ RP3)) RO3).
    + apply (tail_cells_x _ M2 M3 V AG3); [lia | intros i Hi; apply KH; lia | intros i Hi; apply CDEF3; lia|].
      apply (tail_cells_x _ M1 M2 V AG2); [lia | intros i Hi; lia | intros i Hi; apply MG2 | exact TC1].
    + apply (ed_frame_x _ M2 M3 sp r R AG3); [lia | intros i Hi; apply KH; lia|]. apply (ed_frame_x _ M1 M2 sp r R AG2); [lia | intros i Hi; lia | exact FRM1].
    + exact FR3. + exact HH3. + exact BV3. + exact MOK3.
    + intros a Ha Hf Hd. unfold foot in Hf. apply CDEF3; [lia | lia | apply MG2, MG1; exact Hd].
    + apply (CK.samem_weaken2 _ _ _ M M2 M3 (CK.samem_weaken2 _ _ _ M M1 M2 AG1 AG2 (fun a Ha => Ha)) AG3).
      intros a [Ha|(b & Hb & Hr)]; [split; [lia | apply KH; lia]|].
      destruct (BOKf b Hb) as (B0 & B1 & B2 & B3 & B4). unfold hl_ceil in B4. split; [lia|]. split; [intros w [] | right; right; left; exists b; split; [exact Hb | exact Hr]].
Qed.
End H.
End EDX.
